-- Prove2me | Definitions.Def_OAIQ244Duke007
-- name    : OAIQ244Duke007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:11:17.106895+00:00
-- url     : https://prove2.me/theorems/f42546a3-3f03-414d-82d2-9bd3b0622839
-- title:
--   Definitions bundle OAIQ244Duke007 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 270 declarations of OpenAI's Lean: 90 definitions, 6 inductive types or structures, 13 instances and 161 theorems. The definitions and types are `GlobalClassFieldTheory.ClassFieldAxiom.quotientEquivOfSurjectiveWithKernel`, `GlobalClassFieldTheory.ClassFieldAxiom.realInfinitePlaceSignHom`, `KummerTheory.DiscreteNthRootsSubgroup`, `KummerTheory.FiniteSupportKummerQuotient`, `KummerTheory.KummerSubgroup`, `KummerTheory.NthRootsOfUnityInBase`, `KummerTheory.RadicalDatum`, `KummerTheory.RadicalDatum.RadicalQuotient`, `KummerTheory.RadicalDatum.ambientNthPowersSubgroup`, `KummerTheory.RadicalDatum.kummerCharacterWithoutSection`, `KummerTheory.RadicalDatum.quotientKummerCharacterWithoutSection`, `KummerTheory.RadicalDatum.radicalQuotientLift`, `KummerTheory.RadicalDatum.radicalQuotientMk`, `KummerTheory.RadicalDatum.radicalQuotientMulEquiv`, `KummerTheory.RadicalDatum.rootCharacter`, `KummerTheory.RadicalDatum.rootCharacterToMuWithoutSection`, `KummerTheory.RadicalDatum.rootCocycle`, `KummerTheory.RestrictedRadicalQuotient`, `KummerTheory.admissibleFiniteSupportSubgroup`, `KummerTheory.characterToNthRoots`, `KummerTheory.chosenFiniteKummerRadicalDatum`, `KummerTheory.chosenFiniteSupportCoefficient`, `KummerTheory.chosenFiniteSupportCoefficientSet`, `KummerTheory.chosenFiniteSupportCoefficientSubgroup`, `KummerTheory.chosenSimpleKummerExtension`, `KummerTheory.chosenSimpleKummerRoot`, `KummerTheory.finiteKummerRadicalSubgroup`, `KummerTheory.finiteSupportKummerQuotientLift`, `KummerTheory.finiteSupportKummerQuotientMk`, `KummerTheory.finiteSupportKummerQuotientMulEquiv`, `KummerTheory.finiteSupportNthPowersSubgroup`, `KummerTheory.kummerRootSet`, `KummerTheory.maximalKummerSubgroup`, `KummerTheory.nthRootsSubgroup`, `KummerTheory.restrictedKummerTranspose`, `KummerTheory.restrictedNthPowersSubgroup`, `KummerTheory.restrictedQuotientKummerCharacter`, `KummerTheory.restrictedRadicalInclusion`, `KummerTheory.restrictedRadicalQuotientLift`, `KummerTheory.restrictedRadicalQuotientMk` and 56 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Idele_ClassGroup_AlgEquiv`, `AlgebraicNumberTheory_Idele_Extension_EmbeddingNorm`, `AlgebraicNumberTheory_Idele_Extension_GaloisNorm`, `AlgebraicNumberTheory_Idele_SPlaces`, `AlgebraicNumberTheory_SUnit_GaloisAction`, `AlgebraicNumberTheory_SUnit_LogLattice`, `AlgebraicNumberTheory_SUnit_Rank`, `GlobalClassFieldTheory_ClassFieldAxiom_CyclicIdeleClassNormIndex`, `GlobalClassFieldTheory_ClassFieldAxiom_IdeleClassPowerLocalUnitQuotient_ArchimedeanPowerIndex`, `GlobalClassFieldTheory_ClassFieldAxiom_IdeleClassPowerLocalUnitQuotient_FinitePlaceCompletionInstances`, `GlobalClassFieldTheory_ClassFieldAxiom_IdeleClassPowerLocalUnitQuotient_SupportedIdeleIndex`, `GlobalClassFieldTheory_ClassFieldAxiom_SupportedIdelePowerLocalUnitQuotient`, `KummerTheory_Concrete_SUnitPreparation_FiniteRadicalSupport`, `KummerTheory_Concrete_SUnitPreparation_SUnitPowerQuotient`, `Kummer_Concrete_FiniteCharacterEquiv`, `Kummer_Concrete_FiniteDualSeparation`, `Kummer_Concrete_FiniteGeneration`, `Kummer_Concrete_FiniteSupport`, `Kummer_Concrete_InfiniteContinuity`, `Kummer_Concrete_MaximalKummerSubgroup`, `Kummer_Concrete_RadicalExtension`, `Kummer_Concrete_RadicalQuotient`, `Kummer_Concrete_RestrictedFinite`, `Kummer_Concrete_RootCharacters`, `Kummer_Concrete_SimpleExtension`, `LocalClassFieldTheory_ClassFormation_CohomologyBridge`, `LocalClassFieldTheory_Finite_LocalReciprocity_HenselianValuationBase`, `LocalField_Analytic_Arithmetic`, `LocalField_Analytic_LogExpAdditivity`, `LocalField_Analytic_LogExpComposition`, `LocalField_Analytic_LogExpSeries_FormalCore`, `LocalField_Analytic_LogExpSeries_FormalCoreBase_ChoicePositions`, `LocalField_Analytic_LogExpSeries_FormalCoreBase_PowerSeriesComposition`, `LocalField_Analytic_LogExpSeries_FormalCoreBase_ProductArgument`, `LocalField_Analytic_LogExpSeries_FormalProduct`, `LocalField_Analytic_LogExpSeries_SeriesTerms`, `LocalField_DiscreteValuationField_FieldUnitFactors`, `LocalField_DiscreteValuationField_MixedCharacteristicStructure_Core`, `LocalField_DiscreteValuationField_PadicLinearOfContinuous`, `LocalField_DiscreteValuationField_PadicModuleStructure`, `LocalField_DiscreteValuationField_PadicPowerIndex`, `LocalField_DiscreteValuationField_PrincipalUnitPadicAction_PadicReductionContinuous`, `LocalField_DiscreteValuationField_ValuationSubringUnits_CyclicValueGroup`, `LocalField_GroupTheory_PowerIndex`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke018`, `OAIQ244Duke019`, `OAIQ244Duke020`, `OAIQ244Duke021` and `OAIQ244Duke022`.
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
import Mathlib.Algebra.Group.Subgroup.Finite
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
import Mathlib.FieldTheory.LinearDisjoint
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
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
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

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Extension_GaloisNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- The linear polynomial whose value at the coordinates of `x` is the
`σ`-conjugate of `x`. -/
def conjugatePolynomial
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (σ : L ≃ₐ[K] L) :
    MvPolynomial ι L :=
  ∑ i, MvPolynomial.X i * MvPolynomial.C (σ (b i))

omit [FiniteDimensional K L] in
@[simp]
theorem eval_conjugatePolynomial
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (σ : L ≃ₐ[K] L) (x : L) :
    MvPolynomial.eval
        (fun i ↦ algebraMap K L (b.repr x i))
        (conjugatePolynomial b σ) =
      σ x := by
  rw [conjugatePolynomial, map_sum]
  simp only [map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C]
  calc
    ∑ i, algebraMap K L (b.repr x i) * σ (b i) =
        ∑ i, σ ((b.repr x i) • b i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [Algebra.smul_def]
    _ = σ (∑ i, (b.repr x i) • b i) := by
      rw [map_sum]
    _ = σ x := by rw [b.sum_repr]

/-- The product of the universal conjugates, written as a polynomial over
the splitting field. -/
def galoisProductPolynomial
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) :
    MvPolynomial ι L :=
  ∏ σ : L ≃ₐ[K] L, conjugatePolynomial b σ

@[simp]
theorem eval_galoisProductPolynomial
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (x : L) :
    MvPolynomial.eval
        (fun i ↦ algebraMap K L (b.repr x i))
        (galoisProductPolynomial b) =
      ∏ σ : L ≃ₐ[K] L, σ x := by
  simp [galoisProductPolynomial]

end RelativeIdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Extension_EmbeddingNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Norms through an ambient Galois extension

This file proves the embedded-subextension determinant-norm formula.
If `L/K` is embedded in a finite Galois extension `M/K`, extending the
determinant norm of an element of `A ⊗[K] L` to `A ⊗[K] M` gives the
product over all `K`-embeddings `L → M`.
-/

open scoped BigOperators TensorProduct
open NumberField

noncomputable section

namespace RelativeIdeleGroup

universe u v w z

section UniversalPolynomial

variable
    {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K M]

/-- Scalar extension of an embedding `L → M` on tensor algebras. -/
def scalarEmbedding
    (A : Type*) [CommRing A] [Algebra K A]
    (f : L →ₐ[K] M) :
    A ⊗[K] L →ₐ[A] A ⊗[K] M :=
  Algebra.TensorProduct.map
    (AlgHom.id A A) f

omit [Algebra L M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K M] in
@[simp]
theorem scalarEmbedding_tmul
    (A : Type*) [CommRing A] [Algebra K A]
    (f : L →ₐ[K] M) (a : A) (x : L) :
    scalarEmbedding A f (a ⊗ₜ[K] x) =
      a ⊗ₜ[K] f x :=
  rfl

end UniversalPolynomial

end RelativeIdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_SPlaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- The group of `S`-units of `K`, for a finite set of finite places.
All infinite places are understood to lie in `S`. -/
abbrev SUnitGroup
    (S : Finset (HeightOneSpectrum (𝓞 K))) :=
  (S : Set (HeightOneSpectrum (𝓞 K))).unit K

@[simp]
theorem mem_SUnitGroup_iff
    (S : Finset (HeightOneSpectrum (𝓞 K))) (x : Kˣ) :
    x ∈ SUnitGroup (K := K) S ↔
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        v.valuation K x = 1 :=
  Iff.rfl
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_CohomologyBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace LocalClassFieldTheory

/-!
# The actual low-degree Tate quotients as Herbrand quotients

This file compares the concrete multiplicative Herbrand quotients from
low-degree cyclic cohomology with the Tate objects built from mathlib's actual
Galois representation on `Lˣ`.  The comparison uses the standard Galois action
on units; it does not introduce a replacement coefficient object.
-/

noncomputable section

open scoped BigOperators

open CategoryTheory

variable (K L : Type) [Field K] [Field L] [Algebra K L]

/-- Compose an additive equivalence with a submodule quotient map.

Keeping this construction polymorphic prevents typeclass search from unfolding
the concrete Galois representation while it looks for the quotient's additive
structure. -/
def additiveEquivToQuotientHom
    {A M : Type} [AddCommGroup A] [AddCommGroup M]
    (e : A ≃+ M) (N : Submodule ℤ M) : A →+ M ⧸ N :=
  N.mkQ.toAddMonoidHom.comp e.toAddMonoidHom

/-- Multiplicative form of an additive homomorphism, kept polymorphic for the
same elaboration reason as `additiveEquivToQuotientHom`. -/
def additiveHomToMultiplicativeHom
    {G B : Type} [Group G] [AddCommGroup B]
    (f : Additive G →+ B) : G →* Multiplicative B :=
  AddMonoidHom.toMultiplicativeRight f

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_HenselianValuationBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace LocalClassFieldTheory

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

abbrev G_p2 := Gal(SeparableClosure K / K)

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_SUnit_Rank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- The group of ordinary units, expressed as `S`-units for the empty set. -/
noncomputable def emptyEquivNumberFieldUnits :
    ((∅ : Set (HeightOneSpectrum (𝓞 K))).unit K) ≃* (𝓞 K)ˣ :=
  let eInteger :
      ((∅ : Set (HeightOneSpectrum (𝓞 K))).integer K)ˣ ≃*
        (⊥ : Subalgebra (𝓞 K) K)ˣ :=
    Units.mapEquiv
      ((Subalgebra.equivOfEq
        ((∅ : Set (HeightOneSpectrum (𝓞 K))).integer K)
        (⊥ : Subalgebra (𝓞 K) K)
        (IsDedekindDomain.integer_empty (𝓞 K) K) : _ ≃ₐ[𝓞 K] _) : _ ≃* _)
  let eBot :
      (⊥ : Subalgebra (𝓞 K) K)ˣ ≃* (𝓞 K)ˣ :=
    Units.mapEquiv
      ((Algebra.botEquivOfInjective
        (IsFractionRing.injective (𝓞 K) K) : _ ≃ₐ[𝓞 K] _) : _ ≃* _)
  (Set.unitEquivUnitsInteger
    (∅ : Set (HeightOneSpectrum (𝓞 K))) K).trans
      (eInteger.trans eBot)

/-- The canonical embedding of ordinary units into the `S`-unit group. -/
noncomputable def fromNumberFieldUnits
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (𝓞 K)ˣ →* SUnitGroup (K := K) S where
  toFun u :=
    ⟨((emptyEquivNumberFieldUnits (K := K)).symm u : Kˣ),
      fun v _ =>
        Set.unit_valuation_eq_one
          (∅ : Set (HeightOneSpectrum (𝓞 K))) K
          ((emptyEquivNumberFieldUnits (K := K)).symm u) (by simp)⟩
  map_one' := by
    ext
    simp
  map_mul' u v := by
    ext
    simp

section DivisorMap

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- The exponent of the principal fractional ideal of an `S`-unit at a
finite place in `S`. -/
noncomputable def divisorCoordinate
    (x : SUnitGroup (K := K) S) (v : S) : ℤ :=
  FractionalIdeal.count K (v : HeightOneSpectrum (𝓞 K))
    (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((x : Kˣ) : K))

/-- The valuation of a localization fraction is the exponential of the
negative exponent of its principal fractional ideal. -/
theorem valuation_mk'_eq_exp_neg_count
    (v : HeightOneSpectrum (𝓞 K)) {n : 𝓞 K} (hn : n ≠ 0)
    (d : (𝓞 K)⁰) :
    v.valuation K (IsLocalization.mk' K n d) =
      WithZero.exp
        (-FractionalIdeal.count K v
          (FractionalIdeal.spanSingleton (𝓞 K)⁰
            (IsLocalization.mk' K n d))) := by
  classical
  have hI :
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (IsLocalization.mk' K n d) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰
            ((algebraMap (𝓞 K) K) (d : 𝓞 K))⁻¹ *
          ↑(Ideal.span {n} : Ideal (𝓞 K)) := by
    rw [FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
    apply congr_arg
    rw [IsFractionRing.mk'_eq_div, div_eq_mul_inv, mul_comm]
  have hx :
      FractionalIdeal.spanSingleton (𝓞 K)⁰
          (IsLocalization.mk' K n d) ≠ 0 := by
    rw [FractionalIdeal.spanSingleton_ne_zero_iff,
      IsFractionRing.mk'_eq_div, ne_eq, div_eq_zero_iff, not_or]
    exact
      ⟨(map_ne_zero_iff (algebraMap (𝓞 K) K)
          (IsFractionRing.injective (𝓞 K) K)).mpr hn,
        map_ne_zero_of_mem_nonZeroDivisors _
          (IsFractionRing.injective (𝓞 K) K) d.property⟩
  have hcount :
      FractionalIdeal.count K v
          (FractionalIdeal.spanSingleton (𝓞 K)⁰
            (IsLocalization.mk' K n d)) =
        ((Associates.mk v.asIdeal).count
            (Associates.mk (Ideal.span {n} : Ideal (𝓞 K))).factors -
          (Associates.mk v.asIdeal).count
            (Associates.mk
              (Ideal.span {(d : 𝓞 K)} : Ideal (𝓞 K))).factors : ℤ) := by
    exact FractionalIdeal.count_well_defined (K := K) v hx hI
  rw [v.valuation_of_mk', v.intValuation_if_neg hn,
    v.intValuation_if_neg (nonZeroDivisors.coe_ne_zero d), hcount]
  rw [div_eq_mul_inv, ← WithZero.exp_neg, ← WithZero.exp_add]
  congr
  simp [sub_eq_add_neg, add_comm]

/-- The adic valuation of a field unit is the exponential of the
negative exponent of its principal fractional ideal. -/
theorem valuation_eq_exp_neg_count
    (x : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    v.valuation K (x : K) =
      WithZero.exp
        (-FractionalIdeal.count K v
          (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K))) := by
  obtain ⟨n, d, hnd⟩ :=
    IsLocalization.exists_mk'_eq (𝓞 K)⁰ (x : K)
  have hn : n ≠ 0 := by
    intro hn0
    apply Units.ne_zero x
    rw [← hnd, hn0, IsFractionRing.mk'_eq_div, map_zero, zero_div]
  rw [← hnd]
  exact valuation_mk'_eq_exp_neg_count (K := K) v hn d

/-- A field unit has valuation one exactly when its principal fractional
ideal has exponent zero at the place. -/
theorem valuation_eq_one_iff_count_eq_zero
    (x : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    v.valuation K (x : K) = 1 ↔
      FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)) = 0 := by
  rw [valuation_eq_exp_neg_count (K := K) x v]
  constructor
  · intro h
    exact neg_eq_zero.mp (WithZero.exp_eq_one.mp h)
  · intro h
    simp [h]

theorem divisorCoordinate_eq_zero_iff
    (x : SUnitGroup (K := K) S) (v : S) :
    divisorCoordinate (K := K) S x v = 0 ↔
      (v : HeightOneSpectrum (𝓞 K)).valuation K ((x : Kˣ) : K) = 1 := by
  exact (valuation_eq_one_iff_count_eq_zero
    (K := K) (x : Kˣ) (v : HeightOneSpectrum (𝓞 K))).symm

theorem divisorCoordinate_mul
    (x y : SUnitGroup (K := K) S) (v : S) :
    divisorCoordinate (K := K) S (x * y) v =
      divisorCoordinate (K := K) S x v +
        divisorCoordinate (K := K) S y v := by
  change
    FractionalIdeal.count K (v : HeightOneSpectrum (𝓞 K))
        (FractionalIdeal.spanSingleton (𝓞 K)⁰
          ((((x : Kˣ) : K) * ((y : Kˣ) : K)))) =
      FractionalIdeal.count K (v : HeightOneSpectrum (𝓞 K))
          (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((x : Kˣ) : K)) +
        FractionalIdeal.count K (v : HeightOneSpectrum (𝓞 K))
          (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((y : Kˣ) : K))
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul]
  · exact FractionalIdeal.spanSingleton_ne_zero_iff.mpr
      (Units.ne_zero (x : Kˣ))
  · exact FractionalIdeal.spanSingleton_ne_zero_iff.mpr
      (Units.ne_zero (y : Kˣ))

theorem divisorCoordinate_one (v : S) :
    divisorCoordinate (K := K) S 1 v = 0 := by
  simp [divisorCoordinate, FractionalIdeal.count_one]

/-- The additive principal-divisor map on `S`-units. -/
noncomputable def divisor :
    Additive (SUnitGroup (K := K) S) →+
      (S → ℤ) where
  toFun x v := divisorCoordinate (K := K) S (Additive.toMul x) v
  map_zero' := by
    ext v
    exact divisorCoordinate_one (K := K) S v
  map_add' x y := by
    ext v
    exact divisorCoordinate_mul (K := K) S
      (Additive.toMul x) (Additive.toMul y) v

/-- The `ℤ`-linear principal-divisor map on `S`-units. -/
noncomputable def divisorLinearMap :
    Additive (SUnitGroup (K := K) S) →ₗ[ℤ] (S → ℤ) :=
  (divisor (K := K) S).toIntLinearMap

/-- The additive linearization of the ordinary-unit embedding. -/
noncomputable def fromNumberFieldUnitsLinearMap :
    Additive (𝓞 K)ˣ →ₗ[ℤ]
      Additive (SUnitGroup (K := K) S) :=
  (MonoidHom.toAdditive
    (fromNumberFieldUnits (K := K) S)).toIntLinearMap

/-- An `S`-unit in the kernel of the divisor map has valuation one at every
finite place. -/
theorem valuation_eq_one_of_mem_ker_divisorLinearMap
    {x : Additive (SUnitGroup (K := K) S)}
    (hx : x ∈ LinearMap.ker (divisorLinearMap (K := K) S))
    (v : HeightOneSpectrum (𝓞 K)) :
    v.valuation K
      ((((Additive.toMul x :
        SUnitGroup (K := K) S) : Kˣ) : K)) = 1 := by
  by_cases hv : v ∈ S
  · let vv : S := ⟨v, hv⟩
    apply (divisorCoordinate_eq_zero_iff (K := K) S
      (Additive.toMul x) vv).1
    have hxzero :
        divisorLinearMap (K := K) S x = 0 :=
      LinearMap.mem_ker.mp hx
    simpa [divisorLinearMap, divisor] using congrFun hxzero vv
  · exact (Additive.toMul x :
      SUnitGroup (K := K) S).property v hv

/-- An `S`-unit in the divisor kernel, regarded as an `S`-unit for the
empty set. -/
noncomputable def kerDivisorToEmptySUnits
    (x : LinearMap.ker (divisorLinearMap (K := K) S)) :
    ((∅ : Set (HeightOneSpectrum (𝓞 K))).unit K) :=
  ⟨((Additive.toMul (x : Additive (SUnitGroup (K := K) S)) :
      SUnitGroup (K := K) S) : Kˣ),
    fun v _ =>
      valuation_eq_one_of_mem_ker_divisorLinearMap
        (K := K) S x.property v⟩

/-- Ordinary units are exactly the kernel of the `S`-unit divisor map. -/
theorem range_fromNumberFieldUnitsLinearMap_eq_ker_divisorLinearMap :
    LinearMap.range (fromNumberFieldUnitsLinearMap (K := K) S) =
      LinearMap.ker (divisorLinearMap (K := K) S) := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    apply LinearMap.mem_ker.mpr
    ext v
    apply (divisorCoordinate_eq_zero_iff (K := K) S
      (fromNumberFieldUnits (K := K) S (Additive.toMul u)) v).2
    exact Set.unit_valuation_eq_one
      (∅ : Set (HeightOneSpectrum (𝓞 K))) K
      ((emptyEquivNumberFieldUnits (K := K)).symm (Additive.toMul u))
      (by simp)
  · intro hx
    let y := kerDivisorToEmptySUnits (K := K) S ⟨x, hx⟩
    let u : (𝓞 K)ˣ := emptyEquivNumberFieldUnits y
    refine ⟨Additive.ofMul u, ?_⟩
    apply Additive.toMul.injective
    change
      fromNumberFieldUnits (K := K) S u = Additive.toMul x
    apply Subtype.ext
    change
      ((emptyEquivNumberFieldUnits (K := K)).symm u : Kˣ) =
        ((Additive.toMul x : SUnitGroup (K := K) S) : Kˣ)
    dsimp [u]
    rw [MulEquiv.symm_apply_apply]
    rfl

end DivisorMap

end SUnitGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_SUnit_LogLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- The reduced logarithmic space for `S`-units.  It consists of the
Dirichlet logarithmic space and one real divisor coordinate for every
finite place in `S`. -/
abbrev ReducedLogSpace :=
  NumberField.Units.dirichletUnitTheorem.logSpace K × (S → ℝ)

/-- The reduced logarithmic embedding.  At an infinite place it is the
usual multiplicity-weighted logarithm.  At a finite place it is the
integer exponent of the principal fractional ideal, regarded as a real
number. -/
noncomputable def reducedLog :
    Additive (SUnitGroup (K := K) S) →+
      ReducedLogSpace (K := K) S where
  toFun x :=
    (fun w =>
      w.1.mult *
        Real.log
          (w.1
            (((Additive.toMul x :
              SUnitGroup (K := K) S) : Kˣ) : K)),
      fun v =>
        (divisorCoordinate (K := K) S
          (Additive.toMul x) v : ℝ))
  map_zero' := by
    apply Prod.ext
    · ext w
      simp
    · ext v
      change
        (divisorCoordinate (K := K) S 1 v : ℝ) = 0
      exact_mod_cast divisorCoordinate_one (K := K) S v
  map_add' x y := by
    apply Prod.ext
    · ext w
      simp [Real.log_mul, mul_add]
    · ext v
      change
        (divisorCoordinate (K := K) S
          (Additive.toMul x * Additive.toMul y) v : ℝ) =
          (divisorCoordinate (K := K) S
            (Additive.toMul x) v : ℝ) +
          (divisorCoordinate (K := K) S
            (Additive.toMul y) v : ℝ)
      exact_mod_cast
        divisorCoordinate_mul (K := K) S
          (Additive.toMul x) (Additive.toMul y) v

@[simp]
theorem reducedLog_fst_fromNumberFieldUnits
    (u : (𝓞 K)ˣ) :
    (reducedLog (K := K) S
      (Additive.ofMul
        (fromNumberFieldUnits (K := K) S u))).1 =
      NumberField.Units.logEmbedding K (Additive.ofMul u) := by
  ext w
  rfl

@[simp]
theorem reducedLog_snd_fromNumberFieldUnits
    (u : (𝓞 K)ˣ) :
    (reducedLog (K := K) S
      (Additive.ofMul
        (fromNumberFieldUnits (K := K) S u))).2 = 0 := by
  ext v
  change
    (divisorCoordinate (K := K) S
      (fromNumberFieldUnits (K := K) S u) v : ℝ) = 0
  norm_cast
  have hrange :
      fromNumberFieldUnitsLinearMap (K := K) S
          (Additive.ofMul u) ∈
        LinearMap.range
          (fromNumberFieldUnitsLinearMap (K := K) S) :=
    LinearMap.mem_range_self _ _
  rw [range_fromNumberFieldUnitsLinearMap_eq_ker_divisorLinearMap
    (K := K) S] at hrange
  have hzero :=
    congrFun
      (LinearMap.mem_ker.mp hrange) v
  simpa [divisorLinearMap, divisor,
    fromNumberFieldUnitsLinearMap] using hzero

section FullLogarithmicSpace

/-- The places occurring in the `S`-unit theorem: every infinite place
and the finite places belonging to `S`. -/
abbrev LogPlace :=
  NumberField.InfinitePlace K ⊕ S

/-- The ambient real coordinate space indexed by all places occurring
in the `S`-unit theorem. -/
abbrev FullLogSpace :=
  LogPlace (K := K) S → ℝ

/-- The normalized logarithmic absolute-value map at all places in the
`S`-unit theorem. -/
noncomputable def fullLogAmbient :
    Additive (SUnitGroup (K := K) S) →+
      FullLogSpace (K := K) S where
  toFun x p :=
    match p with
    | Sum.inl w =>
        w.mult *
          Real.log
            (w
              (((Additive.toMul x :
                SUnitGroup (K := K) S) : Kˣ) : K))
    | Sum.inr v =>
        Real.log
          (NumberField.HeightOneSpectrum.adicAbv K
            (v : HeightOneSpectrum (𝓞 K))
            (((Additive.toMul x :
              SUnitGroup (K := K) S) : Kˣ) : K))
  map_zero' := by
    ext p
    cases p <;> simp
  map_add' x y := by
    ext p
    cases p <;> simp [Real.log_mul, mul_add]

@[simp]
theorem fullLogAmbient_infinite
    (x : Additive (SUnitGroup (K := K) S))
    (w : NumberField.InfinitePlace K) :
    fullLogAmbient (K := K) S x (Sum.inl w) =
      w.mult *
        Real.log
          (w
            (((Additive.toMul x :
              SUnitGroup (K := K) S) : Kˣ) : K)) :=
  rfl

@[simp]
theorem fullLogAmbient_finite
    (x : Additive (SUnitGroup (K := K) S)) (v : S) :
    fullLogAmbient (K := K) S x (Sum.inr v) =
      Real.log
        (NumberField.HeightOneSpectrum.adicAbv K
          (v : HeightOneSpectrum (𝓞 K))
          (((Additive.toMul x :
            SUnitGroup (K := K) S) : Kˣ) : K)) :=
  rfl

end FullLogarithmicSpace

end SUnitGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_SUnit_GaloisAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

noncomputable section

variable
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

/-- The usual action of the relative Galois group on field units. -/
@[reducible]
noncomputable def fieldUnitsMulDistribMulAction :
    MulDistribMulAction (L ≃ₐ[K] L) Lˣ where
  smul σ x := Units.mapEquiv σ.toMulEquiv x
  one_smul x := by
    ext
    rfl
  mul_smul σ τ x := by
    ext
    rfl
  smul_one σ := map_one (Units.mapEquiv σ.toMulEquiv)
  smul_mul σ x y := map_mul (Units.mapEquiv σ.toMulEquiv) x y

section FinitePlaceAction

local instance instMulDistribMulActionAlgEquivUnits_solutions :
    MulDistribMulAction (L ≃ₐ[K] L) Lˣ :=
  fieldUnitsMulDistribMulAction K L

end FinitePlaceAction
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_ClassGroup_AlgEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Relative idele classes under an isomorphic realization

If two finite extensions of a number field are isomorphic over the base,
their tensor-product presentations of the relative adeles are canonically
isomorphic.  This file descends that canonical isomorphism to relative
ideles and idele classes and records compatibility with the determinant
norm.

The construction is the direct tensor-product congruence

`𝔸_K ⊗[K] L ≃ 𝔸_K ⊗[K] M`

induced by an algebra equivalence `L ≃ₐ[K] M`.  In particular, no second
model of relative adeles or of the idele-class norm is introduced.
-/

open scoped NumberField TensorProduct
open NumberField
open IsDedekindDomain

noncomputable section


universe u v w

variable
    {K : Type u} {L : Type v} {M : Type w}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [Field M] [Algebra K M]

section Absolute

variable
    {K : Type u} {M : Type w}
    [Field K] [NumberField K] [Algebra ℚ K]
    [Field M] [NumberField M] [Algebra ℚ M]

/-- The permutation of finite places induced by an equivalence of number
fields. -/
noncomputable def finitePlaceCongr
    (e : K ≃ₐ[ℚ] M) :
    HeightOneSpectrum (𝓞 K) ≃
      HeightOneSpectrum (𝓞 M) :=
  HeightOneSpectrum.equivOfRingEquiv
    (NumberField.RingOfIntegers.mapRingEquiv
      e.toRingEquiv)
end Absolute
end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_RootCharacters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Root characters for Kummer theory

Support API for root-quotient constructions in concrete Kummer extensions.
-/

namespace KummerTheory

open groupCohomology

section RootQuotientPrelim

variable {L : Type*} [Field L]

/-- Two unit roots with the same `n`-th power differ by an `n`-th root of unity. -/
theorem div_pow_eq_one_of_pow_eq_pow
    {n : ℕ} {u v : Lˣ} (h : u ^ n = v ^ n) :
    (u / v) ^ n = 1 := by
  rw [div_pow, h]
  exact div_self' (v ^ n)

end RootQuotientPrelim

section TorsionSubgroups

variable (L : Type*) [Field L]

/-- The subgroup of units whose `n`-th power is `1`. -/
def nthRootsSubgroup (n : ℕ) : Subgroup Lˣ where
  carrier := {u | u ^ n = 1}
  one_mem' := by
    simp
  mul_mem' := by
    intro u v hu hv
    change (u * v) ^ n = 1
    rw [mul_pow, hu, hv, one_mul]
  inv_mem' := by
    intro u hu
    change u⁻¹ ^ n = 1
    rw [inv_pow, hu, inv_one]

/-- Membership in the roots subgroup is equivalent to satisfying the `n`th-root equation. -/
@[simp] theorem mem_nthRootsSubgroup_iff {n : ℕ} {u : Lˣ} :
    u ∈ nthRootsSubgroup L n ↔ u ^ n = 1 :=
  Iff.rfl

end TorsionSubgroups

section RootQuotients

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The basic root-quotient attached to a unit `β` and a Galois automorphism `σ`. -/
def rootQuotient (β : Lˣ) (σ : Gal(L/K)) : Lˣ :=
  σ • β / β

/-- The root-quotient attached to the identity automorphism is trivial. -/
@[simp] theorem rootQuotient_one (β : Lˣ) :
    rootQuotient (K := K) (L := L) β 1 = 1 := by
  simp [rootQuotient]

/-- Multiplying the root-quotient by the chosen root recovers its Galois transform. -/
@[simp] theorem rootQuotient_mul_right (β : Lˣ) (σ : Gal(L/K)) :
    rootQuotient (K := K) (L := L) β σ * β = σ • β := by
  simp [rootQuotient]

/-- Base-field units have trivial root-quotient. -/
@[simp] theorem rootQuotient_algebraMap_unit (u : Kˣ) (σ : Gal(L/K)) :
    rootQuotient (K := K) (L := L) (Units.map (algebraMap K L).toMonoidHom u) σ = 1 := by
  unfold rootQuotient
  ext
  simp

/-- The root-quotient attached to a product is the product of the root-quotients. -/
theorem rootQuotient_mul_root (u v : Lˣ) (σ : Gal(L/K)) :
    rootQuotient (K := K) (L := L) (u * v) σ =
      rootQuotient (K := K) (L := L) u σ *
        rootQuotient (K := K) (L := L) v σ := by
  simp [rootQuotient, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- The root-quotient is trivial exactly when the chosen root is fixed by `σ`. -/
theorem rootQuotient_eq_one_iff (β : Lˣ) (σ : Gal(L/K)) :
    rootQuotient (K := K) (L := L) β σ = 1 ↔ σ • β = β := by
  unfold rootQuotient
  exact div_eq_one

/-- The root-quotient construction satisfies the multiplicative cocycle identity. -/
theorem rootQuotient_mul (β : Lˣ) (σ τ : Gal(L/K)) :
    rootQuotient (K := K) (L := L) β (σ * τ) =
      σ • rootQuotient (K := K) (L := L) β τ *
        rootQuotient (K := K) (L := L) β σ := by
  rw [rootQuotient]
  rw [mul_smul]
  simp [rootQuotient, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- The root-quotient of a quotient is the quotient of the root-quotients. -/
theorem rootQuotient_div (u v : Lˣ) (σ : Gal(L/K)) :
    rootQuotient (K := K) (L := L) (u / v) σ =
      rootQuotient (K := K) (L := L) u σ /
        rootQuotient (K := K) (L := L) v σ := by
  simp [rootQuotient, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- Changing the chosen root changes the corresponding quotient cocycle by a coboundary. -/
theorem rootQuotient_changeRoot (u v : Lˣ) (σ : Gal(L/K)) :
    rootQuotient (K := K) (L := L) u σ /
        rootQuotient (K := K) (L := L) v σ =
      rootQuotient (K := K) (L := L) (u / v) σ := by
  exact (rootQuotient_div (K := K) (L := L) u v σ).symm

/-- If `β ^ n` is fixed by Galois, then `σ(β) / β` is `n`-torsion. -/
theorem rootQuotient_pow_eq_one_of_pow_fixed
    {n : ℕ} {β : Lˣ} (hβ : ∀ σ : Gal(L/K), σ • (β ^ n) = β ^ n)
    (σ : Gal(L/K)) :
    rootQuotient (K := K) (L := L) β σ ^ n = 1 := by
  unfold rootQuotient
  apply div_pow_eq_one_of_pow_eq_pow
  exact (map_pow (MulDistribMulAction.toMonoidHom Lˣ σ) β n).symm.trans (hβ σ)

end RootQuotients

section RadicalData

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/--
A radical datum of exponent `n` consists of a subgroup of `Kˣ` together with a chosen
`n`-th root in `Lˣ` for each of its elements.
-/
structure RadicalDatum (n : ℕ+) where
  /-- The subgroup of base-field units for which roots are chosen. -/
  carrier : Subgroup Kˣ
  /-- A chosen `n`-th root in `Lˣ` for each unit in `carrier`. -/
  root : carrier → Lˣ
  /-- Each chosen root has `n`-th power equal to the image of its base-field unit in `Lˣ`. -/
  root_pow_eq : ∀ a : carrier,
    root a ^ (n : ℕ) = Units.map (algebraMap K L).toMonoidHom a.1

namespace RadicalDatum

variable {n : ℕ+} (D : RadicalDatum (K := K) (L := L) n)

/-- The chosen root witness has the prescribed `n`-th power. -/
@[simp] theorem root_pow_eq_map (a : D.carrier) :
    D.root a ^ (n : ℕ) = Units.map (algebraMap K L).toMonoidHom a.1 :=
  D.root_pow_eq a

/-- Two `n`-th roots of the same radical element differ by an `n`-th root of unity. -/
theorem div_pow_eq_one_of_same_image
    {u v : Lˣ} (a : D.carrier)
    (hu : u ^ (n : ℕ) = Units.map (algebraMap K L).toMonoidHom a.1)
    (hv : v ^ (n : ℕ) = Units.map (algebraMap K L).toMonoidHom a.1) :
    (u / v) ^ (n : ℕ) = 1 := by
  exact div_pow_eq_one_of_pow_eq_pow (n := (n : ℕ)) (hu.trans hv.symm)

/-- The root-quotient map `σ ↦ σ(β) / β` attached to the chosen root witness of `a`. -/
def rootCocycle (a : D.carrier) (σ : Gal(L/K)) : Lˣ :=
  rootQuotient (K := K) (L := L) (D.root a) σ

/-- The chosen root-quotient is trivial at the identity automorphism. -/
@[simp] theorem rootCocycle_one (a : D.carrier) :
    D.rootCocycle a 1 = 1 := by
  simp [rootCocycle]

/-- The chosen root-quotient satisfies the multiplicative cocycle identity. -/
theorem rootCocycle_mul (a : D.carrier) (σ τ : Gal(L/K)) :
    D.rootCocycle a (σ * τ) =
      σ • D.rootCocycle a τ * D.rootCocycle a σ := by
  exact rootQuotient_mul (K := K) (L := L) (D.root a) σ τ

/-- Galois automorphisms fix units coming from the base field. -/
@[simp] theorem smul_algebraMap_unit (σ : Gal(L/K)) (u : Kˣ) :
    σ • Units.map (algebraMap K L).toMonoidHom u =
      Units.map (algebraMap K L).toMonoidHom u := by
  ext
  simp

/-- The chosen root-quotient of `a` lands in the `n`-torsion subgroup of `Lˣ`. -/
theorem rootCocycle_pow_eq_one (a : D.carrier) (σ : Gal(L/K)) :
    D.rootCocycle a σ ^ (n : ℕ) = 1 := by
  refine rootQuotient_pow_eq_one_of_pow_fixed (K := K) (L := L)
      (β := D.root a) ?_ σ
  intro τ
  rw [D.root_pow_eq_map]
  exact smul_algebraMap_unit (K := K) (L := L) τ a.1

/-- If `μₙ(L)` is fixed by Galois, root-quotients for the same radical element agree. -/
theorem rootQuotient_eq_rootCocycle_of_same_pow
    (hfixed : ∀ σ : Gal(L/K), ∀ u : Lˣ, u ^ (n : ℕ) = 1 → σ • u = u)
    {u : Lˣ} (a : D.carrier)
    (hu : u ^ (n : ℕ) = Units.map (algebraMap K L).toMonoidHom a.1)
    (σ : Gal(L/K)) :
    rootQuotient (K := K) (L := L) u σ = D.rootCocycle a σ := by
  have hpow : (u / D.root a) ^ (n : ℕ) = 1 := by
    exact D.div_pow_eq_one_of_same_image a hu (D.root_pow_eq_map a)
  have hfixed_delta : σ • (u / D.root a) = u / D.root a :=
    hfixed σ (u / D.root a) hpow
  have hquot_one : rootQuotient (K := K) (L := L) (u / D.root a) σ = 1 :=
    (rootQuotient_eq_one_iff (K := K) (L := L) (u / D.root a) σ).2 hfixed_delta
  have hdiv_one : rootQuotient (K := K) (L := L) u σ / D.rootCocycle a σ = 1 := by
    rw [rootCocycle, rootQuotient_changeRoot]
    exact hquot_one
  exact div_eq_one.mp hdiv_one

/-- If `μₙ(L)` is fixed by Galois, the chosen root-quotient is a character. -/
def rootCharacter (a : D.carrier)
    (hfixed : ∀ σ : Gal(L/K), ∀ u : Lˣ, u ^ (n : ℕ) = 1 → σ • u = u) :
    Gal(L/K) →* Lˣ where
  toFun := D.rootCocycle a
  map_one' := by
    exact D.rootCocycle_one a
  map_mul' := by
    intro σ τ
    rw [D.rootCocycle_mul]
    rw [hfixed σ (D.rootCocycle a τ) (D.rootCocycle_pow_eq_one a τ)]
    exact mul_comm _ _

/-- The Kummer root character evaluates as the Galois translate divided by the chosen root. -/
@[simp] theorem rootCharacter_apply (a : D.carrier)
    (hfixed : ∀ σ : Gal(L/K), ∀ u : Lˣ, u ^ (n : ℕ) = 1 → σ • u = u)
    (σ : Gal(L/K)) :
    D.rootCharacter a hfixed σ = D.rootCocycle a σ :=
  rfl

/-- The character obtained from a chosen root still takes values in `μₙ(L)`. -/
theorem rootCharacter_pow_eq_one (a : D.carrier)
    (hfixed : ∀ σ : Gal(L/K), ∀ u : Lˣ, u ^ (n : ℕ) = 1 → σ • u = u)
    (σ : Gal(L/K)) :
    D.rootCharacter a hfixed σ ^ (n : ℕ) = 1 := by
  rw [D.rootCharacter_apply]
  exact D.rootCocycle_pow_eq_one a σ

/-- The character obtained from a chosen root lands in `μₙ(L)`. -/
theorem rootCharacter_mem_nthRootsSubgroup (a : D.carrier)
    (hfixed : ∀ σ : Gal(L/K), ∀ u : Lˣ, u ^ (n : ℕ) = 1 → σ • u = u)
    (σ : Gal(L/K)) :
    D.rootCharacter a hfixed σ ∈ nthRootsSubgroup L (n : ℕ) := by
  rw [mem_nthRootsSubgroup_iff]
  exact D.rootCharacter_pow_eq_one a hfixed σ

end RadicalDatum
end RadicalData

end KummerTheory
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_RadicalQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- Multiplicativity of root characters does not require a multiplicative choice of roots. -/
theorem rootCharacter_mul_withoutSection
    (hfixed : ∀ σ : Gal(L/K), ∀ u : Lˣ, u ^ (n : ℕ) = 1 → σ • u = u)
    (a b : D.carrier) :
    D.rootCharacter (a * b) hfixed =
      D.rootCharacter a hfixed * D.rootCharacter b hfixed := by
  apply MonoidHom.ext
  intro σ
  change D.rootCocycle (a * b) σ = D.rootCocycle a σ * D.rootCocycle b σ
  rw [← D.rootQuotient_eq_rootCocycle_of_same_pow hfixed (a * b) (u := D.root a * D.root b)]
  · exact rootQuotient_mul_root (K := K) (L := L) (D.root a) (D.root b) σ
  · rw [mul_pow, D.root_pow_eq_map, D.root_pow_eq_map]
    exact (map_mul (Units.map (algebraMap K L).toMonoidHom) a.1 b.1).symm

/-- The root character of `1` is trivial, without choosing roots multiplicatively. -/
theorem rootCharacter_one_withoutSection
    (hfixed : ∀ σ : Gal(L/K), ∀ u : Lˣ, u ^ (n : ℕ) = 1 → σ • u = u) :
    D.rootCharacter 1 hfixed = 1 := by
  apply MonoidHom.ext
  intro σ
  rw [D.rootCharacter_apply]
  rw [← D.rootQuotient_eq_rootCocycle_of_same_pow hfixed (1 : D.carrier)
    (u := Units.map (algebraMap K L).toMonoidHom (1 : Kˣ))]
  · exact rootQuotient_algebraMap_unit (K := K) (L := L) 1 σ
  · simp

/-- The root character, bundled with its codomain restricted to `μₙ(L)`. -/
def rootCharacterToMuWithoutSection (a : D.carrier)
    (hfixed : ∀ σ : Gal(L/K), ∀ u : Lˣ, u ^ (n : ℕ) = 1 → σ • u = u) :
    Gal(L/K) →* nthRootsSubgroup L (n : ℕ) where
  toFun := fun σ =>
    ⟨D.rootCharacter a hfixed σ, D.rootCharacter_mem_nthRootsSubgroup a hfixed σ⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (D.rootCharacter a hfixed)
  map_mul' := by
    intro σ τ
    apply Subtype.ext
    exact map_mul (D.rootCharacter a hfixed) σ τ

/-- The section-free root character evaluates as the quotient of the transported
root by the root itself. -/
@[simp] theorem rootCharacterToMuWithoutSection_apply (a : D.carrier)
    (hfixed : ∀ σ : Gal(L/K), ∀ u : Lˣ, u ^ (n : ℕ) = 1 → σ • u = u)
    (σ : Gal(L/K)) :
    D.rootCharacterToMuWithoutSection a hfixed σ =
      ⟨D.rootCharacter a hfixed σ, D.rootCharacter_mem_nthRootsSubgroup a hfixed σ⟩ :=
  rfl

/-- The root-character construction is a homomorphism on the radical subgroup. -/
def kummerCharacterWithoutSection
    (hfixed : ∀ σ : Gal(L/K), ∀ u : Lˣ, u ^ (n : ℕ) = 1 → σ • u = u) :
    D.carrier →* (Gal(L/K) →* nthRootsSubgroup L (n : ℕ)) where
  toFun := fun a => D.rootCharacterToMuWithoutSection a hfixed
  map_one' := by
    apply MonoidHom.ext
    intro σ
    apply Subtype.ext
    exact congrArg (fun χ : Gal(L/K) →* Lˣ => χ σ)
      (D.rootCharacter_one_withoutSection hfixed)
  map_mul' := by
    intro a b
    apply MonoidHom.ext
    intro σ
    apply Subtype.ext
    exact congrArg (fun χ : Gal(L/K) →* Lˣ => χ σ)
      (D.rootCharacter_mul_withoutSection hfixed a b)

/-- Elements of the radical subgroup which are `n`-th powers in the ambient `Kˣ`. -/
def ambientNthPowersSubgroup : Subgroup D.carrier :=
  (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range.comap D.carrier.subtype

/-- An element belongs to the ambient power subgroup exactly when it is an `n`th power. -/
theorem mem_ambientNthPowersSubgroup_iff {a : D.carrier} :
    a ∈ D.ambientNthPowersSubgroup ↔ ∃ b : Kˣ, b ^ (n : ℕ) = a.1 :=
  Iff.rfl

/-- A root character is trivial on an ambient `n`-th power. -/
theorem rootCharacter_eq_one_of_mem_ambientNthPowers
    (hfixed : ∀ σ : Gal(L/K), ∀ u : Lˣ, u ^ (n : ℕ) = 1 → σ • u = u)
    {a : D.carrier} (ha : a ∈ D.ambientNthPowersSubgroup) :
    D.rootCharacter a hfixed = 1 := by
  obtain ⟨b, hb⟩ := (D.mem_ambientNthPowersSubgroup_iff).1 ha
  apply MonoidHom.ext
  intro σ
  rw [D.rootCharacter_apply]
  rw [← D.rootQuotient_eq_rootCocycle_of_same_pow hfixed a
    (u := Units.map (algebraMap K L).toMonoidHom b)]
  · exact rootQuotient_algebraMap_unit (K := K) (L := L) b σ
  · rw [← map_pow, hb]

/-- The ambient `n`-th-power subgroup lies in the kernel of the Kummer character. -/
theorem ambientNthPowersSubgroup_le_ker
    (hfixed : ∀ σ : Gal(L/K), ∀ u : Lˣ, u ^ (n : ℕ) = 1 → σ • u = u) :
    D.ambientNthPowersSubgroup ≤ MonoidHom.ker (D.kummerCharacterWithoutSection hfixed) := by
  intro a ha
  change D.kummerCharacterWithoutSection hfixed a = 1
  apply MonoidHom.ext
  intro σ
  apply Subtype.ext
  exact congrArg (fun χ : Gal(L/K) →* Lˣ => χ σ)
    (D.rootCharacter_eq_one_of_mem_ambientNthPowers hfixed ha)

/-- For a Galois extension, triviality of the Kummer character forces the
chosen root to come from the base field.  Consequently the kernel is exactly
the subgroup of ambient `n`-th powers, not merely a subgroup containing it. -/
theorem ker_kummerCharacterWithoutSection_eq_ambientNthPowers
    [IsGalois K L]
    (hfixed : ∀ σ : Gal(L/K), ∀ u : Lˣ, u ^ (n : ℕ) = 1 → σ • u = u) :
    MonoidHom.ker (D.kummerCharacterWithoutSection hfixed) =
      D.ambientNthPowersSubgroup := by
  apply le_antisymm
  · intro a ha
    have hroot : ∀ σ : Gal(L/K), σ • D.root a = D.root a := by
      intro σ
      have hvalue : D.rootCharacterToMuWithoutSection a hfixed σ = 1 := by
        have happ := congrArg
          (fun χ : Gal(L/K) →* nthRootsSubgroup L (n : ℕ) ↦ χ σ) ha
        simpa [kummerCharacterWithoutSection] using happ
      have hquot : rootQuotient (K := K) (L := L) (D.root a) σ = 1 := by
        exact congrArg Subtype.val hvalue
      exact (rootQuotient_eq_one_iff (K := K) (L := L) (D.root a) σ).1 hquot
    have hfixedVal : ∀ σ : Gal(L/K), σ (D.root a : L) = D.root a := by
      intro σ
      exact congrArg Units.val (hroot σ)
    obtain ⟨b, hb⟩ :=
      (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) (K := L) (D.root a : L)).2
        hfixedVal
    have hb0 : b ≠ 0 := by
      intro hbzero
      have : (D.root a : L) = 0 := by simpa [hbzero] using hb.symm
      exact Units.ne_zero (D.root a) this
    refine (D.mem_ambientNthPowersSubgroup_iff).2 ⟨Units.mk0 b hb0, ?_⟩
    apply Units.ext
    calc
      ((Units.mk0 b hb0 : Kˣ) ^ (n : ℕ) : K) = b ^ (n : ℕ) := rfl
      _ = a.1 := by
        apply (algebraMap K L).injective
        calc
          algebraMap K L (b ^ (n : ℕ)) = (D.root a : L) ^ (n : ℕ) := by
            rw [map_pow, hb]
          _ = algebraMap K L (a.1 : K) := congrArg Units.val (D.root_pow_eq_map a)
  · exact D.ambientNthPowersSubgroup_le_ker hfixed

/-- The ambient radical quotient `Δ / (Δ ∩ Kˣⁿ)`. -/
def RadicalQuotient : Type _ :=
  D.carrier ⧸ D.ambientNthPowersSubgroup

/-- The commutative group structure transported to the named ambient
radical quotient. -/
instance radicalQuotient_commGroupInstance : CommGroup D.RadicalQuotient := by
  change CommGroup (D.carrier ⧸ D.ambientNthPowersSubgroup)
  infer_instance

/-- Comparison with the group-library presentation of the ambient radical
quotient. -/
def radicalQuotientMulEquiv :
    D.RadicalQuotient ≃* (D.carrier ⧸ D.ambientNthPowersSubgroup) :=
  MulEquiv.refl _

/-- The canonical projection to the named ambient radical quotient. -/
def radicalQuotientMk : D.carrier →* D.RadicalQuotient :=
  QuotientGroup.mk' D.ambientNthPowersSubgroup

/-- The named radical quotient projection agrees with the underlying quotient map. -/
@[simp]
theorem radicalQuotientMk_apply (a : D.carrier) :
    D.radicalQuotientMulEquiv (D.radicalQuotientMk a) =
      (QuotientGroup.mk a : D.carrier ⧸ D.ambientNthPowersSubgroup) :=
  rfl

/-- A radical quotient class is trivial exactly when its representative is an
ambient `n`th power. -/
@[simp]
theorem radicalQuotientMk_eq_one_iff (a : D.carrier) :
    D.radicalQuotientMk a = 1 ↔ a ∈ D.ambientNthPowersSubgroup := by
  change
    (QuotientGroup.mk' D.ambientNthPowersSubgroup) a = 1 ↔
      a ∈ D.ambientNthPowersSubgroup
  exact QuotientGroup.eq_one_iff a

/-- Two radical quotient representatives agree exactly when their ratio is an
ambient `n`th power. -/
@[simp]
theorem radicalQuotientMk_eq_iff (a b : D.carrier) :
    D.radicalQuotientMk a = D.radicalQuotientMk b ↔
      a / b ∈ D.ambientNthPowersSubgroup := by
  change
    (QuotientGroup.mk' D.ambientNthPowersSubgroup) a =
        (QuotientGroup.mk' D.ambientNthPowersSubgroup) b ↔
      a / b ∈ D.ambientNthPowersSubgroup
  exact QuotientGroup.eq_iff_div_mem

/-- Descend a homomorphism through the named ambient radical quotient. -/
def radicalQuotientLift {M : Type*} [Group M]
    (f : D.carrier →* M)
    (hf : D.ambientNthPowersSubgroup ≤ MonoidHom.ker f) :
    D.RadicalQuotient →* M :=
  (QuotientGroup.lift D.ambientNthPowersSubgroup f hf).comp
    D.radicalQuotientMulEquiv.toMonoidHom

/-- The radical quotient lift evaluates on a representative by the prescribed lift. -/
@[simp]
theorem radicalQuotientLift_mk {M : Type*} [Group M]
    (f : D.carrier →* M)
    (hf : D.ambientNthPowersSubgroup ≤ MonoidHom.ker f)
    (a : D.carrier) :
    D.radicalQuotientLift f hf (D.radicalQuotientMk a) = f a :=
  rfl

/-- The Kummer character descended to the correct ambient-power quotient. -/
def quotientKummerCharacterWithoutSection
    (hfixed : ∀ σ : Gal(L/K), ∀ u : Lˣ, u ^ (n : ℕ) = 1 → σ • u = u) :
    D.RadicalQuotient →* (Gal(L/K) →* nthRootsSubgroup L (n : ℕ)) :=
  D.radicalQuotientLift (D.kummerCharacterWithoutSection hfixed)
    (D.ambientNthPowersSubgroup_le_ker hfixed)

/-- The section-free Kummer character on a quotient class is computed from any representative. -/
@[simp] theorem quotientKummerCharacterWithoutSection_mk (a : D.carrier)
    (hfixed : ∀ σ : Gal(L/K), ∀ u : Lˣ, u ^ (n : ℕ) = 1 → σ • u = u) :
    D.quotientKummerCharacterWithoutSection hfixed
        (D.radicalQuotientMk a) =
      D.kummerCharacterWithoutSection hfixed a :=
  D.radicalQuotientLift_mk _ _ a

end RadicalDatum
end RadicalQuotient

end KummerTheory
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_FiniteCharacterEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- The radical subgroup `A_L^n intersect Kˣ` for the actual extension
`L/K`: its elements are precisely the base-field units admitting an `n`-th
root in `Lˣ`. -/
def finiteKummerRadicalSubgroup (n : ℕ+) : Subgroup Kˣ where
  carrier := {a | ∃ β : Lˣ,
    β ^ (n : ℕ) = Units.map (algebraMap K L).toMonoidHom a}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro a b ⟨α, hα⟩ ⟨β, hβ⟩
    refine ⟨α * β, ?_⟩
    rw [mul_pow, hα, hβ, map_mul]
  inv_mem' := by
    rintro a ⟨α, hα⟩
    refine ⟨α⁻¹, ?_⟩
    rw [inv_pow, hα, map_inv]

/-- The finite Kummer radical consists exactly of classes annihilated by every
defining character. -/
@[simp] theorem mem_finiteKummerRadicalSubgroup_iff
    (n : ℕ+) {a : Kˣ} :
    a ∈ finiteKummerRadicalSubgroup (K := K) (L := L) n ↔
      ∃ β : Lˣ, β ^ (n : ℕ) = Units.map (algebraMap K L).toMonoidHom a :=
  Iff.rfl

/-- An arbitrary root choice on the already constructed radical subgroup.
No compatibility between the choices is imposed. -/
def chosenFiniteKummerRadicalDatum (n : ℕ+) : RadicalDatum (K := K) (L := L) n where
  carrier := finiteKummerRadicalSubgroup (K := K) (L := L) n
  root a := Classical.choose a.property
  root_pow_eq a := Classical.choose_spec a.property

/-- The field-level form of the roots-of-unity hypothesis `mu_n subset K`, restricted
to the roots of unity occurring in `L`: every `n`-th root of unity in `Lˣ`
comes from a unit of `K`. -/
def NthRootsOfUnityInBase (n : ℕ+) : Prop :=
  ∀ u : Lˣ, u ^ (n : ℕ) = 1 →
    ∃ zeta : Kˣ, Units.map (algebraMap K L).toMonoidHom zeta = u

/-- Under `mu_n subset K`, every Galois automorphism fixes `mu_n(L)`. -/
theorem nthRootsOfUnity_fixed
    (n : ℕ+) (hmu : NthRootsOfUnityInBase (K := K) (L := L) n)
    (sigma : Gal(L/K)) (u : Lˣ) (hu : u ^ (n : ℕ) = 1) :
    sigma • u = u := by
  obtain ⟨zeta, rfl⟩ := hmu u hu
  exact RadicalDatum.smul_algebraMap_unit (K := K) (L := L) sigma zeta

end FiniteKummerCharacterIso

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_FiniteGeneration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- A primitive `n`-th root in `K` implies the field-level hypothesis that
all `n`-th roots of unity occurring in `L` come from `K`. -/
theorem nthRootsOfUnityInBase_of_primitiveRoots
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    NthRootsOfUnityInBase (K := K) (L := L) n := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  intro u hu
  let eta : rootsOfUnity (n : ℕ) L := ⟨u, hu⟩
  let e : rootsOfUnity (n : ℕ) K ≃* rootsOfUnity (n : ℕ) L :=
    rootsOfUnityEquivOfPrimitiveRoots (algebraMap K L).injective hmu
  refine ⟨(e.symm eta : rootsOfUnity (n : ℕ) K).1, ?_⟩
  apply Units.ext
  exact rootsOfUnityEquivOfPrimitiveRoots_symm_apply
    (algebraMap K L).injective hmu eta

end FiniteKummerGeneration

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_RadicalExtension
set_option synthInstance.maxHeartbeats 400000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- The subgroup `Kˣ^n` of `n`-th powers in the unit group. -/
def unitNthPowersSubgroup (K : Type*) [Field K] (n : ℕ+) : Subgroup Kˣ :=
  (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range

/-- A unit lies in the unit power subgroup exactly when it is an `n`th power of a unit. -/
@[simp] theorem mem_unitNthPowersSubgroup_iff
    (n : ℕ+) {a : Kˣ} :
    a ∈ unitNthPowersSubgroup K n ↔ ∃ b : Kˣ, b ^ (n : ℕ) = a :=
  Iff.rfl

/-- The subgroup-side objects in the Kummer correspondence: subgroups `Delta ≤ Kˣ`
containing `Kˣ^n`. -/
def KummerSubgroup (K : Type*) [Field K] (n : ℕ+) :=
  {Delta : Subgroup Kˣ // unitNthPowersSubgroup K n ≤ Delta}

/-- All roots in `Omega` of the Kummer equations belonging to `Delta`. -/
def kummerRootSet (n : ℕ+) (Delta : Subgroup Kˣ) : Set Omega :=
  {beta | ∃ a : Delta,
    beta ^ (n : ℕ) = algebraMap K Omega (a.1 : K)}

/-- Every prescribed Kummer equation has a root in the separable closure.
This is the only point where the characteristic hypothesis is needed. -/
theorem exists_kummerRootSet
    [IsSepClosure K Omega]
    (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0) (Delta : Subgroup Kˣ) (a : Delta) :
    ∃ beta : Omega,
      beta ∈ kummerRootSet (K := K) (Omega := Omega) n Delta ∧
        beta ^ (n : ℕ) = algebraMap K Omega (a.1 : K) := by
  let aOmega : Omega := algebraMap K Omega (a.1 : K)
  have haOmega : aOmega ≠ 0 :=
    (_root_.map_ne_zero (algebraMap K Omega)).2 a.1.ne_zero
  have hnOmega : ((n : ℕ) : Omega) ≠ 0 := by
    rw [← map_natCast (algebraMap K Omega)]
    exact (_root_.map_ne_zero (algebraMap K Omega)).2 hn
  let : IsSepClosed Omega := IsSepClosure.sep_closed K
  obtain ⟨beta, hbeta⟩ := IsSepClosed.exists_root
    (X ^ (n : ℕ) - C aOmega)
    (by rw [degree_X_pow_sub_C n.pos]; exact_mod_cast n.ne_zero)
    (separable_X_pow_sub_C aOmega hnOmega haOmega)
  have hpow : beta ^ (n : ℕ) = aOmega := by
    apply sub_eq_zero.mp
    simpa [IsRoot.def, aOmega] using hbeta
  exact ⟨beta, ⟨a, hpow⟩, hpow⟩

/-- A Kummer root is nonzero because its prescribed power is a unit. -/
theorem kummerRootSet_ne_zero
    (n : ℕ+) (Delta : Subgroup Kˣ) {beta : Omega}
    (hbeta : beta ∈ kummerRootSet (K := K) (Omega := Omega) n Delta) :
    beta ≠ 0 := by
  obtain ⟨a, ha⟩ := hbeta
  intro hzero
  have : algebraMap K Omega (a.1 : K) = 0 := by
    rw [← ha, hzero, zero_pow n.ne_zero]
  exact ((_root_.map_ne_zero (algebraMap K Omega)).2 a.1.ne_zero) this

end RadicalExtension

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_InfiniteContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- The group `μₙ(L)` equipped explicitly with the discrete topology used for
continuous characters in the infinite form of the finite Kummer character equivalence. -/
def DiscreteNthRootsSubgroup (L : Type*) [Field L] (n : ℕ) :=
  nthRootsSubgroup L n

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_FiniteSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- For each member of a finite Kummer root set, choose its coefficient in
`Delta`.  This choice is made only after the finite root set is known. -/
def chosenFiniteSupportCoefficient
    (n : ℕ+) (Delta : Subgroup Kˣ) (T : Finset Omega)
    (hT : (T : Set Omega) ⊆ kummerRootSet (K := K) (Omega := Omega) n Delta)
    (beta : T) : Delta :=
  Classical.choose (hT beta.property)

/-- The finite set of base-field coefficients used by the selected roots. -/
def chosenFiniteSupportCoefficientSet
    (n : ℕ+) (Delta : Subgroup Kˣ) (T : Finset Omega)
    (hT : (T : Set Omega) ⊆ kummerRootSet (K := K) (Omega := Omega) n Delta) :
    Finset Kˣ := by
  classical
  exact Finset.univ.image fun beta : T => (chosenFiniteSupportCoefficient n Delta T hT beta).1

/-- The subgroup `Delta₀` generated by the finitely many selected
coefficients. -/
def chosenFiniteSupportCoefficientSubgroup
    (n : ℕ+) (Delta : Subgroup Kˣ) (T : Finset Omega)
    (hT : (T : Set Omega) ⊆ kummerRootSet (K := K) (Omega := Omega) n Delta) :
    Subgroup Kˣ :=
  Subgroup.closure
    (chosenFiniteSupportCoefficientSet (K := K) (Omega := Omega) n Delta T hT : Set Kˣ)


/-- Add all ambient `n`-th powers to the finite coefficient subgroup.  The
result is an admissible subgroup-side object for the Kummer correspondence. -/
def admissibleFiniteSupportSubgroup
    (n : ℕ+) (Delta : KummerSubgroup K n) (T : Finset Omega)
    (hT : (T : Set Omega) ⊆
      kummerRootSet (K := K) (Omega := Omega) n Delta.1) :
    KummerSubgroup K n :=
  ⟨unitNthPowersSubgroup K n ⊔
      chosenFiniteSupportCoefficientSubgroup (K := K) (Omega := Omega) n Delta.1 T hT,
    le_sup_left⟩

/-- The copy of `Kˣⁿ` inside the admissible finite-support subgroup. -/
def finiteSupportNthPowersSubgroup
    (n : ℕ+) (Delta : KummerSubgroup K n) (T : Finset Omega)
    (hT : (T : Set Omega) ⊆
      kummerRootSet (K := K) (Omega := Omega) n Delta.1) :
    Subgroup (admissibleFiniteSupportSubgroup
      (K := K) (Omega := Omega) n Delta T hT).1 :=
  (unitNthPowersSubgroup K n).comap
    (admissibleFiniteSupportSubgroup
      (K := K) (Omega := Omega) n Delta T hT).1.subtype

/-- The finite-support quotient `Delta₀ / Kˣⁿ`. -/
def FiniteSupportKummerQuotient
    (n : ℕ+) (Delta : KummerSubgroup K n) (T : Finset Omega)
    (hT : (T : Set Omega) ⊆
      kummerRootSet (K := K) (Omega := Omega) n Delta.1) :=
  (admissibleFiniteSupportSubgroup
      (K := K) (Omega := Omega) n Delta T hT).1 ⧸
    finiteSupportNthPowersSubgroup
      (K := K) (Omega := Omega) n Delta T hT

/-- The commutative group structure on the named finite-support Kummer
quotient. -/
instance finiteSupportKummerQuotient_commGroupInstance
    (n : ℕ+) (Delta : KummerSubgroup K n) (T : Finset Omega)
    (hT : (T : Set Omega) ⊆
      kummerRootSet (K := K) (Omega := Omega) n Delta.1) :
    CommGroup (FiniteSupportKummerQuotient
      (K := K) (Omega := Omega) n Delta T hT) := by
  change CommGroup
    ((admissibleFiniteSupportSubgroup
        (K := K) (Omega := Omega) n Delta T hT).1 ⧸
      finiteSupportNthPowersSubgroup
        (K := K) (Omega := Omega) n Delta T hT)
  infer_instance

/-- Comparison with the group-library presentation of the finite-support
Kummer quotient. -/
def finiteSupportKummerQuotientMulEquiv
    (n : ℕ+) (Delta : KummerSubgroup K n) (T : Finset Omega)
    (hT : (T : Set Omega) ⊆
      kummerRootSet (K := K) (Omega := Omega) n Delta.1) :
    FiniteSupportKummerQuotient (K := K) (Omega := Omega) n Delta T hT ≃*
      ((admissibleFiniteSupportSubgroup
          (K := K) (Omega := Omega) n Delta T hT).1 ⧸
        finiteSupportNthPowersSubgroup
          (K := K) (Omega := Omega) n Delta T hT) :=
  MulEquiv.refl _

/-- The canonical projection to the named finite-support Kummer quotient. -/
def finiteSupportKummerQuotientMk
    (n : ℕ+) (Delta : KummerSubgroup K n) (T : Finset Omega)
    (hT : (T : Set Omega) ⊆
      kummerRootSet (K := K) (Omega := Omega) n Delta.1) :
    (admissibleFiniteSupportSubgroup
        (K := K) (Omega := Omega) n Delta T hT).1 →*
      FiniteSupportKummerQuotient
        (K := K) (Omega := Omega) n Delta T hT :=
  QuotientGroup.mk'
    (finiteSupportNthPowersSubgroup
      (K := K) (Omega := Omega) n Delta T hT)

/-- A finite-support Kummer class is trivial exactly when its representative lies
in the defining subgroup. -/
@[simp]
theorem finiteSupportKummerQuotientMk_eq_one_iff
    (n : ℕ+) (Delta : KummerSubgroup K n) (T : Finset Omega)
    (hT : (T : Set Omega) ⊆
      kummerRootSet (K := K) (Omega := Omega) n Delta.1)
    (a : (admissibleFiniteSupportSubgroup
      (K := K) (Omega := Omega) n Delta T hT).1) :
    finiteSupportKummerQuotientMk
        (K := K) (Omega := Omega) n Delta T hT a = 1 ↔
      a ∈ finiteSupportNthPowersSubgroup
        (K := K) (Omega := Omega) n Delta T hT := by
  change
    (QuotientGroup.mk'
      (finiteSupportNthPowersSubgroup
        (K := K) (Omega := Omega) n Delta T hT)) a = 1 ↔ _
  exact QuotientGroup.eq_one_iff a

/-- Equality of finite-support Kummer classes is characterized by their quotient
lying in the defining subgroup. -/
@[simp]
theorem finiteSupportKummerQuotientMk_eq_iff
    (n : ℕ+) (Delta : KummerSubgroup K n) (T : Finset Omega)
    (hT : (T : Set Omega) ⊆
      kummerRootSet (K := K) (Omega := Omega) n Delta.1)
    (a b : (admissibleFiniteSupportSubgroup
      (K := K) (Omega := Omega) n Delta T hT).1) :
    finiteSupportKummerQuotientMk
        (K := K) (Omega := Omega) n Delta T hT a =
      finiteSupportKummerQuotientMk
        (K := K) (Omega := Omega) n Delta T hT b ↔
      a / b ∈ finiteSupportNthPowersSubgroup
        (K := K) (Omega := Omega) n Delta T hT := by
  change
    (QuotientGroup.mk'
      (finiteSupportNthPowersSubgroup
        (K := K) (Omega := Omega) n Delta T hT)) a =
      (QuotientGroup.mk'
        (finiteSupportNthPowersSubgroup
          (K := K) (Omega := Omega) n Delta T hT)) b ↔ _
  exact QuotientGroup.eq_iff_div_mem

/-- Descend a homomorphism through the named finite-support quotient. -/
def finiteSupportKummerQuotientLift {M : Type*} [Group M]
    (n : ℕ+) (Delta : KummerSubgroup K n) (T : Finset Omega)
    (hT : (T : Set Omega) ⊆
      kummerRootSet (K := K) (Omega := Omega) n Delta.1)
    (f : (admissibleFiniteSupportSubgroup
      (K := K) (Omega := Omega) n Delta T hT).1 →* M)
    (hf : finiteSupportNthPowersSubgroup
      (K := K) (Omega := Omega) n Delta T hT ≤ MonoidHom.ker f) :
    FiniteSupportKummerQuotient
      (K := K) (Omega := Omega) n Delta T hT →* M :=
  (QuotientGroup.lift
    (finiteSupportNthPowersSubgroup
      (K := K) (Omega := Omega) n Delta T hT) f hf).comp
    (finiteSupportKummerQuotientMulEquiv
      (K := K) (Omega := Omega) n Delta T hT).toMonoidHom

/-- The finite-support quotient lift evaluates on a representative by the chosen lift. -/
@[simp]
theorem finiteSupportKummerQuotientLift_mk {M : Type*} [Group M]
    (n : ℕ+) (Delta : KummerSubgroup K n) (T : Finset Omega)
    (hT : (T : Set Omega) ⊆
      kummerRootSet (K := K) (Omega := Omega) n Delta.1)
    (f : (admissibleFiniteSupportSubgroup
      (K := K) (Omega := Omega) n Delta T hT).1 →* M)
    (hf : finiteSupportNthPowersSubgroup
      (K := K) (Omega := Omega) n Delta T hT ≤ MonoidHom.ker f)
    (a : (admissibleFiniteSupportSubgroup
      (K := K) (Omega := Omega) n Delta T hT).1) :
    finiteSupportKummerQuotientLift
        (K := K) (Omega := Omega) n Delta T hT f hf
        (finiteSupportKummerQuotientMk
          (K := K) (Omega := Omega) n Delta T hT a) = f a :=
  rfl


end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_FiniteDualSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- Restrict a unit-valued character to `μₙ` when its source is killed by
`n`. -/
def characterToNthRoots
    {G K : Type*} [Group G] [Field K]
    (n : ℕ+) (hexponent : ∀ g : G, g ^ (n : ℕ) = 1)
    (φ : G →* Kˣ) : G →* nthRootsSubgroup K (n : ℕ) where
  toFun g :=
    ⟨φ g, by
      calc
        φ g ^ (n : ℕ) = φ (g ^ (n : ℕ)) := (map_pow φ g (n : ℕ)).symm
        _ = 1 := by rw [hexponent g, map_one]⟩
  map_one' := by
    apply Subtype.ext
    exact map_one φ
  map_mul' := by
    intro g h
    apply Subtype.ext
    exact map_mul φ g h

/-- A finite character evaluates in the subgroup of `n`th roots of unity. -/
@[simp] theorem characterToNthRoots_apply
    {G K : Type*} [Group G] [Field K]
    (n : ℕ+) (hexponent : ∀ g : G, g ^ (n : ℕ) = 1)
    (φ : G →* Kˣ) (g : G) :
    (characterToNthRoots n hexponent φ g : Kˣ) = φ g :=
  rfl

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_RestrictedFinite
attribute [-instance] _root_.KummerTheory.finiteSupportKummerQuotient_commGroupInstance
attribute [-simp] _root_.KummerTheory.finiteSupportKummerQuotientLift_mk _root_.KummerTheory.finiteSupportKummerQuotientMk_eq_iff _root_.KummerTheory.finiteSupportKummerQuotientMk_eq_one_iff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# finite restricted Kummer pairing

Let `Delta ≤ Kˣ` contain `Kˣ^n`, and suppose every element of `Delta` has
an `n`-th root in a finite Galois extension `L/K`.  This file restricts the
actual finite Kummer character to

`Delta / Kˣ^n → Hom(Gal(L/K), μₙ(L))`.

The exact kernel theorem for the actual radical subgroup proves this
restricted map injective.  We then transpose the pairing.  If `L` is
generated by the roots belonging to `Delta`, the transpose is injective
because an automorphism in its kernel fixes every generator.

No character-surjectivity or lattice-correspondence conclusion is assumed.
-/

noncomputable section

namespace KummerTheory

section RestrictedFiniteKummer

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The copy of `Kˣ^n` inside an admissible subgroup `Delta`. -/
def restrictedNthPowersSubgroup
    (n : ℕ+) (Delta : KummerSubgroup K n) : Subgroup Delta.1 :=
  (unitNthPowersSubgroup K n).comap Delta.1.subtype

/-- Restricted power-subgroup membership is characterized by an `n`th-power
witness in the restricted group. -/
@[simp] theorem mem_restrictedNthPowersSubgroup_iff
    (n : ℕ+) (Delta : KummerSubgroup K n) {a : Delta.1} :
    a ∈ restrictedNthPowersSubgroup n Delta ↔
      ∃ b : Kˣ, b ^ (n : ℕ) = a.1 :=
  Iff.rfl

/-- The subgroup-side quotient `Delta / Kˣ^n` from the Kummer correspondence. -/
def RestrictedRadicalQuotient
    (n : ℕ+) (Delta : KummerSubgroup K n) :=
  Delta.1 ⧸ restrictedNthPowersSubgroup n Delta

/-- The commutative group structure on the named restricted radical
quotient. -/
instance restrictedRadicalQuotient_commGroupInstance
    (n : ℕ+) (Delta : KummerSubgroup K n) :
    CommGroup (RestrictedRadicalQuotient n Delta) := by
  change CommGroup (Delta.1 ⧸ restrictedNthPowersSubgroup n Delta)
  infer_instance

/-- Comparison with the group-library presentation of the restricted
radical quotient. -/
def restrictedRadicalQuotientMulEquiv
    (n : ℕ+) (Delta : KummerSubgroup K n) :
    RestrictedRadicalQuotient n Delta ≃*
      (Delta.1 ⧸ restrictedNthPowersSubgroup n Delta) :=
  MulEquiv.refl _

/-- The canonical projection to the named restricted radical quotient. -/
def restrictedRadicalQuotientMk
    (n : ℕ+) (Delta : KummerSubgroup K n) :
    Delta.1 →* RestrictedRadicalQuotient n Delta :=
  QuotientGroup.mk' (restrictedNthPowersSubgroup n Delta)

/-- A restricted radical class is trivial exactly when its representative is a
restricted `n`th power. -/
@[simp]
theorem restrictedRadicalQuotientMk_eq_one_iff
    (n : ℕ+) (Delta : KummerSubgroup K n) (a : Delta.1) :
    restrictedRadicalQuotientMk n Delta a = 1 ↔
      a ∈ restrictedNthPowersSubgroup n Delta := by
  change
    (QuotientGroup.mk' (restrictedNthPowersSubgroup n Delta)) a = 1 ↔ _
  exact QuotientGroup.eq_one_iff a

/-- Equality in the restricted radical quotient is characterized by a restricted power ratio. -/
@[simp]
theorem restrictedRadicalQuotientMk_eq_iff
    (n : ℕ+) (Delta : KummerSubgroup K n) (a b : Delta.1) :
    restrictedRadicalQuotientMk n Delta a =
        restrictedRadicalQuotientMk n Delta b ↔
      a / b ∈ restrictedNthPowersSubgroup n Delta := by
  change
    (QuotientGroup.mk' (restrictedNthPowersSubgroup n Delta)) a =
        (QuotientGroup.mk' (restrictedNthPowersSubgroup n Delta)) b ↔ _
  exact QuotientGroup.eq_iff_div_mem

/-- Descend a homomorphism through the named restricted radical quotient. -/
def restrictedRadicalQuotientLift {M : Type*} [Group M]
    (n : ℕ+) (Delta : KummerSubgroup K n) (f : Delta.1 →* M)
    (hf : restrictedNthPowersSubgroup n Delta ≤ MonoidHom.ker f) :
    RestrictedRadicalQuotient n Delta →* M :=
  (QuotientGroup.lift (restrictedNthPowersSubgroup n Delta) f hf).comp
    (restrictedRadicalQuotientMulEquiv n Delta).toMonoidHom

/-- The restricted radical lift evaluates on quotient representatives by the chosen lift. -/
@[simp]
theorem restrictedRadicalQuotientLift_mk {M : Type*} [Group M]
    (n : ℕ+) (Delta : KummerSubgroup K n) (f : Delta.1 →* M)
    (hf : restrictedNthPowersSubgroup n Delta ≤ MonoidHom.ker f)
    (a : Delta.1) :
    restrictedRadicalQuotientLift n Delta f hf
        (restrictedRadicalQuotientMk n Delta a) = f a :=
  rfl

/-- The field-level fixed-roots hypothesis supplied by a primitive root in
the base field. -/
theorem restrictedKummerFixed
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    ∀ sigma : Gal(L/K), ∀ u : Lˣ,
      u ^ (n : ℕ) = 1 → sigma • u = u :=
  nthRootsOfUnity_fixed (K := K) (L := L) n
    (nthRootsOfUnityInBase_of_primitiveRoots (K := K) (L := L) n hmu)

/-- Include the specified subgroup into the actual radical subgroup of
`L/K`. -/
def restrictedRadicalInclusion
    (n : ℕ+) (Delta : KummerSubgroup K n)
    (hDelta : Delta.1 ≤ finiteKummerRadicalSubgroup (K := K) (L := L) n) :
    Delta.1 →* (chosenFiniteKummerRadicalDatum (K := K) (L := L) n).carrier :=
  Subgroup.inclusion hDelta

/-- The Kummer character restricted from the actual radical subgroup to
the prescribed subgroup `Delta`. -/
def restrictedSubgroupKummerCharacter
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (Delta : KummerSubgroup K n)
    (hDelta : Delta.1 ≤ finiteKummerRadicalSubgroup (K := K) (L := L) n) :
    Delta.1 →* (Gal(L/K) →* nthRootsSubgroup L (n : ℕ)) :=
  ((chosenFiniteKummerRadicalDatum (K := K) (L := L) n).kummerCharacterWithoutSection
    (restrictedKummerFixed n hmu)).comp
      (restrictedRadicalInclusion n Delta hDelta)

/-- The restricted subgroup character has exactly the expected kernel `Kˣ^n`.
This is inherited from the exact kernel theorem on the actual radical
subgroup; it is not an additional hypothesis. -/
theorem ker_restrictedSubgroupKummerCharacter
    [IsGalois K L]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (Delta : KummerSubgroup K n)
    (hDelta : Delta.1 ≤ finiteKummerRadicalSubgroup (K := K) (L := L) n) :
    MonoidHom.ker (restrictedSubgroupKummerCharacter n hmu Delta hDelta) =
      restrictedNthPowersSubgroup n Delta := by
  let D := chosenFiniteKummerRadicalDatum (K := K) (L := L) n
  let hfixed := restrictedKummerFixed (K := K) (L := L) n hmu
  apply le_antisymm
  · intro a ha
    have hinc : restrictedRadicalInclusion n Delta hDelta a ∈
        MonoidHom.ker (D.kummerCharacterWithoutSection hfixed) := by
      simpa [restrictedSubgroupKummerCharacter, D, hfixed] using ha
    have hpowers : restrictedRadicalInclusion n Delta hDelta a ∈
        D.ambientNthPowersSubgroup := by
      rw [← D.ker_kummerCharacterWithoutSection_eq_ambientNthPowers hfixed]
      exact hinc
    exact (mem_restrictedNthPowersSubgroup_iff n Delta).2
      ((D.mem_ambientNthPowersSubgroup_iff).1 hpowers)
  · intro a ha
    have hpowers : restrictedRadicalInclusion n Delta hDelta a ∈
        D.ambientNthPowersSubgroup :=
      (D.mem_ambientNthPowersSubgroup_iff).2
        ((mem_restrictedNthPowersSubgroup_iff n Delta).1 ha)
    have hker : restrictedRadicalInclusion n Delta hDelta a ∈
        MonoidHom.ker (D.kummerCharacterWithoutSection hfixed) := by
      rw [D.ker_kummerCharacterWithoutSection_eq_ambientNthPowers hfixed]
      exact hpowers
    simpa [restrictedSubgroupKummerCharacter, D, hfixed] using hker

/-- The restricted character descended to `Delta / Kˣ^n`. -/
def restrictedQuotientKummerCharacter
    [IsGalois K L]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (Delta : KummerSubgroup K n)
    (hDelta : Delta.1 ≤ finiteKummerRadicalSubgroup (K := K) (L := L) n) :
    RestrictedRadicalQuotient n Delta →*
      (Gal(L/K) →* nthRootsSubgroup L (n : ℕ)) :=
  restrictedRadicalQuotientLift n Delta
    (restrictedSubgroupKummerCharacter n hmu Delta hDelta)
    (by rw [ker_restrictedSubgroupKummerCharacter n hmu Delta hDelta])

/-- The restricted Kummer character is computed on a quotient representative by
its root character. -/
@[simp] theorem restrictedQuotientKummerCharacter_mk
    [IsGalois K L]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (Delta : KummerSubgroup K n)
    (hDelta : Delta.1 ≤ finiteKummerRadicalSubgroup (K := K) (L := L) n)
    (a : Delta.1) :
    restrictedQuotientKummerCharacter n hmu Delta hDelta
        (restrictedRadicalQuotientMk n Delta a) =
      restrictedSubgroupKummerCharacter n hmu Delta hDelta a :=
  rfl

/-- Transpose the restricted Kummer pairing by evaluation. -/
def restrictedKummerTranspose
    [IsGalois K L]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (Delta : KummerSubgroup K n)
    (hDelta : Delta.1 ≤ finiteKummerRadicalSubgroup (K := K) (L := L) n) :
    Gal(L/K) →*
      (RestrictedRadicalQuotient n Delta →* nthRootsSubgroup L (n : ℕ)) where
  toFun sigma :=
    { toFun := fun q => restrictedQuotientKummerCharacter n hmu Delta hDelta q sigma
      map_one' := by simp
      map_mul' := by
        intro q r
        exact congrArg (fun chi : Gal(L/K) →* nthRootsSubgroup L (n : ℕ) => chi sigma)
          (map_mul (restrictedQuotientKummerCharacter n hmu Delta hDelta) q r) }
  map_one' := by
    apply MonoidHom.ext
    intro q
    exact map_one (restrictedQuotientKummerCharacter n hmu Delta hDelta q)
  map_mul' := by
    intro sigma tau
    apply MonoidHom.ext
    intro q
    exact map_mul (restrictedQuotientKummerCharacter n hmu Delta hDelta q) sigma tau

/-- The restricted Kummer transpose evaluates a radical class against the
corresponding character. -/
@[simp] theorem restrictedKummerTranspose_apply
    [IsGalois K L]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (Delta : KummerSubgroup K n)
    (hDelta : Delta.1 ≤ finiteKummerRadicalSubgroup (K := K) (L := L) n)
    (sigma : Gal(L/K)) (q : RestrictedRadicalQuotient n Delta) :
    restrictedKummerTranspose n hmu Delta hDelta sigma q =
      restrictedQuotientKummerCharacter n hmu Delta hDelta q sigma :=
  rfl

end RestrictedFiniteKummer

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_GroupTheory_PowerIndex
attribute [-simp] _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Power indices in commutative groups

Reusable kernel, quotient, product, and additive-transport formulas for
`n`-th powers in commutative groups.  The basic power map and its image and
kernel are mathlib's `powMonoidHom`, `MonoidHom.range`, and `MonoidHom.ker`.
-/

noncomputable section

namespace LocalFieldTheory

open scoped Int

section NthPowers

universe uG uH uU

variable (G : Type uG) (H : Type uH) (U : Type uU)
variable [CommGroup G] [CommGroup H] [CommGroup U]


/-- In a finite commutative group, the `n`-th-power quotient has the same
cardinality as the subgroup of `n`-torsion elements.  This is the finite
kernel/cokernel equality for the power endomorphism. -/
theorem card_nthPowerQuotient_eq_nthPowerKernel
    [Finite G] (n : ℕ) :
    Nat.card (G ⧸ (powMonoidHom n : G →* G).range) =
      Nat.card ((powMonoidHom n : G →* G).ker) := by
  change ((powMonoidHom n : G →* G)).range.index = Nat.card ((powMonoidHom n : G →* G)).ker
  rw [Subgroup.index_range]

/-- A multiplicative equivalence transports `n`-torsion kernels. -/
def nthPowerKernelEquivOfMulEquiv (n : ℕ) (e : G ≃* H) :
    (powMonoidHom n : G →* G).ker ≃* (powMonoidHom n : H →* H).ker where
  toFun x :=
    ⟨e (x : G), by
      have hx : (x : G) ^ n = 1 :=
        (MonoidHom.mem_ker (G := G)).1 x.property
      change (e (x : G)) ^ n = 1
      simpa [map_pow] using congrArg e hx⟩
  invFun y :=
    ⟨e.symm (y : H), by
      have hy : (y : H) ^ n = 1 :=
        (MonoidHom.mem_ker (G := H)).1 y.property
      change (e.symm (y : H)) ^ n = 1
      simpa [map_pow] using congrArg e.symm hy⟩
  left_inv x := by
    ext
    simp
  right_inv y := by
    ext
    simp
  map_mul' x y := by
    ext
    simp

/-- A multiplicative equivalence carries the range of the `n`-th power map onto the corresponding
range. -/
theorem powMonoidHom_range_map (n : ℕ) (e : G ≃* H) :
    ((powMonoidHom n : G →* G).range).map e.toMonoidHom = (powMonoidHom n : H →* H).range := by
  exact e.map_range_powMonoidHom n

/-- An injective multiplicative homomorphism transports finiteness of the
ambient power kernel to the source power kernel. -/
theorem finite_nthPowerKernel_of_injective
    (n : ℕ) (f : G →* H) (hf : Function.Injective f)
    [Finite ((powMonoidHom n : H →* H).ker)] :
    Finite ((powMonoidHom n : G →* G).ker) := by
  let mapKernel : (powMonoidHom n : G →* G).ker →
      (powMonoidHom n : H →* H).ker := fun x =>
    ⟨f x, (MonoidHom.mem_ker (G := H)).2 (by
      have hx : (x : G) ^ n = 1 := by
        simpa only [powMonoidHom_apply] using
          (MonoidHom.mem_ker (G := G)).1 x.property
      rw [powMonoidHom_apply, ← map_pow, hx, map_one])⟩
  exact Finite.of_injective mapKernel fun x y hxy => by
    apply Subtype.ext
    exact hf (congrArg Subtype.val hxy)

/-- The power kernel in the unit group of a commutative ring is Mathlib's
group of roots of unity. -/
theorem powMonoidHom_ker_units_eq_rootsOfUnity
    (R : Type*) [CommRing R] (n : ℕ) :
    (powMonoidHom n : Rˣ →* Rˣ).ker = rootsOfUnity n R := by
  ext x
  exact MonoidHom.mem_ker

/-- For nonzero exponent over a domain, the unit-group power kernel is
finite because it is the finite set of roots of `X ^ n - 1`. -/
noncomputable instance finite_powMonoidHom_ker_units
    (R : Type*) [CommRing R] [IsDomain R] (n : ℕ) [NeZero n] :
    Finite ((powMonoidHom n : Rˣ →* Rˣ).ker) := by
  rw [powMonoidHom_ker_units_eq_rootsOfUnity]
  infer_instance

/-- A multiplicative equivalence transports quotients by `n`-th powers. -/
def nthPowerQuotientEquivOfMulEquiv (n : ℕ) (e : G ≃* H) :
    G ⧸ (powMonoidHom n : G →* G).range ≃* H ⧸ (powMonoidHom n : H →* H).range :=
  QuotientGroup.congr ((powMonoidHom n : G →* G).range) ((powMonoidHom n : H →* H).range) e
    (powMonoidHom_range_map G H n e)

/-- The quotient equivalence induced by a multiplicative equivalence maps each power-class
representative to its image. -/
@[simp]
theorem nthPowerQuotientEquivOfMulEquiv_mk (n : ℕ) (e : G ≃* H) (x : G) :
    nthPowerQuotientEquivOfMulEquiv G H n e
        (QuotientGroup.mk' ((powMonoidHom n : G →* G).range) x) =
      QuotientGroup.mk' ((powMonoidHom n : H →* H).range) (e x) :=
  rfl

/-- Finiteness of a power quotient transports backwards along a
multiplicative equivalence. -/
theorem finite_nthPowerQuotient_of_mulEquiv
    (n : ℕ) (e : G ≃* H)
    [Finite (H ⧸ (powMonoidHom n : H →* H).range)] :
    Finite (G ⧸ (powMonoidHom n : G →* G).range) :=
  Finite.of_equiv
    (H ⧸ (powMonoidHom n : H →* H).range)
    (nthPowerQuotientEquivOfMulEquiv G H n e).symm.toEquiv

/-- The `n`-torsion kernel of a product is the product of the two
`n`-torsion kernels. -/
def nthPowerKernelProductEquiv (n : ℕ) :
    (powMonoidHom n : (G × H) →* (G × H)).ker ≃*
      (powMonoidHom n : G →* G).ker × (powMonoidHom n : H →* H).ker where
  toFun x :=
    (⟨(x : G × H).1, by
        have hx : (x : G × H) ^ n = 1 :=
          (MonoidHom.mem_ker (G := G × H)).1 x.property
        have hfst := congrArg Prod.fst hx
        simpa using hfst⟩,
      ⟨(x : G × H).2, by
        have hx : (x : G × H) ^ n = 1 :=
          (MonoidHom.mem_ker (G := G × H)).1 x.property
        have hsnd := congrArg Prod.snd hx
        simpa using hsnd⟩)
  invFun x :=
    ⟨((x.1 : G), (x.2 : H)), by
      have hx₁ : (x.1 : G) ^ n = 1 :=
        (MonoidHom.mem_ker (G := G)).1 x.1.property
      have hx₂ : (x.2 : H) ^ n = 1 :=
        (MonoidHom.mem_ker (G := H)).1 x.2.property
      change (((x.1 : G), (x.2 : H)) : G × H) ^ n = 1
      ext <;> simp [hx₁, hx₂]⟩
  left_inv x := by
    ext <;> rfl
  right_inv x := by
    ext <;> rfl
  map_mul' x y := by
    ext <;> rfl

/-- Finiteness of the two factor kernels transports across the canonical
product-kernel equivalence. -/
noncomputable instance finite_powMonoidHom_ker_prod (n : ℕ)
    [Finite ((powMonoidHom n : G →* G).ker)]
    [Finite ((powMonoidHom n : H →* H).ker)] :
    Finite ((powMonoidHom n : (G × H) →* (G × H)).ker) :=
  Finite.of_equiv
    ((powMonoidHom n : G →* G).ker × (powMonoidHom n : H →* H).ker)
    (nthPowerKernelProductEquiv G H n).symm.toEquiv

/-- Cardinality form of `nthPowerKernelProductEquiv`. -/
theorem card_nthPowerKernelProduct (n : ℕ)
    [Finite ((powMonoidHom n : G →* G).ker)]
    [Finite ((powMonoidHom n : H →* H).ker)] :
    Nat.card ((powMonoidHom n : (G × H) →* (G × H)).ker) =
      Nat.card ((powMonoidHom n : G →* G).ker) *
        Nat.card ((powMonoidHom n : H →* H).ker) := by
  rw [Nat.card_congr (nthPowerKernelProductEquiv G H n).toEquiv,
    Nat.card_prod]

/-- A product decomposition of a commutative group splits the cardinality of
the `n`-torsion kernel as the product of the two factor kernels. -/
theorem card_nthPowerKernel_eq_mul_of_mulEquiv_prod
    (n : ℕ) (e : G ≃* H × U)
    [Finite ((powMonoidHom n : G →* G).ker)]
    [Finite ((powMonoidHom n : H →* H).ker)]
    [Finite ((powMonoidHom n : U →* U).ker)] :
    Nat.card ((powMonoidHom n : G →* G).ker) =
      Nat.card ((powMonoidHom n : H →* H).ker) *
        Nat.card ((powMonoidHom n : U →* U).ker) := by
  calc
    Nat.card ((powMonoidHom n : G →* G).ker) =
        Nat.card ((powMonoidHom n : (H × U) →* (H × U)).ker) := by
      rw [Nat.card_congr
        (nthPowerKernelEquivOfMulEquiv G (H × U) n e).toEquiv]
    _ =
        Nat.card ((powMonoidHom n : H →* H).ker) *
          Nat.card ((powMonoidHom n : U →* U).ker) :=
      card_nthPowerKernelProduct H U n

/-- The product map from a product group to the product of its `n`-th-power
quotients. -/
def nthPowerProductQuotientHom (n : ℕ) :
    G × H →* (G ⧸ (powMonoidHom n : G →* G).range) × (H ⧸ (powMonoidHom n : H →* H).range) where
  toFun x :=
    (QuotientGroup.mk' ((powMonoidHom n : G →* G).range) x.1,
      QuotientGroup.mk' ((powMonoidHom n : H →* H).range) x.2)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Every pair of power classes is represented by a power class in the product group. -/
theorem nthPowerProductQuotientHom_surjective (n : ℕ) :
    Function.Surjective (nthPowerProductQuotientHom G H n) := by
  intro q
  rcases q with ⟨qG, qH⟩
  refine Quotient.inductionOn' qG ?_
  intro g
  refine Quotient.inductionOn' qH ?_
  intro h
  exact ⟨(g, h), rfl⟩

/-- The product power-class homomorphism has trivial kernel. -/
theorem nthPowerProductQuotientHom_ker (n : ℕ) :
    (nthPowerProductQuotientHom G H n).ker =
      (powMonoidHom n : (G × H) →* (G × H)).range := by
  ext x
  constructor
  · intro hx
    rw [MonoidHom.mem_ker] at hx
    change
      (QuotientGroup.mk' ((powMonoidHom n : G →* G).range) x.1,
        QuotientGroup.mk' ((powMonoidHom n : H →* H).range) x.2) = 1 at hx
    have hxG :
        QuotientGroup.mk' ((powMonoidHom n : G →* G).range) x.1 = 1 :=
      congrArg Prod.fst hx
    have hxH :
        QuotientGroup.mk' ((powMonoidHom n : H →* H).range) x.2 = 1 :=
      congrArg Prod.snd hx
    have hxGmem : x.1 ∈ (powMonoidHom n : G →* G).range :=
      (QuotientGroup.eq_one_iff x.1).1 hxG
    have hxHmem : x.2 ∈ (powMonoidHom n : H →* H).range :=
      (QuotientGroup.eq_one_iff x.2).1 hxH
    rw [MonoidHom.mem_range] at hxGmem hxHmem ⊢
    rcases hxGmem with ⟨g, hg⟩
    rcases hxHmem with ⟨h, hh⟩
    refine ⟨(g, h), ?_⟩
    ext
    · change g ^ n = x.1
      simpa only [powMonoidHom_apply] using hg
    · change h ^ n = x.2
      simpa only [powMonoidHom_apply] using hh
  · intro hx
    rw [MonoidHom.mem_ker]
    rw [MonoidHom.mem_range] at hx
    rcases hx with ⟨y, rfl⟩
    apply Prod.ext
    · exact (QuotientGroup.eq_one_iff ((y.1) ^ n)).2
        ((MonoidHom.mem_range (G := G)).2 ⟨y.1, rfl⟩)
    · exact (QuotientGroup.eq_one_iff ((y.2) ^ n)).2
        ((MonoidHom.mem_range (G := H)).2 ⟨y.2, rfl⟩)

/-- Quotienting a product by `n`-th powers is the product of the two
`n`-th-power quotients. -/
def nthPowerProductQuotientEquiv (n : ℕ) :
    (G × H) ⧸ (powMonoidHom n : (G × H) →* (G × H)).range ≃*
      (G ⧸ (powMonoidHom n : G →* G).range) × (H ⧸ (powMonoidHom n : H →* H).range) :=
  (QuotientGroup.quotientMulEquivOfEq
      (nthPowerProductQuotientHom_ker G H n).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (nthPowerProductQuotientHom G H n)
      (nthPowerProductQuotientHom_surjective G H n))

/-- Finiteness of the factor power quotients transports across the canonical
product-quotient equivalence. -/
noncomputable instance finite_powMonoidHom_rangeQuotient_prod (n : ℕ)
    [Finite (G ⧸ (powMonoidHom n : G →* G).range)]
    [Finite (H ⧸ (powMonoidHom n : H →* H).range)] :
    Finite ((G × H) ⧸ (powMonoidHom n : (G × H) →* (G × H)).range) :=
  Finite.of_equiv
    ((G ⧸ (powMonoidHom n : G →* G).range) × (H ⧸ (powMonoidHom n : H →* H).range))
    (nthPowerProductQuotientEquiv G H n).symm.toEquiv

/-- The number of `n`-th power classes in a product is the product of the two factor class numbers.
The number of `n`-th power classes in a product is the product of the two factor class numbers. -/
theorem card_nthPowerProductQuotient (n : ℕ)
    [Finite (G ⧸ (powMonoidHom n : G →* G).range)]
    [Finite (H ⧸ (powMonoidHom n : H →* H).range)] :
    Nat.card ((G × H) ⧸ (powMonoidHom n : (G × H) →* (G × H)).range) =
      Nat.card (G ⧸ (powMonoidHom n : G →* G).range) *
        Nat.card (H ⧸ (powMonoidHom n : H →* H).range) := by
  rw [Nat.card_congr (nthPowerProductQuotientEquiv G H n).toEquiv,
    Nat.card_prod]

/-- A product decomposition of a commutative group splits the `n`-th-power
quotient index as the product of the two factor indices. -/
theorem card_nthPowerQuotient_eq_mul_of_mulEquiv_prod
    (n : ℕ) (e : G ≃* H × U)
    [Finite (G ⧸ (powMonoidHom n : G →* G).range)]
    [Finite (H ⧸ (powMonoidHom n : H →* H).range)]
    [Finite (U ⧸ (powMonoidHom n : U →* U).range)] :
    Nat.card (G ⧸ (powMonoidHom n : G →* G).range) =
      Nat.card (H ⧸ (powMonoidHom n : H →* H).range) *
        Nat.card (U ⧸ (powMonoidHom n : U →* U).range) := by
  calc
    Nat.card (G ⧸ (powMonoidHom n : G →* G).range) =
        Nat.card ((H × U) ⧸ (powMonoidHom n : (H × U) →* (H × U)).range) := by
      rw [Nat.card_congr
        (nthPowerQuotientEquivOfMulEquiv G (H × U) n e).toEquiv]
    _ =
        Nat.card (H ⧸ (powMonoidHom n : H →* H).range) *
          Nat.card (U ⧸ (powMonoidHom n : U →* U).range) :=
      card_nthPowerProductQuotient H U n

/-- For nonzero `n`, the `n`-th power map on multiplicative integers has trivial kernel. -/
theorem powMonoidHom_ker_multiplicativeInt_eq_bot
    {n : ℕ} (hn : n ≠ 0) :
    (powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).ker = ⊥ := by
  ext x
  constructor
  · intro hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_bot]
    apply Multiplicative.toAdd.injective
    have hmul : (n : ℤ) * Multiplicative.toAdd x = 0 := by
      have h := congrArg Multiplicative.toAdd hx
      simpa [Int.toAdd_pow] using h
    have hnZ : (n : ℤ) ≠ 0 := by
      exact_mod_cast hn
    exact (mul_eq_zero.mp hmul).resolve_left hnZ
  · intro hx
    rw [Subgroup.mem_bot] at hx
    rw [MonoidHom.mem_ker, hx, powMonoidHom_apply, one_pow]

/-- The kernel of a nonzero power map on multiplicative integers is finite. -/
theorem finite_multiplicativeInt_nthPowerKernel
    {n : ℕ} (hn : n ≠ 0) :
    Finite ((powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).ker) := by
  rw [powMonoidHom_ker_multiplicativeInt_eq_bot (n := n) hn]
  infer_instance

/-- The kernel of a nonzero power map on multiplicative integers has one element. -/
theorem card_multiplicativeInt_nthPowerKernel
    {n : ℕ} (hn : n ≠ 0)
    [Finite ((powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).ker)] :
    Nat.card ((powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).ker) = 1 := by
  rw [powMonoidHom_ker_multiplicativeInt_eq_bot (n := n) hn]
  simp

/-- For nonzero `n`, a decomposition `G ≃ U × ℤ` identifies the `n`-torsion
kernel of `G` with the `n`-torsion kernel of the unit factor. -/
theorem card_nthPowerKernel_eq_of_mulEquiv_units_prod_int
    {n : ℕ} (hn : n ≠ 0) (e : G ≃* U × Multiplicative ℤ)
    [Finite ((powMonoidHom n : G →* G).ker)]
    [Finite ((powMonoidHom n : U →* U).ker)] :
    Nat.card ((powMonoidHom n : G →* G).ker) =
      Nat.card ((powMonoidHom n : U →* U).ker) := by
  let := finite_multiplicativeInt_nthPowerKernel hn
  rw [card_nthPowerKernel_eq_mul_of_mulEquiv_prod
    G U (Multiplicative ℤ) n e]
  rw [card_multiplicativeInt_nthPowerKernel hn, Nat.mul_one]

end NthPowers

section AdditivePowers

universe uA uB uG

variable (A : Type uA) [AddCommGroup A]

/-- The additive subgroup of `n`-fold multiples. -/
abbrev nsmulAddSubgroup (n : ℕ) : AddSubgroup A :=
  (nsmulAddMonoidHom n).range

/-- The additive subgroup killed by `x ↦ n • x`. -/
abbrev nsmulAddKernel (n : ℕ) : AddSubgroup A :=
  (nsmulAddMonoidHom n).ker

/-- Membership in the image of multiplication by `n` is equivalent to being an `n`-fold additive
multiple. -/
@[simp]
theorem mem_nsmulAddSubgroup_iff {n : ℕ} {x : A} :
    x ∈ nsmulAddSubgroup A n ↔ ∃ y : A, n • y = x := by
  simp [nsmulAddSubgroup, AddMonoidHom.mem_range]

/-- Membership in the kernel of multiplication by `n` is equivalent to being annihilated by `n`. -/
@[simp]
theorem mem_nsmulAddKernel_iff {n : ℕ} {x : A} :
    x ∈ nsmulAddKernel A n ↔ n • x = 0 := by
  simp [nsmulAddKernel, AddMonoidHom.mem_ker]

/-- Under the `Multiplicative` wrapper, `n`-th powers are exactly additive
`n`-fold multiples. -/
theorem powMonoidHom_range_multiplicative_eq_nsmulAddSubgroup_toSubgroup
    (n : ℕ) :
    (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range =
      AddSubgroup.toSubgroup (nsmulAddSubgroup A n) := by
  ext x
  constructor
  · intro hx
    rw [MonoidHom.mem_range] at hx
    rcases hx with ⟨y, rfl⟩
    simp
  · intro hx
    rw [MonoidHom.mem_range]
    have hxadd : Multiplicative.toAdd x ∈ nsmulAddSubgroup A n := by
      simpa using hx
    rw [mem_nsmulAddSubgroup_iff] at hxadd
    rcases hxadd with ⟨y, hy⟩
    refine ⟨Multiplicative.ofAdd y, ?_⟩
    apply Multiplicative.toAdd.injective
    simp [hy]

/-- The underlying quotient types in multiplicative and additive notation
are canonically equivalent. -/
def multiplicativeNthPowerQuotientEquivAdditive (n : ℕ) :
    (Multiplicative A ⧸ (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range) ≃
      (A ⧸ nsmulAddSubgroup A n) := by
  rw [powMonoidHom_range_multiplicative_eq_nsmulAddSubgroup_toSubgroup]
  exact Equiv.refl _

/-- Finiteness of the additive quotient transports to its multiplicative
presentation without any choice of representatives. -/
noncomputable instance finite_multiplicative_nthPowerQuotient
    (n : ℕ) [Finite (A ⧸ nsmulAddSubgroup A n)] :
    Finite
      (Multiplicative A ⧸ (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range) :=
  Finite.of_equiv (A ⧸ nsmulAddSubgroup A n)
    (multiplicativeNthPowerQuotientEquivAdditive A n).symm

/-- Cardinality/index form of
`powMonoidHom_range_multiplicative_eq_nsmulAddSubgroup_toSubgroup`. -/
theorem card_multiplicative_nthPowerQuotient_eq_nsmulAddSubgroup_index
    (n : ℕ)
    [Finite (Multiplicative A ⧸ (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range)] :
    Nat.card (Multiplicative A ⧸ (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range) =
      (nsmulAddSubgroup A n).index := by
  rw [← Subgroup.index_eq_card
    (H := (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range)]
  rw [powMonoidHom_range_multiplicative_eq_nsmulAddSubgroup_toSubgroup]
  simp

/-- Under logarithmic/additive notation, the `n`-th-power quotient is the
additive quotient by `n`-fold multiples. -/
theorem card_multiplicative_nthPowerQuotient_eq_additive_nsmulQuotient
    (n : ℕ)
    [Finite (Multiplicative A ⧸ (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range)]
    [Finite (A ⧸ nsmulAddSubgroup A n)] :
    Nat.card (Multiplicative A ⧸ (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range) =
      Nat.card (A ⧸ nsmulAddSubgroup A n) := by
  rw [card_multiplicative_nthPowerQuotient_eq_nsmulAddSubgroup_index]
  rw [AddSubgroup.index_eq_card]

/-- Under the `Multiplicative` wrapper, `n`-torsion is exactly the additive
kernel of `x ↦ n • x`. -/
theorem powMonoidHom_ker_multiplicative_eq_nsmulAddKernel_toSubgroup
    (n : ℕ) :
    (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).ker =
      AddSubgroup.toSubgroup (nsmulAddKernel A n) := by
  ext x
  constructor
  · intro hx
    rw [MonoidHom.mem_ker] at hx
    change Multiplicative.toAdd x ∈ nsmulAddKernel A n
    rw [mem_nsmulAddKernel_iff]
    have h := congrArg Multiplicative.toAdd hx
    simpa using h
  · intro hx
    have hxadd : Multiplicative.toAdd x ∈ nsmulAddKernel A n := by
      simpa using hx
    rw [mem_nsmulAddKernel_iff] at hxadd
    rw [MonoidHom.mem_ker]
    apply Multiplicative.toAdd.injective
    simpa using hxadd

/-- The multiplicative power kernel and additive scalar kernel have the same
underlying type. -/
def multiplicativeNthPowerKernelEquivAdditive (n : ℕ) :
    (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).ker ≃ nsmulAddKernel A n := by
  rw [powMonoidHom_ker_multiplicative_eq_nsmulAddKernel_toSubgroup]
  exact Equiv.refl _

/-- Finiteness of the additive scalar kernel transports to multiplicative
notation without introducing a noncanonical enumeration. -/
noncomputable instance finite_multiplicative_nthPowerKernel
    (n : ℕ) [Finite (nsmulAddKernel A n)] :
    Finite ((powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).ker) :=
  Finite.of_equiv (nsmulAddKernel A n)
    (multiplicativeNthPowerKernelEquivAdditive A n).symm

section AdditiveProducts

variable (B : Type uB) [AddCommGroup B]

/-- Finiteness of additive scalar quotients is stable under binary products. -/
noncomputable instance finite_nsmulAddQuotient_prod (n : ℕ)
    [Finite (A ⧸ nsmulAddSubgroup A n)]
    [Finite (B ⧸ nsmulAddSubgroup B n)] :
    Finite ((A × B) ⧸ nsmulAddSubgroup (A × B) n) := by
  let e := MulEquiv.prodMultiplicative A B
  let : Finite
      (Multiplicative (A × B) ⧸
        (powMonoidHom n : (Multiplicative (A × B)) →* (Multiplicative (A × B))).range) :=
    finite_nthPowerQuotient_of_mulEquiv
      (Multiplicative (A × B))
      (Multiplicative A × Multiplicative B) n e
  exact Finite.of_equiv
    (Multiplicative (A × B) ⧸
      (powMonoidHom n : (Multiplicative (A × B)) →* (Multiplicative (A × B))).range)
    (multiplicativeNthPowerQuotientEquivAdditive (A × B) n)

/-- Finiteness of additive scalar kernels is stable under binary products. -/
noncomputable instance finite_nsmulAddKernel_prod (n : ℕ)
    [Finite (nsmulAddKernel A n)]
    [Finite (nsmulAddKernel B n)] :
    Finite (nsmulAddKernel (A × B) n) := by
  let e := MulEquiv.prodMultiplicative A B
  let : Finite
      ((powMonoidHom n : (Multiplicative (A × B)) →* (Multiplicative (A × B))).ker) :=
    Finite.of_equiv
      ((powMonoidHom n : (Multiplicative A × Multiplicative B) →* (Multiplicative A × Multiplicative B)).ker)
      (nthPowerKernelEquivOfMulEquiv
        (Multiplicative (A × B))
        (Multiplicative A × Multiplicative B) n e).symm.toEquiv
  exact Finite.of_equiv
    ((powMonoidHom n : (Multiplicative (A × B)) →* (Multiplicative (A × B))).ker)
    (multiplicativeNthPowerKernelEquivAdditive (A × B) n)

end AdditiveProducts

/-- Cardinality form of the multiplicative/additive kernel translation. -/
theorem card_multiplicative_nthPowerKernel_eq_nsmulAddKernel
    (n : ℕ)
    [Finite ((powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).ker)]
    [Finite (nsmulAddKernel A n)] :
    Nat.card ((powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).ker) =
      Nat.card (nsmulAddKernel A n) := by
  rw [powMonoidHom_ker_multiplicative_eq_nsmulAddKernel_toSubgroup]
  rfl

/-- Finite additive kernel/cokernel equality for the map `x ↦ n • x`, proved
through the multiplicative `n`-th-power translation. -/
theorem card_additive_nsmulQuotient_eq_nsmulKernel
    [Finite A] (n : ℕ) :
    Nat.card (A ⧸ nsmulAddSubgroup A n) =
      Nat.card (nsmulAddKernel A n) := by
  rw [← card_multiplicative_nthPowerQuotient_eq_additive_nsmulQuotient A n]
  rw [card_nthPowerQuotient_eq_nthPowerKernel
    (Multiplicative A) n]
  exact card_multiplicative_nthPowerKernel_eq_nsmulAddKernel A n

variable (G : Type uG) [CommGroup G]

/-- A logarithmic multiplicative equivalence transports an `n`-th-power quotient
to the additive quotient by `n`-fold multiples. -/
theorem card_nthPowerQuotient_eq_additive_nsmulQuotient_of_mulEquiv
    (n : ℕ) (e : G ≃* Multiplicative A)
    [Finite (G ⧸ (powMonoidHom n : G →* G).range)]
    [Finite (A ⧸ nsmulAddSubgroup A n)] :
    Nat.card (G ⧸ (powMonoidHom n : G →* G).range) =
      Nat.card (A ⧸ nsmulAddSubgroup A n) := by
  rw [Nat.card_congr
    (nthPowerQuotientEquivOfMulEquiv G (Multiplicative A) n e).toEquiv]
  exact card_multiplicative_nthPowerQuotient_eq_additive_nsmulQuotient A n

/-- A logarithmic multiplicative equivalence transports the `n`-torsion kernel
to the additive kernel of `x ↦ n • x`. -/
theorem card_nthPowerKernel_eq_additive_nsmulKernel_of_mulEquiv
    (n : ℕ) (e : G ≃* Multiplicative A)
    [Finite ((powMonoidHom n : G →* G).ker)]
    [Finite (nsmulAddKernel A n)] :
    Nat.card ((powMonoidHom n : G →* G).ker) =
      Nat.card (nsmulAddKernel A n) := by
  rw [Nat.card_congr
    (nthPowerKernelEquivOfMulEquiv G (Multiplicative A) n e).toEquiv]
  exact card_multiplicative_nthPowerKernel_eq_nsmulAddKernel A n

end AdditivePowers

end LocalFieldTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.KummerTheory_Concrete_SUnitPreparation_SUnitPowerQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- The total place-set cardinal `s = #S`, with all infinite places included. -/
def totalPlaceCard
    (S : Finset (HeightOneSpectrum (𝓞 K))) : ℕ :=
  Fintype.card (InfinitePlace K) + S.card

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_IdeleClassPowerLocalUnitQuotient_ArchimedeanPowerIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Archimedean power indices in idele class quotients

This file defines the concrete idele-class subgroup attached to local power
conditions and computes its archimedean local indices.
-/

open scoped NumberField Classical NNReal ValuativeRel TensorProduct
open NumberField IsDedekindDomain
open KummerTheory

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type} [Field K] [NumberField K]

/-- The sign of a unit at a real infinite place. -/
def realInfinitePlaceSignHom
    (w : InfinitePlace K)
    (hw : w.IsReal) :
    w.Completionˣ →* SignTypeˣ :=
  (Units.map
      (signHom : ℝ →*₀ SignType).toMonoidHom).comp
    (Units.mapEquiv
      (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal
        hw).toMulEquiv).toMonoidHom

omit [NumberField K] in
/-- Both signs occur at a real infinite place. -/
theorem realInfinitePlaceSignHom_surjective
    (w : InfinitePlace K)
    (hw : w.IsReal) :
    Function.Surjective (realInfinitePlaceSignHom w hw) := by
  let eu : w.Completionˣ ≃* ℝˣ :=
    Units.mapEquiv
      (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal
        hw).toMulEquiv
  intro s
  cases hs : (s : SignType) with
  | zero =>
      exact False.elim (s.ne_zero hs)
  | neg =>
      refine ⟨eu.symm (-1), ?_⟩
      apply Units.ext
      simp [realInfinitePlaceSignHom, eu, hs]
  | pos =>
      refine ⟨eu.symm 1, ?_⟩
      apply Units.ext
      simp [realInfinitePlaceSignHom, eu, hs]


end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_IdeleClassPowerLocalUnitQuotient_FinitePlaceCompletionInstances
attribute [-instance] _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Canonical structures on finite completions

This module installs the complete discrete valuation, characteristic-zero,
and finite residue-field structures used by finite-place class-field
arithmetic.
-/

open scoped NumberField ValuativeRel
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type} [Field K] [NumberField K]

/-- A finite completion of a number field has characteristic zero. -/
noncomputable instance finitePlaceAdicCompletion_charZero
    (v₀ : HeightOneSpectrum (𝓞 K)) :
    CharZero (v₀.adicCompletion K) :=
  charZero_of_injective_algebraMap
    (algebraMap K (v₀.adicCompletion K)).injective

end GlobalClassFieldTheory.ClassFieldAxiom

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_ValuationSubringUnits_CyclicValueGroup
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod
attribute [-simp] _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Cyclic value groups and normalized uniformizers

This file supplies the ordered-group and rank-one facts used for actual
multiplicative valuation ranges, together with normalized uniformizer results
for `ℤᵐ⁰`-valued valuations.
-/

noncomputable section

universe u x

open WithZero
open scoped NNReal Valued WithZero

namespace LocalFieldTheory.DiscreteValuationField

namespace WithZeroValuation

variable {R : Type u}
variable {Gamma : Type x} [LinearOrderedCommGroupWithZero Gamma]

open LinearOrderedCommGroup

/-- For a valuation with values in the standard group `ℤᵐ⁰`, an element of
value `exp (-1)` is a uniformizer. -/
theorem isUniformizer_of_valuation_eq_exp_neg_one
    {K : Type u} [Field K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [v.IsRankOneDiscrete] (π : K)
    (hπ : v π = WithZero.exp (-1 : ℤ)) :
    v.IsUniformizer π := by
  rw [_root_.Valuation.IsUniformizer.iff, hπ]
  simpa using
    (congrArg Units.val
      (_root_.Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range
        (v := v) ⟨π, hπ⟩)).symm

/-- A surjective standard `ℤᵐ⁰`-valued valuation has a normalized
uniformizer in its valuation subring. -/
theorem exists_valuationSubring_valuation_eq_exp_neg_one_of_surjective
    {K : Type u} [Field K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    (hv : Function.Surjective v) :
    ∃ π : v.valuationSubring,
      v (π : K) = WithZero.exp (-1 : ℤ) := by
  rcases hv (WithZero.exp (-1 : ℤ)) with ⟨π, hπ⟩
  have hπmem : π ∈ v.valuationSubring := by
    change v π ≤ 1
    rw [hπ]
    change WithZero.exp (-1 : ℤ) ≤ WithZero.exp (0 : ℤ)
    rw [WithZero.exp_le_exp]
    norm_num
  exact ⟨⟨π, hπmem⟩, hπ⟩


end WithZeroValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_Arithmetic
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod
attribute [-simp] _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Arithmetic lemmas for local-field index calculations

This file contains the pure natural-number cancellation steps used after local-field
norm and value-group arguments have produced an lcm divisibility.

It also contains the elementary `p`-adic valuation estimates used in the local-field structure development,
the logarithm and exponential estimates for the convergence and valuation behavior of the
logarithm and exponential series.
-/

namespace LocalFieldTheory.DiscreteValuationField

open Filter

section PadicLogArithmetic

variable {p n : ℕ}

/-- Variant of the logarithmic domination estimate with a fixed real multiple
of the logarithmic term.  This is the form needed after inserting the
ramification index into the valuation of integer denominators. -/
theorem tendsto_nat_succ_mul_const_sub_const_mul_logb_atTop
    {c C : ℝ} (hc : 0 < c) :
    Tendsto
      (fun n : ℕ =>
        ((n + 1 : ℕ) : ℝ) * c -
          C * Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ))
      atTop atTop := by
  have hhalf : 0 < c / 2 := by positivity
  have htend :
      Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hsmall :
      (fun n : ℕ => C * Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ)) =o[atTop]
        (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) := by
    have hlog :
        (fun n : ℕ => Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ)) =o[atTop]
          (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) := by
      simpa [Function.comp_def] using
        (Real.isLittleO_logb_id_atTop (b := (p : ℝ))).comp_tendsto
          htend
    simpa using hlog.const_mul_left C
  have hbound :
      ∀ᶠ n : ℕ in atTop,
        ‖C * Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ)‖ ≤
          (c / 2) * ‖((n + 1 : ℕ) : ℝ)‖ :=
    hsmall.def hhalf
  have hle :
      (fun n : ℕ => (c / 2) * ((n + 1 : ℕ) : ℝ)) ≤ᶠ[atTop]
        (fun n : ℕ =>
          ((n + 1 : ℕ) : ℝ) * c -
            C * Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ)) := by
    filter_upwards [hbound] with n hn
    have hnnonneg : 0 ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hlog_le :
        C * Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ) ≤
          (c / 2) * ((n + 1 : ℕ) : ℝ) := by
      calc
        C * Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ) ≤
            ‖C * Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ)‖ :=
          le_abs_self _
        _ ≤ (c / 2) * ‖((n + 1 : ℕ) : ℝ)‖ := hn
        _ = (c / 2) * ((n + 1 : ℕ) : ℝ) := by
          rw [Real.norm_eq_abs, abs_of_nonneg hnnonneg]
    calc
      (c / 2) * ((n + 1 : ℕ) : ℝ) =
          ((n + 1 : ℕ) : ℝ) * c -
            (c / 2) * ((n + 1 : ℕ) : ℝ) := by
        ring
      _ ≤ ((n + 1 : ℕ) : ℝ) * c -
          C * Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ) :=
        sub_le_sub_left hlog_le (((n + 1 : ℕ) : ℝ) * c)
  have hlin :
      Tendsto (fun n : ℕ => (c / 2) * ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop hhalf htend
  exact tendsto_atTop_mono' atTop hle hlin

/-- Arithmetic estimate at the deep exponential–logarithm threshold:
for `n > 1`, the quotient `v_p(n)/(n-1)` is at most `1/(p-1)`.

This is the exact numerical inequality used later to show that, above the
threshold `1/(p-1)`, the linear term of the logarithm or exponential series
has strictly smaller valuation than every higher term. -/
theorem padicValNat_div_sub_one_le_inv_sub_one
    [Fact p.Prime] (hn : 1 < n) :
    (padicValNat p n : ℚ) / ((n : ℚ) - 1) ≤
      1 / ((p : ℚ) - 1) := by
  let a := padicValNat p n
  have hpNat : Nat.Prime p := Fact.out
  have hp : (1 : ℚ) < p := by
    exact_mod_cast hpNat.one_lt
  have hpden : 0 < (p : ℚ) - 1 := by
    linarith
  have hnden : 0 < (n : ℚ) - 1 := by
    have hnq : (1 : ℚ) < n := by
      exact_mod_cast hn
    linarith
  have hpowNat : p ^ a ≤ n :=
    Nat.le_of_dvd (lt_trans Nat.zero_lt_one hn) pow_padicValNat_dvd
  have hpow : (p : ℚ) ^ a ≤ (n : ℚ) := by
    exact_mod_cast hpowNat
  have hbern :
      (a : ℚ) ≤ (((p : ℚ) ^ a - 1) / ((p : ℚ) - 1)) :=
    Nat.cast_le_pow_sub_div_sub (α := ℚ) (a := (p : ℚ)) hp a
  have hsub :
      ((p : ℚ) ^ a - 1) / ((p : ℚ) - 1) ≤
        ((n : ℚ) - 1) / ((p : ℚ) - 1) :=
    div_le_div_of_nonneg_right (sub_le_sub_right hpow 1) hpden.le
  have hbound :
      (a : ℚ) ≤ ((n : ℚ) - 1) / ((p : ℚ) - 1) :=
    hbern.trans hsub
  calc
    (padicValNat p n : ℚ) / ((n : ℚ) - 1) =
        (a : ℚ) / ((n : ℚ) - 1) := rfl
    _ ≤ (((n : ℚ) - 1) / ((p : ℚ) - 1)) /
        ((n : ℚ) - 1) :=
      div_le_div_of_nonneg_right hbound hnden.le
    _ = 1 / ((p : ℚ) - 1) := by
      field_simp [hnden.ne', hpden.ne']

/-- Ramified-denominator version of
`log_higher_term_integer_valuation_gt`: if the denominator contributes
`e * v_p(n)`, then the sharp comparison threshold is `e/(p-1)`. -/
theorem log_higher_term_integer_valuation_gt_scaled
    [Fact p.Prime] {n e : ℕ} (hn : 2 ≤ n) {m : ℤ}
    (hm : (e : ℚ) / ((p : ℚ) - 1) < (m : ℚ)) :
    m < (n : ℤ) * m - (e : ℤ) * (padicValNat p n : ℤ) := by
  have hquot :=
    padicValNat_div_sub_one_le_inv_sub_one
      (p := p) (n := n) (by omega)
  have hnden : 0 < (n : ℚ) - 1 := by
    have hnq : (1 : ℚ) < n := by
      exact_mod_cast (by omega : 1 < n)
    linarith
  have he_nonneg : 0 ≤ (e : ℚ) := by
    positivity
  have hscaled_div :
      ((e : ℚ) * (padicValNat p n : ℚ)) / ((n : ℚ) - 1) ≤
        (e : ℚ) / ((p : ℚ) - 1) := by
    calc
      ((e : ℚ) * (padicValNat p n : ℚ)) / ((n : ℚ) - 1) =
          (e : ℚ) * ((padicValNat p n : ℚ) / ((n : ℚ) - 1)) := by
        ring
      _ ≤ (e : ℚ) * (1 / ((p : ℚ) - 1)) :=
        mul_le_mul_of_nonneg_left hquot he_nonneg
      _ = (e : ℚ) / ((p : ℚ) - 1) := by
        ring
  have hstrict :
      ((e : ℚ) * (padicValNat p n : ℚ)) / ((n : ℚ) - 1) < (m : ℚ) :=
    lt_of_le_of_lt hscaled_div hm
  have hdenlt :
      (e : ℚ) * (padicValNat p n : ℚ) <
        ((n : ℚ) - 1) * (m : ℚ) := by
    calc
      (e : ℚ) * (padicValNat p n : ℚ) =
          (((e : ℚ) * (padicValNat p n : ℚ)) / ((n : ℚ) - 1)) *
            ((n : ℚ) - 1) := by
        field_simp [hnden.ne']
      _ < (m : ℚ) * ((n : ℚ) - 1) :=
        mul_lt_mul_of_pos_right hstrict hnden
      _ = ((n : ℚ) - 1) * (m : ℚ) := by
        ring
  have hgoal :
      (m : ℚ) <
        (n : ℚ) * (m : ℚ) -
          (e : ℚ) * (padicValNat p n : ℚ) := by
    nlinarith
  have hgoal' :
      (m : ℚ) <
        (((n : ℤ) * m -
          (e : ℤ) * (padicValNat p n : ℤ) : ℤ) : ℚ) := by
    simpa [Int.cast_mul, Int.cast_sub, Int.cast_natCast] using hgoal
  exact_mod_cast hgoal'

end PadicLogArithmetic

end LocalFieldTheory.DiscreteValuationField
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PrincipalUnitPadicAction_PadicReductionContinuous
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Continuity of reduction of p-adic integers

Reduction modulo `p^n` has open kernel and is continuous for the discrete
topology on the quotient. This source has no local-field dependencies.
-/

namespace LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup

/-- The kernel of reduction `Z_p -> ZMod (p^n)` is open. -/
theorem isOpen_ker_padicIntToZModPow
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsOpen
      ((RingHom.ker (PadicInt.toZModPow n : ℤ_[p] →+* ZMod (p ^ n)) :
        Ideal ℤ_[p]) : Set ℤ_[p]) := by
  rw [PadicInt.ker_toZModPow]
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hr : (p : ℝ) ^ (-n : ℤ) ≠ 0 := zpow_ne_zero (-n : ℤ) hp0
  have hball :
      IsOpen (Metric.closedBall (0 : ℤ_[p]) ((p : ℝ) ^ (-n : ℤ))) :=
    IsUltrametricDist.isOpen_closedBall (0 : ℤ_[p]) hr
  have heq :
      ((Ideal.span {(p : ℤ_[p]) ^ n} : Ideal ℤ_[p]) : Set ℤ_[p]) =
        Metric.closedBall (0 : ℤ_[p]) ((p : ℝ) ^ (-n : ℤ)) := by
    ext x
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (PadicInt.norm_le_pow_iff_mem_span_pow x n).symm
  rw [heq]
  exact hball

/-- Reduction of p-adic integers modulo `p^n` is continuous for the
discrete topology on the target. -/
theorem Internal.continuous_padicIntToZModPow
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    @Continuous ℤ_[p] (ZMod (p ^ n))
      (inferInstance : TopologicalSpace ℤ_[p]) ⊥
      (PadicInt.toZModPow n : ℤ_[p] → ZMod (p ^ n)) := by
  let : TopologicalSpace (ZMod (p ^ n)) := ⊥
  let : DiscreteTopology (ZMod (p ^ n)) := ⟨rfl⟩
  apply continuous_of_continuousAt_zero
    (PadicInt.toZModPow n : ℤ_[p] →+* ZMod (p ^ n))
  rw [ContinuousAt, nhds_discrete (ZMod (p ^ n)), map_zero, Filter.tendsto_pure]
  exact (isOpen_ker_padicIntToZModPow p n).mem_nhds
    (RingHom.ker (PadicInt.toZModPow n)).zero_mem

end LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_LogExpSeries_FormalCoreBase_PowerSeriesComposition
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod
attribute [-simp] _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Formal logarithm and exponential composition

This module develops the formal composition identities between Mathlib's
`PowerSeries.log` and `PowerSeries.exp` that are used by the local-field
logarithm and exponential.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace PowerSeries

/-- The alternating geometric series is the formal inverse of `1 + X`. -/
theorem alternating_mul_one_add_X
    (A : Type*) [CommRing A] :
    (PowerSeries.mk fun n : ℕ => (-1 : A) ^ n) *
        (1 + PowerSeries.X : PowerSeries A) = 1 := by
  have h :=
    congrArg (PowerSeries.evalNegHom (A := A))
      (PowerSeries.mk_one_mul_one_sub_eq_one A)
  have hmk' :
      PowerSeries.evalNegHom (PowerSeries.mk (1 : ℕ → A)) =
        PowerSeries.mk fun n : ℕ => (-1 : A) ^ n := by
    ext n
    simp [PowerSeries.evalNegHom, PowerSeries.rescale_mk]
  simpa [hmk', sub_eq_add_neg] using h

/-- `(log A)' * (1 + X) = 1` (compat: the older Mathlib's `derivative_log_mul_one_add_X`). -/
theorem derivative_log_mul_one_add_X
    {A : Type*} [CommRing A] [Algebra ℚ A] :
    PowerSeries.derivative A (PowerSeries.log A) * (1 + PowerSeries.X : PowerSeries A) = 1 := by
  rw [PowerSeries.deriv_log]
  have : (PowerSeries.mk fun n : ℕ => (algebraMap ℚ A) ((-1 : ℚ) ^ n)) =
      PowerSeries.mk fun n : ℕ => (-1 : A) ^ n := by
    ext n
    simp
  rw [this]
  exact alternating_mul_one_add_X A

/-- Compat: the older Mathlib's `constantCoeff_subst_of_constantCoeff_zero`. -/
theorem constantCoeff_subst_of_constantCoeff_zero
    {A : Type*} [CommRing A] {a : PowerSeries A} (ha : PowerSeries.constantCoeff a = 0)
    (f : PowerSeries A) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = PowerSeries.constantCoeff f := by
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha),
    finsum_eq_single _ 0]
  · simp [PowerSeries.coeff_zero_eq_constantCoeff]
  · intro d hd
    have : MvPowerSeries.constantCoeff (a ^ d) = 0 := by
      have h : MvPowerSeries.constantCoeff a = 0 := ha
      rw [map_pow, h, zero_pow hd]
    simp [this]

/-- A torsion-free power series with zero constant coefficient satisfying
`f' * (1 + X) = f` is zero. -/
theorem eq_zero_of_derivative_mul_one_add_X_eq_self
    (A : Type*) [CommRing A] [IsAddTorsionFree A] {f : PowerSeries A}
    (hD :
      PowerSeries.derivative A f * (1 + PowerSeries.X : PowerSeries A) = f)
    (hc : PowerSeries.constantCoeff f = 0) :
    f = 0 := by
  ext n
  induction n with
  | zero =>
      rw [PowerSeries.coeff_zero_eq_constantCoeff, hc]
      simp
  | succ n ih =>
      cases n with
      | zero =>
          have hcoeff := congrArg (PowerSeries.coeff 0) hD
          have hmul :
              PowerSeries.derivative A f *
                  (1 + PowerSeries.X : PowerSeries A) =
                PowerSeries.derivative A f +
                  PowerSeries.derivative A f * PowerSeries.X := by
            ring
          rw [hmul, map_add, PowerSeries.coeff_zero_mul_X,
            add_zero, PowerSeries.coeff_zero_eq_constantCoeff, hc] at hcoeff
          rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
            PowerSeries.coeff_derivative] at hcoeff
          simpa using hcoeff
      | succ n =>
          have hcoeff := congrArg (PowerSeries.coeff (n + 1)) hD
          have hmul :
              PowerSeries.derivative A f *
                  (1 + PowerSeries.X : PowerSeries A) =
                PowerSeries.derivative A f +
                  PowerSeries.derivative A f * PowerSeries.X := by
            ring
          rw [hmul, map_add, PowerSeries.coeff_succ_mul_X,
            PowerSeries.coeff_derivative, PowerSeries.coeff_derivative] at hcoeff
          simp [ih] at hcoeff
          have hzero :
              PowerSeries.coeff (n + 2) f *
                  ((Nat.succ (n + 1) : ℕ) : A) = 0 := by
            simpa using hcoeff
          rw [mul_comm, ← nsmul_eq_mul] at hzero
          simpa using
            (smul_right_inj (Nat.succ_ne_zero (n + 1))).mp
              (by simpa using hzero)

/-- A torsion-free power series with constant coefficient one satisfying
`f' * (1 + X) = f` is `1 + X`. -/
theorem eq_one_add_X_of_derivative_mul_one_add_X_eq_self
    (A : Type*) [CommRing A] [IsAddTorsionFree A] {f : PowerSeries A}
    (hD :
      PowerSeries.derivative A f * (1 + PowerSeries.X : PowerSeries A) = f)
    (hc : PowerSeries.constantCoeff f = 1) :
    f = 1 + PowerSeries.X := by
  have hbase :
      PowerSeries.derivative A (1 + PowerSeries.X : PowerSeries A) *
          (1 + PowerSeries.X : PowerSeries A) =
        (1 + PowerSeries.X : PowerSeries A) := by
    simp
  have hzero :
      PowerSeries.derivative A (f - (1 + PowerSeries.X : PowerSeries A)) *
          (1 + PowerSeries.X : PowerSeries A) =
        f - (1 + PowerSeries.X : PowerSeries A) := by
    rw [map_sub, sub_mul, hD, hbase]
  have hczero :
      PowerSeries.constantCoeff
          (f - (1 + PowerSeries.X : PowerSeries A)) = 0 := by
    simp [hc]
  have h := eq_zero_of_derivative_mul_one_add_X_eq_self
    A hzero hczero
  exact sub_eq_zero.mp h

/-- A power series with derivative one and constant coefficient zero is `X`. -/
theorem eq_X_of_derivative_eq_one
    (A : Type*) [CommRing A] [IsAddTorsionFree A] {f : PowerSeries A}
    (hD : PowerSeries.derivative A f = 1)
    (hc : PowerSeries.constantCoeff f = 0) :
    f = PowerSeries.X := by
  apply PowerSeries.derivative.ext
  · rw [hD, PowerSeries.derivative_X]
  · simp [hc]

/-- Substituting Mathlib's formal logarithm into its exponential yields
`1 + X`. -/
theorem exp_subst_log_eq_one_add_X
    (A : Type*) [CommRing A] [Algebra ℚ A] [IsAddTorsionFree A] :
    PowerSeries.subst (PowerSeries.log A) (PowerSeries.exp A) =
      (1 + PowerSeries.X : PowerSeries A) := by
  let l : PowerSeries A := PowerSeries.log A
  have hl0 : PowerSeries.constantCoeff l = 0 :=
    PowerSeries.constantCoeff_log
  have hl : PowerSeries.HasSubst l := by
    simpa [l] using PowerSeries.HasSubst.log (A := A)
  let f : PowerSeries A := PowerSeries.subst l (PowerSeries.exp A)
  have hD :
      PowerSeries.derivative A f * (1 + PowerSeries.X : PowerSeries A) = f := by
    dsimp [f]
    rw [PowerSeries.derivative_subst hl]
    rw [PowerSeries.derivative_exp]
    calc
      (PowerSeries.subst l (PowerSeries.exp A) *
            PowerSeries.derivative A l) *
          (1 + PowerSeries.X : PowerSeries A) =
        PowerSeries.subst l (PowerSeries.exp A) *
          (PowerSeries.derivative A l *
            (1 + PowerSeries.X : PowerSeries A)) := by
          ring
      _ = PowerSeries.subst l (PowerSeries.exp A) * 1 := by
          rw [show
            PowerSeries.derivative A l *
              (1 + PowerSeries.X : PowerSeries A) = 1 by
              simpa [l] using
                PowerSeries.derivative_log_mul_one_add_X (A := A)]
      _ = PowerSeries.subst l (PowerSeries.exp A) := by
          rw [mul_one]
  have hc : PowerSeries.constantCoeff f = 1 := by
    dsimp [f]
    change MvPowerSeries.constantCoeff
      (PowerSeries.subst l (PowerSeries.exp A)) = 1
    rw [PowerSeries.constantCoeff_subst_of_constantCoeff_zero hl0]
    exact PowerSeries.constantCoeff_exp
  exact
    eq_one_add_X_of_derivative_mul_one_add_X_eq_self
      A hD hc

/-- Substituting `exp - 1` into Mathlib's formal logarithm yields `X`. -/
theorem log_subst_exp_sub_one_eq_X
    (A : Type*) [CommRing A] [Algebra ℚ A] [IsAddTorsionFree A] :
    PowerSeries.subst ((PowerSeries.exp A) - 1) (PowerSeries.log A) =
      (PowerSeries.X : PowerSeries A) := by
  let e : PowerSeries A := PowerSeries.exp A - 1
  have he0 : PowerSeries.constantCoeff e = 0 := by
    simp [e]
  have he : PowerSeries.HasSubst e :=
    PowerSeries.HasSubst.of_constantCoeff_zero' he0
  let l : PowerSeries A := PowerSeries.log A
  let f : PowerSeries A := PowerSeries.subst e l
  have hde : PowerSeries.derivative A e = PowerSeries.exp A := by
    simp [e, PowerSeries.derivative_exp]
  have hsubst_deriv_mul_exp :
      PowerSeries.subst e (PowerSeries.derivative A l) *
          PowerSeries.exp A = 1 := by
    have hlog :
        PowerSeries.derivative A l *
            (1 + PowerSeries.X : PowerSeries A) = 1 := by
      simpa [l] using
        PowerSeries.derivative_log_mul_one_add_X (A := A)
    have hsubst :=
      congrArg (fun q : PowerSeries A => PowerSeries.subst e q) hlog
    have hone : PowerSeries.subst e (1 : PowerSeries A) = 1 := by
      rw [← PowerSeries.coe_substAlgHom he]
      simp
    change PowerSeries.subst e
        (PowerSeries.derivative A l * (1 + PowerSeries.X : PowerSeries A)) =
      PowerSeries.subst e (1 : PowerSeries A) at hsubst
    rw [PowerSeries.subst_mul he, PowerSeries.subst_add he,
      PowerSeries.subst_X he, hone] at hsubst
    have hone_add_e : (1 : PowerSeries A) + e = PowerSeries.exp A := by
      dsimp [e]
      ring
    simpa [hone_add_e] using hsubst
  have hD : PowerSeries.derivative A f = 1 := by
    dsimp [f]
    calc
      PowerSeries.derivative A (PowerSeries.subst e l) =
          PowerSeries.subst e (PowerSeries.derivative A l) *
            PowerSeries.derivative A e := by
        rw [PowerSeries.derivative_subst he]
      _ = PowerSeries.subst e (PowerSeries.derivative A l) *
            PowerSeries.exp A := by
        rw [hde]
      _ = 1 := hsubst_deriv_mul_exp
  have hc : PowerSeries.constantCoeff f = 0 := by
    dsimp [f]
    change MvPowerSeries.constantCoeff (PowerSeries.subst e l) = 0
    rw [PowerSeries.constantCoeff_subst_of_constantCoeff_zero he0]
    exact PowerSeries.constantCoeff_log
  exact eq_X_of_derivative_eq_one A hD hc


end PowerSeries

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_LogExpSeries_FormalCoreBase_ProductArgument
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod
attribute [-simp] _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# The two-variable formal logarithm product argument

This module defines `X + Y + XY`, its logarithmic substitution, and the
support description needed for the formal product formula.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

/-- The polynomial incarnation of the two-variable product argument
`(1 + X) * (1 + Y) - 1 = X + Y + XY`. -/
def formalLogOnePlusProductArgumentPolynomial
    (A : Type*) [CommSemiring A] : MvPolynomial (Fin 2) A :=
  MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2) +
    MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)

/-- Evaluating the polynomial product argument at `(x,y)` gives
`x + y + xy`. -/
@[simp] theorem formalLogOnePlusProductArgumentPolynomial_eval_pair
    (A : Type*) [CommSemiring A] (x y : A) :
    MvPolynomial.eval (fun i : Fin 2 => if i = 0 then x else y)
        (formalLogOnePlusProductArgumentPolynomial A) =
      x + y + x * y := by
  simp [formalLogOnePlusProductArgumentPolynomial]

/-- Establishes the identity `e = 0`. -/
theorem finsupp_fin_two_eq_zero_of_coords_eq_zero
    (e : Fin 2 →₀ ℕ)
    (hleft : e (0 : Fin 2) = 0) (hright : e (1 : Fin 2) = 0) :
    e = 0 := by
  ext i
  fin_cases i <;> simp [hleft, hright]

/-- Establishes the identity `e = Finsupp.single (0 : Fin 2) 1`. -/
theorem finsupp_fin_two_eq_single_left_of_coords_eq
    (e : Fin 2 →₀ ℕ)
    (hleft : e (0 : Fin 2) = 1) (hright : e (1 : Fin 2) = 0) :
    e = Finsupp.single (0 : Fin 2) 1 := by
  ext i
  fin_cases i <;> simp [hleft, hright]

/-- Establishes the identity `e = Finsupp.single (1 : Fin 2) 1`. -/
theorem finsupp_fin_two_eq_single_right_of_coords_eq
    (e : Fin 2 →₀ ℕ)
    (hleft : e (0 : Fin 2) = 0) (hright : e (1 : Fin 2) = 1) :
    e = Finsupp.single (1 : Fin 2) 1 := by
  ext i
  fin_cases i <;> simp [hleft, hright]

/-- Establishes the identity `e = Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1`. -/
theorem finsupp_fin_two_eq_mixed_of_coords_eq_one
    (e : Fin 2 →₀ ℕ)
    (hleft : e (0 : Fin 2) = 1) (hright : e (1 : Fin 2) = 1) :
    e =
      Finsupp.single (0 : Fin 2) 1 +
        Finsupp.single (1 : Fin 2) 1 := by
  ext i
  fin_cases i <;> simp [hleft, hright]


end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_LogExpSeries_FormalCoreBase_ChoicePositions
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod
attribute [-simp] _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Realizing formal-product choices by position sets

This module constructs a basic-factor choice from its mixed and left position
sets and proves the resulting position-count formulas.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

/-- The left basic exponent vector. -/
noncomputable def formalLogOnePlusProductArgumentBasicFactorLeft :
    Fin 2 →₀ ℕ :=
  Finsupp.single (0 : Fin 2) 1

/-- The right basic exponent vector. -/
noncomputable def formalLogOnePlusProductArgumentBasicFactorRight :
    Fin 2 →₀ ℕ :=
  Finsupp.single (1 : Fin 2) 1

/-- The mixed basic exponent vector. -/
noncomputable def formalLogOnePlusProductArgumentBasicFactorMixed :
    Fin 2 →₀ ℕ :=
  Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1

/-- The basic-factor sequence with mixed positions `M`, left positions `L`,
and right factors in every remaining position below `q`. -/
noncomputable def formalLogOnePlusProductArgumentChoiceFromMixedLeft
    (q : ℕ) (M L : Finset ℕ) : ℕ →₀ (Fin 2 →₀ ℕ) :=
  Finsupp.onFinset (Finset.range q)
    (fun i =>
      if i ∈ Finset.range q then
        if i ∈ M then formalLogOnePlusProductArgumentBasicFactorMixed
        else if i ∈ L then formalLogOnePlusProductArgumentBasicFactorLeft
        else formalLogOnePlusProductArgumentBasicFactorRight
      else 0)
    (by
      intro i hi
      by_cases hq : i ∈ Finset.range q
      · exact hq
      · simp [hq] at hi)

/--
Establishes the identity `formalLogOnePlusProductArgumentChoiceFromMixedLeft q M L i = if i ∈ M
then formalLogOnePlusProductArgumentBasicFactorMixed else if i ∈ L then
formalLogOnePlusProductArgumentBasicFactorLeft else
formalLogOnePlusProductArgumentBasicFactorRight`.
-/
@[simp] theorem formalLogOnePlusProductArgumentChoiceFromMixedLeft_apply_of_mem
    {q : ℕ} {M L : Finset ℕ} {i : ℕ} (hi : i ∈ Finset.range q) :
    formalLogOnePlusProductArgumentChoiceFromMixedLeft q M L i =
      if i ∈ M then formalLogOnePlusProductArgumentBasicFactorMixed
      else if i ∈ L then formalLogOnePlusProductArgumentBasicFactorLeft
      else formalLogOnePlusProductArgumentBasicFactorRight := by
  have hlt : i < q := Finset.mem_range.mp hi
  simp [formalLogOnePlusProductArgumentChoiceFromMixedLeft, hlt]

/-- Establishes the identity `formalLogOnePlusProductArgumentChoiceFromMixedLeft q M L i = 0`. -/
@[simp] theorem formalLogOnePlusProductArgumentChoiceFromMixedLeft_apply_of_not_mem
    {q : ℕ} {M L : Finset ℕ} {i : ℕ} (hi : i ∉ Finset.range q) :
    formalLogOnePlusProductArgumentChoiceFromMixedLeft q M L i = 0 := by
  have hle : q ≤ i := by simpa [Finset.mem_range] using hi
  simp [formalLogOnePlusProductArgumentChoiceFromMixedLeft, hle]


end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_LogExpSeries_FormalCore
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod
attribute [-simp] _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

open Filter
open Polynomial
open scoped Topology
open scoped PowerSeries.WithPiTopology

/-!
# Choice-count combinatorics for the formal logarithm product

This module completes the formal logarithm core by identifying the basic-factor
choices with pairs of finite position sets and evaluating their cardinality.
The formal-series identities and the underlying position calculus live in
`FormalCoreBase`.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

/-- Defines `formalLogOnePlusProductArgumentMixedLeftChoices`. -/
noncomputable def formalLogOnePlusProductArgumentMixedLeftChoices
    (q a b : ℕ) : Finset (Σ _ : Finset ℕ, Finset ℕ) :=
  ((Finset.range q).powersetCard (a + b - q)).sigma fun M =>
    ((Finset.range q \ M).powersetCard (q - b))

/--
Establishes the identity `(formalLogOnePlusProductArgumentMixedLeftChoices q a b).card =
Nat.choose q (a + b - q) * Nat.choose (q - (a + b - q)) (q - b)`.
-/
theorem formalLogOnePlusProductArgumentMixedLeftChoices_card
    (q a b : ℕ) :
    (formalLogOnePlusProductArgumentMixedLeftChoices q a b).card =
      Nat.choose q (a + b - q) *
        Nat.choose (q - (a + b - q)) (q - b) := by
  classical
  rw [formalLogOnePlusProductArgumentMixedLeftChoices, Finset.card_sigma]
  calc
    (∑ M ∈ (Finset.range q).powersetCard (a + b - q),
        ((Finset.range q \ M).powersetCard (q - b)).card)
        = ∑ M ∈ (Finset.range q).powersetCard (a + b - q),
            Nat.choose (q - (a + b - q)) (q - b) := by
          apply Finset.sum_congr rfl
          intro M hM
          rw [Finset.card_powersetCard]
          have hsub : M ⊆ Finset.range q :=
            (Finset.mem_powersetCard.mp hM).1
          have hcard : M.card = a + b - q :=
            (Finset.mem_powersetCard.mp hM).2
          rw [Finset.card_sdiff_of_subset hsub, Finset.card_range, hcard]
    _ = Nat.choose q (a + b - q) *
          Nat.choose (q - (a + b - q)) (q - b) := by
          rw [Finset.sum_const]
          simp [Finset.card_powersetCard]

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_LogExpSeries_FormalProduct
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod
attribute [-simp] _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false
/-!
Proves the formal combinatorial identities behind additivity of the logarithm on products of
principal units.
-/

open Filter
open Polynomial
open scoped Topology
open scoped PowerSeries.WithPiTopology
noncomputable section

attribute [local instance] Classical.propDecidable

universe u

open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

variable {K : Type u} [Field K]

/--
Establishes the identity `MvPowerSeries.coeff e ((MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin
2) A) ^ d) = if e = Finsupp.single (0 : Fin 2) d then 1 else 0`.
-/
theorem formalLogOnePlusLeftVariable_pow_coeff
    (A : Type*) [CommRing A] (e : Fin 2 →₀ ℕ) (d : ℕ) :
    MvPowerSeries.coeff e
        ((MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) A) ^ d) =
      if e = Finsupp.single (0 : Fin 2) d then 1 else 0 := by
  simpa using
    MvPowerSeries.coeff_X_pow (R := A) e (0 : Fin 2) d

/-- Establishes the identity `e = Finsupp.single (0 : Fin 2) (e (0 : Fin 2))`. -/
theorem finsupp_fin_two_eq_single_left_of_right_eq_zero
    (e : Fin 2 →₀ ℕ) (he : e (1 : Fin 2) = 0) :
    e = Finsupp.single (0 : Fin 2) (e (0 : Fin 2)) := by
  ext i
  fin_cases i <;> simp [he]

/-- Establishes the identity `Finsupp.degree e = e (0 : Fin 2) + e (1 : Fin 2)`. -/
theorem finsupp_fin_two_degree_eq (e : Fin 2 →₀ ℕ) :
    Finsupp.degree e = e (0 : Fin 2) + e (1 : Fin 2) := by
  classical
  have huniv :
      (Finset.univ : Finset (Fin 2)) =
        {0, 1} := by
    ext i
    fin_cases i <;> simp
  rw [Finsupp.degree_eq_sum, huniv]
  simp

/-- Establishes the inequality `e ≠ Finsupp.single (0 : Fin 2) d`. -/
theorem finsupp_fin_two_ne_single_left_of_right_pos
    (e : Fin 2 →₀ ℕ) (hpos : 0 < e (1 : Fin 2)) (d : ℕ) :
    e ≠ Finsupp.single (0 : Fin 2) d := by
  intro h
  have hcoord : e (1 : Fin 2) = 0 := by
    simp [h]
  exact (Nat.ne_of_gt hpos) hcoord

/-- Establishes the inequality `e ≠ Finsupp.single (1 : Fin 2) d`. -/
theorem finsupp_fin_two_ne_single_right_of_left_pos
    (e : Fin 2 →₀ ℕ) (hpos : 0 < e (0 : Fin 2)) (d : ℕ) :
    e ≠ Finsupp.single (1 : Fin 2) d := by
  intro h
  have hcoord : e (0 : Fin 2) = 0 := by
    simp [h]
  exact (Nat.ne_of_gt hpos) hcoord

/--
Establishes the identity `(∑ q ∈ (Finset.range (a + b + 1)).filter (fun q => a ≤ q ∧ b ≤ q), F q)
= ∑ m ∈ (Finset.range (a + 1)).filter (fun m => m ≤ b), F (a + b - m)`.
-/
theorem sum_range_add_filter_coord_le_reindex
    {R : Type*} [AddCommMonoid R] (a b : ℕ) (F : ℕ → R) :
    (∑ q ∈ (Finset.range (a + b + 1)).filter (fun q => a ≤ q ∧ b ≤ q),
      F q) =
      ∑ m ∈ (Finset.range (a + 1)).filter (fun m => m ≤ b),
        F (a + b - m) := by
  refine Finset.sum_bij'
    (fun q _ => a + b - q)
    (fun m _ => a + b - m)
    ?_ ?_ ?_ ?_ ?_
  · intro q hq
    rw [Finset.mem_filter] at hq ⊢
    constructor
    · rw [Finset.mem_range]
      omega
    · omega
  · intro m hm
    rw [Finset.mem_filter] at hm ⊢
    have hmle_a : m ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm.1)
    have hmle_b : m ≤ b := hm.2
    have hleftRewrite : a + b - m = a + (b - m) := by
      exact Nat.add_sub_assoc hmle_b a
    have hrightRewrite : a + b - m = b + (a - m) := by
      rw [Nat.add_comm a b]
      exact Nat.add_sub_assoc hmle_a b
    constructor
    · rw [Finset.mem_range]
      omega
    · constructor
      · rw [hleftRewrite]
        omega
      · rw [hrightRewrite]
        omega
  · intro q hq
    rw [Finset.mem_filter] at hq
    have hqle : q ≤ a + b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq.1)
    exact Nat.sub_sub_self hqle
  · intro m hm
    rw [Finset.mem_filter] at hm
    have hmle_a : m ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm.1)
    have hmle : m ≤ a + b := by omega
    exact Nat.sub_sub_self hmle
  · intro q hq
    rw [Finset.mem_filter] at hq
    have hqle : q ≤ a + b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq.1)
    simp [Nat.sub_sub_self hqle]

/--
Establishes the identity `(∑ m ∈ Finset.range (a + 1), ((-1 : ℚ) ^ m) * (Nat.choose a m : ℚ) *
(Nat.choose (a + b - 1 - m) (a - 1) : ℚ)) = 0`.
-/
theorem formalLogOnePlusProduct_alternating_sum_choose_eq_zero
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (∑ m ∈ Finset.range (a + 1),
      ((-1 : ℚ) ^ m) * (Nat.choose a m : ℚ) *
        (Nat.choose (a + b - 1 - m) (a - 1) : ℚ)) = 0 := by
  let P : ℚ[X] := X + 1
  have hcoeff :
      (∑ m ∈ Finset.range (a + 1),
        ((-1 : ℚ) ^ m) * (Nat.choose a m : ℚ) *
          (Nat.choose (a + b - 1 - m) (a - 1) : ℚ)) =
        Polynomial.coeff
          (∑ m ∈ Finset.range (a + 1),
            C (((-1 : ℚ) ^ m) * (Nat.choose a m : ℚ)) *
              P ^ (a + b - 1 - m)) (a - 1) := by
    have hsumcoeff :
        Polynomial.coeff
          (∑ m ∈ Finset.range (a + 1),
            C (((-1 : ℚ) ^ m) * (Nat.choose a m : ℚ)) *
              P ^ (a + b - 1 - m)) (a - 1) =
          ∑ m ∈ Finset.range (a + 1),
            Polynomial.coeff
              (C (((-1 : ℚ) ^ m) * (Nat.choose a m : ℚ)) *
                P ^ (a + b - 1 - m)) (a - 1) := by
      simp
    rw [hsumcoeff]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Polynomial.coeff_C_mul]
    have hpowcoeff :
        Polynomial.coeff (P ^ (a + b - 1 - m)) (a - 1) =
          (Nat.choose (a + b - 1 - m) (a - 1) : ℚ) := by
      dsimp [P]
      rw [Polynomial.coeff_X_add_one_pow]
    rw [hpowcoeff]
  rw [hcoeff]
  have hpoly :
      (∑ m ∈ Finset.range (a + 1),
        C (((-1 : ℚ) ^ m) * (Nat.choose a m : ℚ)) *
          P ^ (a + b - 1 - m)) =
        X ^ a * P ^ (b - 1) := by
    calc
      (∑ m ∈ Finset.range (a + 1),
        C (((-1 : ℚ) ^ m) * (Nat.choose a m : ℚ)) *
          P ^ (a + b - 1 - m))
          =
        ∑ k ∈ Finset.range (a + 1),
          C (((-1 : ℚ) ^ (a - k)) * (Nat.choose a (a - k) : ℚ)) *
            P ^ (a + b - 1 - (a - k)) := by
            simpa using
              (Finset.sum_range_reflect
                (fun m =>
                  C (((-1 : ℚ) ^ m) * (Nat.choose a m : ℚ)) *
                    P ^ (a + b - 1 - m)) (a + 1)).symm
      _ =
        ∑ k ∈ Finset.range (a + 1),
          C (((-1 : ℚ) ^ (k + a)) * (Nat.choose a k : ℚ)) *
            P ^ (k + (b - 1)) := by
            apply Finset.sum_congr rfl
            intro k hk
            have hk_le : k ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
            have hchoose : Nat.choose a (a - k) = Nat.choose a k :=
              Nat.choose_symm hk_le
            have hpow : ((-1 : ℚ) ^ (a - k)) = (-1 : ℚ) ^ (k + a) := by
              have hadd : k + a = a - k + 2 * k := by omega
              rw [hadd, pow_add, pow_mul]
              simp [pow_two]
            have hexp : a + b - 1 - (a - k) = k + (b - 1) := by omega
            rw [hchoose, hpow, hexp]
      _ =
        (∑ k ∈ Finset.range (a + 1),
          C (((-1 : ℚ) ^ (k + a)) * (Nat.choose a k : ℚ)) *
            P ^ k) * P ^ (b - 1) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro k hk
            rw [pow_add]
            ring
      _ = (P - 1) ^ a * P ^ (b - 1) := by
            rw [sub_pow]
            simp [P, mul_assoc, mul_comm]
      _ = X ^ a * P ^ (b - 1) := by
            simp [P]
  rw [hpoly]
  have hdiv : X ^ a ∣ (X ^ a * P ^ (b - 1) : ℚ[X]) := ⟨P ^ (b - 1), rfl⟩
  exact
    (Polynomial.X_pow_dvd_iff.mp hdiv (a - 1)
      (Nat.sub_lt ha Nat.one_pos))

/--
Establishes the identity `(∑ m ∈ (Finset.range (a + 1)).filter (fun m => m ≤ b), ((-1 : ℚ) ^ m) *
(Nat.choose a m : ℚ) * (Nat.choose (a + b - 1 - m) (a - 1) : ℚ)) = 0`.
-/
theorem formalLogOnePlusProduct_alternating_sum_choose_filter_eq_zero
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (∑ m ∈ (Finset.range (a + 1)).filter (fun m => m ≤ b),
      ((-1 : ℚ) ^ m) * (Nat.choose a m : ℚ) *
        (Nat.choose (a + b - 1 - m) (a - 1) : ℚ)) = 0 := by
  rw [← formalLogOnePlusProduct_alternating_sum_choose_eq_zero a b ha hb]
  exact
    (Finset.sum_subset (Finset.filter_subset _ _) (fun m hm hnot => by
      have hle_a : m ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      have hlt_b : b < m := Nat.lt_of_not_ge (by
        intro hmb
        exact hnot (Finset.mem_filter.mpr ⟨hm, hmb⟩))
      have hchooseZero :
          Nat.choose (a + b - 1 - m) (a - 1) = 0 := by
        apply Nat.choose_eq_zero_of_lt
        omega
      change
        ((-1 : ℚ) ^ m) * (Nat.choose a m : ℚ) *
          (Nat.choose (a + b - 1 - m) (a - 1) : ℚ) = 0
      rw [hchooseZero]
      simp))

/--
After the substitution `q = a + b - m`, the mixed logarithmic coefficient rewrites as the
corresponding alternating binomial term.
-/
theorem formalLogOnePlusProduct_rational_mixed_reindexed_term
    (a b m : ℕ) (ha : 0 < a) (hmle_a : m ≤ a) (hmle_b : m ≤ b) :
    let q := a + b - m
    (a : ℚ) *
        (((-1 : ℚ) ^ (q - 1) / (q : ℚ)) *
          ((Nat.choose q m * Nat.choose (q - m) (q - b) : ℕ) : ℚ)) =
      ((-1 : ℚ) ^ (a + b - 1)) *
        (((-1 : ℚ) ^ m) * (Nat.choose a m : ℚ) *
          (Nat.choose (a + b - 1 - m) (a - 1) : ℚ)) := by
  intro q
  subst q
  have hqpos : 0 < a + b - m := by omega
  have hq_ne : ((a + b - m : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hqpos)
  have hq_sub_b : a + b - m - b = a - m := by omega
  have hq_pred : a + b - m - 1 = a + b - 1 - m := by omega
  have hprodNat :
      Nat.choose (a + b - m) m *
          Nat.choose (a + b - m - m) (a + b - m - b) =
        Nat.choose (a + b - m) a * Nat.choose a m := by
    rw [hq_sub_b]
    exact
      (Nat.choose_mul (n := a + b - m) (k := a) (s := m) hmle_a).symm
  have hsuccNat :
      (a + b - m) * Nat.choose (a + b - m - 1) (a - 1) =
        Nat.choose (a + b - m) a * a := by
    calc
      (a + b - m) * Nat.choose (a + b - m - 1) (a - 1)
          =
        ((a + b - m - 1) + 1) *
          Nat.choose (a + b - m - 1) (a - 1) := by
            rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hqpos)]
      _ =
        Nat.choose ((a + b - m - 1) + 1) ((a - 1) + 1) *
          ((a - 1) + 1) := by
            exact Nat.add_one_mul_choose_eq (a + b - m - 1) (a - 1)
      _ = Nat.choose (a + b - m) a * a := by
            rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hqpos),
              Nat.sub_add_cancel (Nat.succ_le_of_lt ha)]
  have hsuccQ :
      ((a + b - m : ℕ) : ℚ) *
          (Nat.choose (a + b - m - 1) (a - 1) : ℚ) =
        (Nat.choose (a + b - m) a : ℚ) * (a : ℚ) := by
    exact_mod_cast hsuccNat
  have hsuccQ' :
      ((a + b - m : ℕ) : ℚ) *
          (Nat.choose (a + b - 1 - m) (a - 1) : ℚ) =
        (Nat.choose (a + b - m) a : ℚ) * (a : ℚ) := by
    simpa [hq_pred] using hsuccQ
  have hsign :
      (-1 : ℚ) ^ (a + b - m - 1) =
        (-1 : ℚ) ^ (a + b - 1) * (-1 : ℚ) ^ m := by
    calc
      (-1 : ℚ) ^ (a + b - m - 1)
          = (-1 : ℚ) ^ ((a + b - 1) + m) := by
            have hadd : (a + b - 1) + m = a + b - m - 1 + 2 * m := by
              omega
            rw [hadd, pow_add, pow_mul]
            simp [pow_two]
      _ = (-1 : ℚ) ^ (a + b - 1) * (-1 : ℚ) ^ m := by
            rw [pow_add]
  rw [hprodNat, hsign]
  field_simp [hq_ne]
  rw [Nat.cast_mul]
  calc
    (a : ℚ) *
        ((Nat.choose (a + b - m) a : ℚ) * (Nat.choose a m : ℚ))
        =
      ((Nat.choose (a + b - m) a : ℚ) * (a : ℚ)) *
        (Nat.choose a m : ℚ) := by
          ring
    _ =
      (((a + b - m : ℕ) : ℚ) *
          (Nat.choose (a + b - 1 - m) (a - 1) : ℚ)) *
        (Nat.choose a m : ℚ) := by
          rw [← hsuccQ']
    _ =
      ((a + b - m : ℕ) : ℚ) * (Nat.choose a m : ℚ) *
        (Nat.choose (a + b - 1 - m) (a - 1) : ℚ) := by
          ring

/--
Establishes the identity `(∑ q ∈ (Finset.range (a + b + 1)).filter (fun q : ℕ => a ≤ q ∧ b ≤ q),
(((-1 : ℚ) ^ (q - 1) / (q : ℚ)) * ((Nat.choose q (a + b - q) * Nat.choose (q - (a + b - q)) (q -
b) : ℕ) : ℚ))) = 0`.
-/
theorem formalLogOnePlusProduct_rational_mixed_sum_eq_zero
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (∑ q ∈
      (Finset.range (a + b + 1)).filter (fun q : ℕ => a ≤ q ∧ b ≤ q),
      (((-1 : ℚ) ^ (q - 1) / (q : ℚ)) *
        ((Nat.choose q (a + b - q) *
          Nat.choose (q - (a + b - q)) (q - b) : ℕ) : ℚ))) = 0 := by
  let F : ℕ → ℚ := fun q =>
    (((-1 : ℚ) ^ (q - 1) / (q : ℚ)) *
      ((Nat.choose q (a + b - q) *
        Nat.choose (q - (a + b - q)) (q - b) : ℕ) : ℚ))
  change
    (∑ q ∈
      (Finset.range (a + b + 1)).filter (fun q : ℕ => a ≤ q ∧ b ≤ q),
      F q) = 0
  rw [sum_range_add_filter_coord_le_reindex a b F]
  have haQ : (a : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt ha)
  apply (mul_eq_zero.mp ?_).resolve_left haQ
  calc
    (a : ℚ) *
        (∑ m ∈ (Finset.range (a + 1)).filter (fun m => m ≤ b),
          F (a + b - m))
        =
      ∑ m ∈ (Finset.range (a + 1)).filter (fun m => m ≤ b),
        (a : ℚ) * F (a + b - m) := by
          rw [Finset.mul_sum]
    _ =
      ∑ m ∈ (Finset.range (a + 1)).filter (fun m => m ≤ b),
        ((-1 : ℚ) ^ (a + b - 1)) *
          (((-1 : ℚ) ^ m) * (Nat.choose a m : ℚ) *
            (Nat.choose (a + b - 1 - m) (a - 1) : ℚ)) := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [Finset.mem_filter] at hm
          have hmle_a : m ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm.1)
          have hmle_b : m ≤ b := hm.2
          have hmle_sum : m ≤ a + b := by omega
          have hsub : a + b - (a + b - m) = m := Nat.sub_sub_self hmle_sum
          change
            (a : ℚ) *
                (((-1 : ℚ) ^ (a + b - m - 1) /
                    ((a + b - m : ℕ) : ℚ)) *
                  ((Nat.choose (a + b - m) (a + b - (a + b - m)) *
                    Nat.choose
                      (a + b - m - (a + b - (a + b - m)))
                      (a + b - m - b) : ℕ) : ℚ)) =
              ((-1 : ℚ) ^ (a + b - 1)) *
                (((-1 : ℚ) ^ m) * (Nat.choose a m : ℚ) *
                  (Nat.choose (a + b - 1 - m) (a - 1) : ℚ))
          rw [hsub]
          exact formalLogOnePlusProduct_rational_mixed_reindexed_term
            a b m ha hmle_a hmle_b
    _ =
      ((-1 : ℚ) ^ (a + b - 1)) *
        (∑ m ∈ (Finset.range (a + 1)).filter (fun m => m ≤ b),
          ((-1 : ℚ) ^ m) * (Nat.choose a m : ℚ) *
            (Nat.choose (a + b - 1 - m) (a - 1) : ℚ)) := by
          rw [Finset.mul_sum]
    _ = 0 := by
          rw [formalLogOnePlusProduct_alternating_sum_choose_filter_eq_zero
            a b ha hb]
          simp

/-- The value of the monomial indexed by a finitely supported exponent at a
chosen evaluation point. -/
noncomputable def mvPowerSeriesMonomialValue
    {σ : Type*} {A : Type*} [CommMonoid A]
    (a : σ → A) (d : σ →₀ ℕ) : A :=
  d.prod fun s e => a s ^ e

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_LogExpSeries_SeriesTerms
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

variable {K : Type u} [Field K]

/-! ### Exponential-series terms -/

/-- The product of two elements of valuation strictly below one again has
valuation strictly below one. -/
theorem valuation_mul_lt_one_of_lt_one
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : _root_.Valuation K Γ₀) {x y : K}
    (hx : v x < 1) (hy : v y < 1) :
    v (x * y) < 1 := by
  rw [v.map_mul]
  exact _root_.Left.mul_lt_one' hx hy

/-- The logarithm product argument `(1+x)(1+y)-1 = x+y+xy` stays in the
open unit ball of a valuation. -/
theorem valuation_log_mul_argument_lt_one_of_lt_one
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : _root_.Valuation K Γ₀) {x y : K}
    (hx : v x < 1) (hy : v y < 1) :
    v (x + y + x * y) < 1 := by
  have hxy : v (x * y) < 1 :=
    valuation_mul_lt_one_of_lt_one v hx hy
  have hsum_le : v (x + y) ≤ max (v x) (v y) :=
    map_add_le_max v x y
  have hsum_lt : v (x + y) < 1 :=
    lt_of_le_of_lt hsum_le (max_lt hx hy)
  have htotal_le : v ((x + y) + x * y) ≤ max (v (x + y)) (v (x * y)) :=
    map_add_le_max v (x + y) (x * y)
  exact lt_of_le_of_lt htotal_le (max_lt hsum_lt hxy)

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_LogExpAdditivity
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod
attribute [-simp] _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

variable {K : Type u} [Field K]

/-- Natural-number coefficients have valuation at most one under a scaled
`p`-adic denominator formula. -/
theorem valuation_natCast_le_one_ofWithZeroValuation_scaled
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} (e : ℕ)
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (m : ℕ) :
    v (m : K) ≤ 1 := by
  cases m with
  | zero => simp
  | succ n =>
      rw [hnval n]
      calc
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))) ≤
            WithZero.exp (0 : ℤ) :=
          WithZero.exp_le_exp.mpr (by
            apply neg_nonpos.mpr
            exact mul_nonneg (Int.natCast_nonneg e)
              (Int.natCast_nonneg (padicValNat p (n + 1))))
        _ = 1 := WithZero.exp_zero

/-- Evaluation of a two-variable monomial at `(x,y)`. -/
theorem mvPowerSeriesMonomialValue_pair
    (x y : K) (d : Fin 2 →₀ ℕ) :
    mvPowerSeriesMonomialValue
        (fun i : Fin 2 => if i = 0 then x else y) d =
      x ^ d 0 * y ^ d 1 := by
  rw [mvPowerSeriesMonomialValue, Finsupp.prod_fintype]
  · rw [Fin.prod_univ_two]
    simp
  · intro i
    simp

/-- A monomial occurring in `(X + Y + XY)^q`, evaluated in the open unit ball,
is no larger than the larger of the two pure degree-`q` monomials. -/
theorem valuation_mvPowerSeriesMonomialValue_pair_le_max_pow
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {x y : K}
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hvy : v y < (1 : WithZero (Multiplicative ℤ)))
    (q : ℕ) (d : Fin 2 →₀ ℕ) (hq : q ≤ d 0 + d 1) :
    v (mvPowerSeriesMonomialValue
        (fun i : Fin 2 => if i = 0 then x else y) d) ≤
      max (v x ^ q) (v y ^ q) := by
  rw [mvPowerSeriesMonomialValue_pair, v.map_mul, v.map_pow, v.map_pow]
  let r := max (v x) (v y)
  have hxr : v x ≤ r := le_max_left _ _
  have hyr : v y ≤ r := le_max_right _ _
  have hr : r ≤ 1 := max_le (le_of_lt hvx) (le_of_lt hvy)
  have hprod : v x ^ d 0 * v y ^ d 1 ≤ r ^ (d 0 + d 1) := by
    calc
      v x ^ d 0 * v y ^ d 1 ≤ r ^ d 0 * r ^ d 1 :=
        mul_le_mul (pow_le_pow_left' hxr _) (pow_le_pow_left' hyr _)
          (by simp) (by simp)
      _ = r ^ (d 0 + d 1) := by rw [pow_add]
  have hpow : r ^ (d 0 + d 1) ≤ r ^ q :=
    pow_le_pow_of_le_one (by exact bot_le) hr hq
  calc
    v x ^ d 0 * v y ^ d 1 ≤ r ^ (d 0 + d 1) := hprod
    _ ≤ r ^ q := hpow
    _ = max (v x ^ q) (v y ^ q) := by
      by_cases hxy : v x ≤ v y
      · simp [r, max_eq_right hxy, pow_le_pow_left' hxy]
      · have hyx : v y ≤ v x := le_of_not_ge hxy
        simp [r, max_eq_left hyx, pow_le_pow_left' hyx]

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_LogExpComposition
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod
attribute [-simp] _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- A convergent one-variable power series may be raised to a natural power
by taking its nonarchimedean Cauchy product. -/
theorem hasSum_powerSeries_pow_coeff_mul_pow
    [UniformSpace K] [IsUniformAddGroup K] [T3Space K]
    [NonarchimedeanRing K]
    (g : PowerSeries K) (x y : K)
    (hgy : HasSum (fun d : ℕ => PowerSeries.coeff d g * x ^ d) y)
    (q : ℕ) :
    HasSum (fun d : ℕ => PowerSeries.coeff d (g ^ q) * x ^ d) (y ^ q) := by
  induction q with
  | zero =>
      have hsingle :
          HasSum (fun d : ℕ => if d = 0 then (1 : K) else 0) 1 := by
        apply hasSum_single 0
        intro d hd
        simp [hd]
      have hsingle' :
          HasSum (fun d : ℕ => PowerSeries.coeff d (1 : PowerSeries K) * x ^ d) 1 :=
        hsingle.congr_fun fun d => by
          by_cases hd : d = 0
          · subst d
            simp
          · simp [PowerSeries.coeff_one, hd]
      simpa only [pow_zero] using hsingle'
  | succ q ih =>
      have hprod := ih.mul_of_nonarchimedean hgy
      have hsigma :
          HasSum
            (fun nd : Sigma fun d : ℕ => ↑(Finset.HasAntidiagonal.antidiagonal d) =>
              (PowerSeries.coeff nd.2.1.1 (g ^ q) * x ^ nd.2.1.1) *
                (PowerSeries.coeff nd.2.1.2 g * x ^ nd.2.1.2))
            (y ^ q * y) := by
        simpa [Function.comp_def] using
          (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff).2 hprod
      have hsumCauchy :
          HasSum
            (fun d : ℕ =>
              ∑ ij : ↑(Finset.HasAntidiagonal.antidiagonal d),
                (PowerSeries.coeff ij.1.1 (g ^ q) * x ^ ij.1.1) *
                  (PowerSeries.coeff ij.1.2 g * x ^ ij.1.2))
            (y ^ q * y) :=
        hsigma.sigma fun d => hasSum_fintype _
      rw [show g ^ (q + 1) = g ^ q * g by rw [pow_succ],
        show y ^ (q + 1) = y ^ q * y by rw [pow_succ]]
      refine hsumCauchy.congr_fun ?_
      intro d
      rw [PowerSeries.coeff_mul, Finset.sum_mul]
      rw [← Finset.sum_attach, Finset.attach_eq_univ]
      apply Finset.sum_congr rfl
      intro ij _
      have hijsum : ij.1.1 + ij.1.2 = d :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp ij.2
      have hpow : x ^ d = x ^ ij.1.1 * x ^ ij.1.2 := by
        calc
          x ^ d = x ^ (ij.1.1 + ij.1.2) :=
            congrArg (fun n : ℕ => x ^ n) hijsum.symm
          _ = x ^ ij.1.1 * x ^ ij.1.2 := pow_add _ _ _
      rw [hpow]
      ring

/-- If every evaluated coefficient of a series is at most `r`, then every
evaluated coefficient of its `q`-th power is at most `r^q`. -/
theorem valuation_powerSeries_pow_coeff_mul_pow_le
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    (g : PowerSeries K) (x : K) (r : WithZero (Multiplicative ℤ))
    (hcoeff : ∀ d : ℕ, v (PowerSeries.coeff d g * x ^ d) ≤ r)
    (q d : ℕ) :
    v (PowerSeries.coeff d (g ^ q) * x ^ d) ≤ r ^ q := by
  induction q generalizing d with
  | zero =>
      by_cases hd : d = 0
      · subst d
        simp
      · simp [PowerSeries.coeff_one, hd]
  | succ q ih =>
      rw [pow_succ, PowerSeries.coeff_mul, Finset.sum_mul]
      apply v.map_sum_le
      intro ij hij
      have hijsum : ij.1 + ij.2 = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      have heq :
          (PowerSeries.coeff ij.1 (g ^ q) * PowerSeries.coeff ij.2 g) * x ^ d =
            (PowerSeries.coeff ij.1 (g ^ q) * x ^ ij.1) *
              (PowerSeries.coeff ij.2 g * x ^ ij.2) := by
        rw [← hijsum, pow_add]
        ring
      rw [heq, v.map_mul, pow_succ]
      exact mul_le_mul (ih ij.1) (hcoeff ij.2) (by simp) (by simp)

/-- The valuation of a term in the expanded substitution is bounded by the
corresponding outer-series term. -/
theorem valuation_powerSeries_subst_sigmaTerm_le_outerTerm
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    (f g : PowerSeries K) (x : K)
    (hcoeff : ∀ d : ℕ,
      v (PowerSeries.coeff d g * x ^ d) ≤ v x)
    (q d : ℕ) :
    v (PowerSeries.coeff q f * PowerSeries.coeff d (g ^ q) * x ^ d) ≤
      v (PowerSeries.coeff q f * x ^ q) := by
  have hpow :=
    valuation_powerSeries_pow_coeff_mul_pow_le
      v g x (v x) hcoeff q d
  calc
    v (PowerSeries.coeff q f * PowerSeries.coeff d (g ^ q) * x ^ d) =
        v (PowerSeries.coeff q f) *
          v (PowerSeries.coeff d (g ^ q) * x ^ d) := by
      rw [mul_assoc, v.map_mul]
    _ ≤ v (PowerSeries.coeff q f) * (v x) ^ q :=
      by gcongr
    _ = v (PowerSeries.coeff q f * x ^ q) := by
      rw [v.map_mul, v.map_pow]

/-- The doubly indexed family expanding `f(g(X))` is unconditionally
summable.  Large outer degrees are controlled uniformly by the convergent
evaluation of `f` at `x`; the finitely many remaining outer degrees are
controlled by the convergent Cauchy powers of `g`. -/
theorem summable_powerSeries_subst_sigma_of_outer_summable
    [Valued K (WithZero (Multiplicative ℤ))] [CompleteSpace K]
    [NonarchimedeanRing K]
    (f g : PowerSeries K) (x y : K)
    (hgy : HasSum (fun d : ℕ => PowerSeries.coeff d g * x ^ d) y)
    (houter : Summable (fun q : ℕ => PowerSeries.coeff q f * x ^ q))
    (hcoeff : ∀ d : ℕ,
      Valued.v (PowerSeries.coeff d g * x ^ d) ≤ Valued.v x) :
    Summable
      (fun qd : Sigma fun _ : ℕ => ℕ =>
        PowerSeries.coeff qd.1 f *
          PowerSeries.coeff qd.2 (g ^ qd.1) * x ^ qd.2) := by
  let term : (Sigma fun _ : ℕ => ℕ) → K := fun qd =>
    PowerSeries.coeff qd.1 f *
      PowerSeries.coeff qd.2 (g ^ qd.1) * x ^ qd.2
  let outerTerm : ℕ → K := fun q => PowerSeries.coeff q f * x ^ q
  change Summable term
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero]
  rw [tendsto_def]
  intro s hs
  have hrepr := Valued.mem_nhds_zero.mp hs
  let γ := Classical.choose hrepr
  have hγ := Classical.choose_spec hrepr
  have hball :
      {z : K |
        Valued.v z < MonoidWithZeroHom.ValueGroup₀.embedding γ.1} ∈ nhds (0 : K) := by
    apply Valued.mem_nhds_zero.mpr
    exact ⟨γ, by
      intro z hz
      change Valued.v.restrict z < γ.1 at hz
      rw [Valuation.restrict_lt_iff_lt_embedding] at hz
      exact hz⟩
  have houterZero : Tendsto outerTerm cofinite (nhds (0 : K)) := by
    simpa [outerTerm] using houter.tendsto_cofinite_zero
  have houterEventually :
      ∀ᶠ q : ℕ in cofinite,
        Valued.v (outerTerm q) <
          MonoidWithZeroHom.ValueGroup₀.embedding γ.1 :=
    houterZero.eventually hball
  let goodOuter : Set ℕ :=
    {q | Valued.v (outerTerm q) <
      MonoidWithZeroHom.ValueGroup₀.embedding γ.1}
  have hgoodOuter : goodOuter ∈ cofinite := by
    change {q : ℕ |
      Valued.v (outerTerm q) <
        MonoidWithZeroHom.ValueGroup₀.embedding γ.1} ∈ cofinite
    exact houterEventually
  have hbadOuterFinite : goodOuterᶜ.Finite :=
    Filter.mem_cofinite.mp hgoodOuter
  let Q : Finset ℕ := hbadOuterFinite.toFinset
  have hpower : ∀ q : ℕ,
      HasSum
        (fun d : ℕ => PowerSeries.coeff d (g ^ q) * x ^ d)
        (y ^ q) :=
    fun q => hasSum_powerSeries_pow_coeff_mul_pow g x y hgy q
  have hfiber : ∀ q : ℕ,
      HasSum (fun d : ℕ => term ⟨q, d⟩)
        (PowerSeries.coeff q f * y ^ q) := by
    intro q
    simpa [term, mul_assoc] using
      (hpower q).mul_left (PowerSeries.coeff q f)
  let badFiber : ℕ → Set ℕ := fun q => {d | term ⟨q, d⟩ ∉ s}
  have hbadFiberFinite : ∀ q : ℕ, (badFiber q).Finite := by
    intro q
    have hevent := (hfiber q).summable.tendsto_cofinite_zero.eventually hs
    apply (Filter.mem_cofinite.mp hevent).subset
    intro d hd
    exact hd
  let D : ℕ → Finset ℕ := fun q => (hbadFiberFinite q).toFinset
  let E : Finset (Sigma fun _ : ℕ => ℕ) := Q.sigma D
  apply Filter.mem_cofinite.mpr
  apply E.finite_toSet.subset
  intro qd hbad
  by_contra hnotE
  have hgood : term qd ∈ s := by
    by_cases hq : qd.1 ∈ Q
    · have hdnot : qd.2 ∉ D qd.1 := by
        intro hd
        apply hnotE
        exact Finset.mem_sigma.mpr ⟨hq, hd⟩
      by_contra hterm
      apply hdnot
      simp [D, badFiber, hterm]
    · have houterGood :
          Valued.v (outerTerm qd.1) <
            MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by
        have hgoodMem : qd.1 ∈ goodOuter := by
          by_contra hnotGood
          apply hq
          simpa [Q] using hnotGood
        exact hgoodMem
      apply hγ
      change Valued.v.restrict (term qd) < γ.1
      rw [Valuation.restrict_lt_iff_lt_embedding]
      have hbound :=
        valuation_powerSeries_subst_sigmaTerm_le_outerTerm
          Valued.v f g x hcoeff qd.1 qd.2
      exact lt_of_le_of_lt (by simpa [term, outerTerm] using hbound) houterGood
  exact hbad hgood

/-- Expanded substitution has the value obtained by first evaluating the
inner series and then the outer series. -/
theorem hasSum_powerSeries_subst_sigma
    [Valued K (WithZero (Multiplicative ℤ))] [CompleteSpace K]
    [NonarchimedeanRing K]
    (f g : PowerSeries K) (x y z : K)
    (hgy : HasSum (fun d : ℕ => PowerSeries.coeff d g * x ^ d) y)
    (houterX : Summable
      (fun q : ℕ => PowerSeries.coeff q f * x ^ q))
    (houterY : HasSum
      (fun q : ℕ => PowerSeries.coeff q f * y ^ q) z)
    (hcoeff : ∀ d : ℕ,
      Valued.v (PowerSeries.coeff d g * x ^ d) ≤ Valued.v x) :
    HasSum
      (fun qd : Sigma fun _ : ℕ => ℕ =>
        PowerSeries.coeff qd.1 f *
          PowerSeries.coeff qd.2 (g ^ qd.1) * x ^ qd.2)
      z := by
  have hsigma :=
    summable_powerSeries_subst_sigma_of_outer_summable
      f g x y hgy houterX hcoeff
  have hinner : ∀ q : ℕ,
      HasSum
        (fun d : ℕ =>
          PowerSeries.coeff q f * PowerSeries.coeff d (g ^ q) * x ^ d)
        (PowerSeries.coeff q f * y ^ q) := by
    intro q
    simpa [mul_assoc] using
      (hasSum_powerSeries_pow_coeff_mul_pow g x y hgy q).mul_left
        (PowerSeries.coeff q f)
  exact HasSum.sigma_of_hasSum houterY hinner hsigma

/-- Regrouping the expanded substitution by the final monomial degree gives
the coefficient evaluation of the formal substitution itself.  Finiteness
of every regrouped fiber is supplied by `PowerSeries.coeff_subst_finite'`.-/
theorem hasSum_powerSeries_subst_coeff_mul_pow_of_sigma
    [Valued K (WithZero (Multiplicative ℤ))]
    (f g : PowerSeries K) (x z : K)
    (hg0 : PowerSeries.constantCoeff g = 0)
    (hsigma :
      HasSum
        (fun qd : Sigma fun _ : ℕ => ℕ =>
          PowerSeries.coeff qd.1 f *
            PowerSeries.coeff qd.2 (g ^ qd.1) * x ^ qd.2)
        z) :
    HasSum
      (fun d : ℕ =>
        PowerSeries.coeff d (PowerSeries.subst g f) * x ^ d)
      z := by
  have hg : PowerSeries.HasSubst g :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hg0
  let sigmaTerm : (Sigma fun _ : ℕ => ℕ) → K := fun qd =>
    PowerSeries.coeff qd.1 f *
      PowerSeries.coeff qd.2 (g ^ qd.1) * x ^ qd.2
  have hsigma' : HasSum sigmaTerm z := by
    simpa [sigmaTerm] using hsigma
  let swap :
      (Sigma fun _ : ℕ => ℕ) ≃ (Sigma fun _ : ℕ => ℕ) :=
    { toFun := fun dq => ⟨dq.2, dq.1⟩
      invFun := fun qd => ⟨qd.2, qd.1⟩
      left_inv := by intro dq; cases dq; rfl
      right_inv := by intro qd; cases qd; rfl }
  have hswapped : HasSum (sigmaTerm ∘ swap) z :=
    (swap.hasSum_iff).2 hsigma'
  have hfiber : ∀ d : ℕ,
      HasSum
        (fun q : ℕ => (sigmaTerm ∘ swap) ⟨d, q⟩)
        (PowerSeries.coeff d (PowerSeries.subst g f) * x ^ d) := by
    intro d
    let base : ℕ → K := fun q =>
      PowerSeries.coeff q f • PowerSeries.coeff d (g ^ q)
    let fiberTerm : ℕ → K := fun q => base q * x ^ d
    have hsupport : base.support.Finite := by
      rw [← Function.HasFiniteSupport]
      simpa only [base] using PowerSeries.coeff_subst_finite' hg f d
    let S : Finset ℕ := hsupport.toFinset
    have hfinite :
        HasSum fiberTerm (∑ q ∈ S, fiberTerm q) := by
      apply hasSum_sum_of_ne_finset_zero
      intro q hq
      have hbase : base q = 0 := by
        by_contra hne
        apply hq
        simp [S, hne]
      simp [fiberTerm, hbase]
    have hsum :
        (∑ q ∈ S, fiberTerm q) =
          PowerSeries.coeff d (PowerSeries.subst g f) * x ^ d := by
      rw [PowerSeries.coeff_subst' hg f d]
      rw [finsum_eq_sum _ hsupport]
      rw [Finset.sum_mul]
    rw [hsum] at hfinite
    simpa [fiberTerm, base, sigmaTerm, swap, Function.comp_def,
      smul_eq_mul, mul_assoc] using hfinite
  exact hswapped.sigma hfiber

/-- A source-level evaluation theorem for convergent formal substitution. -/
theorem hasSum_powerSeries_subst_coeff_mul_pow
    [Valued K (WithZero (Multiplicative ℤ))] [CompleteSpace K]
    [NonarchimedeanRing K]
    (f g : PowerSeries K) (x y z : K)
    (hg0 : PowerSeries.constantCoeff g = 0)
    (hgy : HasSum (fun d : ℕ => PowerSeries.coeff d g * x ^ d) y)
    (houterX : Summable
      (fun q : ℕ => PowerSeries.coeff q f * x ^ q))
    (houterY : HasSum
      (fun q : ℕ => PowerSeries.coeff q f * y ^ q) z)
    (hcoeff : ∀ d : ℕ,
      Valued.v (PowerSeries.coeff d g * x ^ d) ≤ Valued.v x) :
    HasSum
      (fun d : ℕ =>
        PowerSeries.coeff d (PowerSeries.subst g f) * x ^ d)
      z := by
  apply hasSum_powerSeries_subst_coeff_mul_pow_of_sigma f g x z hg0
  exact hasSum_powerSeries_subst_sigma
    f g x y z hgy houterX houterY hcoeff

/-! ## Scaled logarithm and exponential input estimates -/

/-- Evaluation commutes with subtracting the constant power series `1`. -/
theorem hasSum_powerSeries_sub_one_coeff_mul_pow
    [Valued K (WithZero (Multiplicative ℤ))]
    (f : PowerSeries K) (x z : K)
    (hf : HasSum (fun d : ℕ => PowerSeries.coeff d f * x ^ d) z) :
    HasSum
      (fun d : ℕ => PowerSeries.coeff d (f - 1) * x ^ d)
      (z - 1) := by
  have hsingle :
      HasSum (fun d : ℕ => if d = 0 then (1 : K) else 0) 1 := by
    apply hasSum_single 0
    intro d hd
    simp [hd]
  have hone :
      HasSum
        (fun d : ℕ => PowerSeries.coeff d (1 : PowerSeries K) * x ^ d)
        1 :=
    hsingle.congr_fun fun d => by
      by_cases hd : d = 0
      · subst d
        simp
      · simp [PowerSeries.coeff_one, hd]
  refine (hf.sub hone).congr_fun ?_
  intro d
  rw [map_sub]
  ring

/-! ## Evaluation of the two formal identities -/

/-- Evaluation of the formal series `X`. -/
theorem hasSum_powerSeries_X_coeff_mul_pow
    [Valued K (WithZero (Multiplicative ℤ))] (x : K) :
    HasSum
      (fun d : ℕ => PowerSeries.coeff d (PowerSeries.X : PowerSeries K) * x ^ d)
      x := by
  have hsingle :
      HasSum (fun d : ℕ => if d = 1 then x else 0) x := by
    apply hasSum_single 1
    intro d hd
    simp [hd]
  exact hsingle.congr_fun fun d => by
    by_cases hd : d = 1
    · subst d
      simp [PowerSeries.coeff_X]
    · simp [PowerSeries.coeff_X, hd]

/-- Evaluation of the formal series `1 + X`. -/
theorem hasSum_powerSeries_one_add_X_coeff_mul_pow
    [Valued K (WithZero (Multiplicative ℤ))] (x : K) :
    HasSum
      (fun d : ℕ =>
        PowerSeries.coeff d (1 + PowerSeries.X : PowerSeries K) * x ^ d)
      (1 + x) := by
  have hsingle :
      HasSum (fun d : ℕ => if d = 0 then (1 : K) else 0) 1 := by
    apply hasSum_single 0
    intro d hd
    simp [hd]
  have hone :
      HasSum
        (fun d : ℕ => PowerSeries.coeff d (1 : PowerSeries K) * x ^ d)
        1 :=
    hsingle.congr_fun fun d => by
      by_cases hd : d = 0
      · subst d
        simp
      · simp [PowerSeries.coeff_one, hd]
  have hx := hasSum_powerSeries_X_coeff_mul_pow (K := K) x
  refine (hone.add hx).congr_fun ?_
  intro d
  rw [map_add]
  ring

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_FieldUnitFactors
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Finite and uniformizer factors of the field-unit group

This file isolates the two factors of the field-unit structure theorem which do not depend on
the structure theorem for first principal units.  The Teichmuller factor is
the cyclic group of order `q - 1`, with its (necessarily discrete) topology.
-/

noncomputable section

universe u v

namespace LocalFieldTheory.DiscreteValuationField
namespace CompleteDVF
namespace higherPrincipalUnitGroup

variable {K : Type u} [Field K]

/-- Additive version of `continuousMulEquivOfCompactToT2`. -/
noncomputable def continuousAddEquivOfCompactToT2
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [Add A] [Add B] [CompactSpace A] [T2Space B]
    (e : A ≃+ B) (he : Continuous e) : A ≃ₜ+ B :=
  ContinuousAddEquiv.mk'
    (he.homeoOfEquivCompactToT2 (f := e.toEquiv)) e.map_add

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PadicLinearOfContinuous
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Continuous additive maps of p-adic modules are p-adic linear

This is the density argument used explicitly in the local-field structure theory,
the field-unit structure theorem: compatibility with ordinary integral powers, together with
continuity of the p-adic scalar orbit, forces compatibility with every
p-adic scalar.
-/

noncomputable section

namespace LocalFieldTheory.DiscreteValuationField

/-- Turn a topological group equivalence whose source is an additive group
written multiplicatively into the inverse topological additive equivalence. -/
noncomputable def continuousAddEquivOfMultiplicativeSource
    {C G : Type*} [AddZeroClass C] [MulOneClass G]
    [TopologicalSpace C] [TopologicalSpace G]
    (e : Multiplicative C ≃ₜ* G) : Additive G ≃ₜ+ C :=
  { (MulEquiv.toAdditiveRight e.toMulEquiv).symm with
    continuous_toFun := e.continuous_invFun
    continuous_invFun := e.continuous_toFun }

/-- Turn a topological additive equivalence into the corresponding
topological multiplicative equivalence after tagging the source
multiplicatively. -/
noncomputable def continuousMulEquivOfAdditiveTarget
    {C G : Type*} [AddZeroClass C] [MulOneClass G]
    [TopologicalSpace C] [TopologicalSpace G]
    (e : C ≃ₜ+ Additive G) : Multiplicative C ≃ₜ* G :=
  { e.toAddEquiv.toMultiplicativeLeft with
    continuous_toFun := e.continuous_toFun
    continuous_invFun := e.continuous_invFun }

variable {p : ℕ} [Fact p.Prime]
variable {A B : Type*}
variable [TopologicalSpace A] [TopologicalSpace B]
variable [AddCommMonoid A] [AddCommMonoid B]
variable [Module ℤ_[p] A] [Module ℤ_[p] B]
variable [ContinuousSMul ℤ_[p] A] [ContinuousSMul ℤ_[p] B]
variable [T2Space B]

/-- A continuous additive homomorphism between topological `Z_p`-modules is
`Z_p`-linear.  The proof checks natural scalars and extends over the dense
copy of `ℕ` in `Z_p`. -/
theorem map_padicInt_smul_of_continuous
    (f : A →+ B) (hf : Continuous f) (a : ℤ_[p]) (x : A) :
    f (a • x) = a • f x := by
  have hleft : Continuous (fun z : ℤ_[p] => f (z • x)) :=
    hf.comp (continuous_id.smul continuous_const)
  have hright : Continuous (fun z : ℤ_[p] => z • f x) :=
    continuous_id.smul continuous_const
  have hclosed : IsClosed {z : ℤ_[p] | f (z • x) = z • f x} :=
    isClosed_eq hleft hright
  refine PadicInt.denseRange_natCast.induction_on a hclosed ?_
  intro n
  simp only [Nat.cast_smul_eq_nsmul, map_nsmul]

/-- Package the preceding density argument as a linear equivalence. -/
noncomputable def padicLinearEquivOfContinuousAddEquiv
    (e : A ≃+ B) (he : Continuous e) : A ≃ₗ[ℤ_[p]] B :=
  { e with
    map_smul' := fun a x =>
      map_padicInt_smul_of_continuous e.toAddMonoidHom he a x }

/-- Every `Z_p`-linear map from a finite Cartesian power of `Z_p` is
continuous when the target has continuous addition and scalar multiplication.
This is the elementary finite-basis continuity step used in the
mixed-characteristic part of the field-unit structure theorem. -/
theorem continuous_padicInt_finPi_linearMap
    {M : Type*} [TopologicalSpace M] [AddCommMonoid M]
    [Module ℤ_[p] M] [ContinuousAdd M] [ContinuousSMul ℤ_[p] M]
    (d : ℕ) (f : (Fin d → ℤ_[p]) →ₗ[ℤ_[p]] M) : Continuous f := by
  classical
  have hfun :
      (fun x : Fin d → ℤ_[p] => f x) =
        fun x => ∑ i : Fin d,
          x i • f (Pi.single (M := fun _ : Fin d => ℤ_[p]) i 1) := by
    funext x
    have hx : x = ∑ i : Fin d,
        x i • Pi.single (M := fun _ : Fin d => ℤ_[p]) i 1 :=
      pi_eq_sum_univ' x
    calc
      f x = f (∑ i : Fin d,
          x i • Pi.single (M := fun _ : Fin d => ℤ_[p]) i 1) :=
        congrArg f hx
      _ = ∑ i : Fin d,
          x i • f (Pi.single (M := fun _ : Fin d => ℤ_[p]) i 1) := by
        simp only [map_sum, map_smul]
  change Continuous (fun x : Fin d → ℤ_[p] => f x)
  rw [hfun]
  fun_prop

end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PadicModuleStructure
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod
attribute [-simp] _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Topological structure of a finite p-adic module

This file packages the PID step in the mixed-characteristic proof of
the local-field structure theory, the field-unit structure theorem.  Once the torsion submodule is known to
be a finite cyclic group of order `p^a`, and the torsion-free quotient has
rank `d`, the module is topologically the product of that cyclic factor and
`d` copies of `Z_p`.
-/

noncomputable section

universe u

namespace LocalFieldTheory.DiscreteValuationField
namespace CompleteDVF
namespace higherPrincipalUnitGroup

/-- A finite topological `Z_p`-module with cyclic torsion of order `p^a` and
torsion-free quotient of rank `d` is topologically
`ZMod (p^a) × Z_p^d`.

The algebraic splitting is obtained by projectively lifting the quotient map
and applying `lequivProdOfRightSplitExact`.  For continuity, its restriction
to the finite torsion factor is automatic, while its restriction to the free
factor is a linear map out of a finite Cartesian power of `Z_p`. -/
noncomputable def chosenPadicModuleContinuousAddEquivZModProdFinPi
    (p : ℕ) [Fact p.Prime]
    (M : Type u) [TopologicalSpace M] [AddCommGroup M] [Module ℤ_[p] M]
    [ContinuousAdd M] [ContinuousSMul ℤ_[p] M]
    [CompactSpace M] [T2Space M] [Module.Finite ℤ_[p] M]
    (a d : ℕ)
    [Finite (Submodule.torsion ℤ_[p] M)]
    (hcyclic : IsAddCyclic (Submodule.torsion ℤ_[p] M))
    (hcard : Nat.card (Submodule.torsion ℤ_[p] M) = p ^ a)
    (hfinrank : Module.finrank ℤ_[p]
      (M ⧸ Submodule.torsion ℤ_[p] M) = d) :
    (ZMod (p ^ a) × (Fin d → ℤ_[p])) ≃ₜ+ M := by
  let T : Submodule ℤ_[p] M := Submodule.torsion ℤ_[p] M
  let Q := M ⧸ T
  letI : Module.Finite ℤ_[p] Q := Module.Finite.quotient ℤ_[p] T
  letI : Module.IsTorsionFree ℤ_[p] Q :=
    Submodule.QuotientTorsion.instIsTorsionFree
  letI : Module.Free ℤ_[p] Q :=
    Module.free_of_finite_type_torsion_free'
  let b : Module.Basis (Fin d) ℤ_[p] Q :=
    Module.finBasisOfFinrankEq ℤ_[p] Q (by simpa [Q, T] using hfinrank)
  let q : M →ₗ[ℤ_[p]] Q := T.mkQ
  have hliftExists : ∃ lift : Q →ₗ[ℤ_[p]] M,
      q.comp lift = LinearMap.id :=
    Module.projective_lifting_property q LinearMap.id T.mkQ_surjective
  let lift : Q →ₗ[ℤ_[p]] M := Classical.choose hliftExists
  have hlift : q.comp lift = LinearMap.id := Classical.choose_spec hliftExists
  have hexact : LinearMap.range T.subtype = LinearMap.ker q := by
    change LinearMap.range T.subtype = LinearMap.ker T.mkQ
    rw [Submodule.range_subtype, Submodule.ker_mkQ]
  let split : (T × Q) ≃ₗ[ℤ_[p]] M :=
    lequivProdOfRightSplitExact T.injective_subtype hexact hlift
  let torsionEquiv : ZMod (p ^ a) ≃+ T := by
    rw [← hcard]
    exact zmodAddCyclicAddEquiv hcyclic
  let freeEquiv : (Fin d → ℤ_[p]) ≃ₗ[ℤ_[p]] Q := b.equivFun.symm
  let algebraic : (ZMod (p ^ a) × (Fin d → ℤ_[p])) ≃+ M :=
    (torsionEquiv.prodCongr freeEquiv.toAddEquiv).trans split.toAddEquiv
  let freeToM : (Fin d → ℤ_[p]) →ₗ[ℤ_[p]] M :=
    split.toLinearMap.comp
      ((LinearMap.inr ℤ_[p] T Q).comp freeEquiv.toLinearMap)
  have hfree : Continuous freeToM :=
    continuous_padicInt_finPi_linearMap d freeToM
  have htorsion : Continuous (fun z : ZMod (p ^ a) =>
      split (torsionEquiv z, (0 : Q))) :=
    continuous_of_discreteTopology
  have halgebraic : Continuous algebraic := by
    have hfun : (fun z : ZMod (p ^ a) × (Fin d → ℤ_[p]) => algebraic z) =
        fun z =>
          split (torsionEquiv z.1, (0 : Q)) +
            freeToM z.2 := by
      funext z
      change split (torsionEquiv z.1, freeEquiv z.2) =
        split (torsionEquiv z.1, 0) + split (0, freeEquiv z.2)
      rw [← split.map_add]
      simp
    change Continuous (fun z => algebraic z)
    rw [hfun]
    exact (htorsion.comp continuous_fst).add (hfree.comp continuous_snd)
  exact continuousAddEquivOfCompactToT2 algebraic halgebraic

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_MixedCharacteristicStructure_Core
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod
attribute [-simp] _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# First principal units in mixed characteristic

This module combines the deep free `Z_p` lattice with the finite quotient
exact sequence and packages the algebraic and topological structure of
the first principal-unit group.
-/

noncomputable section

universe u v

namespace LocalFieldTheory.DiscreteValuationField
namespace LocalField

open scoped WithZero nonZeroDivisors
open Module

variable {K : Type u} [Field K]

/-! ### The finite-level exact sequence and the first principal units -/

/-- Proof-relevant output of the finite-kernel/finite-quotient PID argument. -/
structure FiniteRankTorsionProjectionData
    (R M Q : Type*) [CommRing R]
    [AddCommGroup M] [AddCommGroup Q] [Module R M] [Module R Q]
    (f : M →ₗ[R] Q) (d : ℕ) where
  /-- The middle module is finitely generated over `R`. -/
  moduleFinite : Module.Finite R M
  /-- The torsion submodule of the middle module is finite. -/
  finiteTorsion : Finite (Submodule.torsion R M)
  /-- The restriction of `f` to the torsion submodule is injective. -/
  torsionProjection_injective :
    Function.Injective (f.domRestrict (Submodule.torsion R M))
  /-- The middle module has `R`-finrank `d`. -/
  finrankMiddle : Module.finrank R M = d
  /-- The torsion-free quotient of the middle module has `R`-finrank `d`. -/
  finrankFree :
    Module.finrank R (M ⧸ Submodule.torsion R M) = d

/-- A finite quotient together with its free kernel data. -/
structure FiniteQuotientSetup
    (R M Q : Type*) [CommRing R]
    [AddCommGroup M] [AddCommGroup Q] [Module R M] [Module R Q]
    (d : ℕ) where
  /-- The linear projection from the middle module to the quotient. -/
  projection : M →ₗ[R] Q
  /-- The projection onto the quotient is surjective. -/
  projection_surjective : Function.Surjective projection
  /-- The kernel of the projection is finitely generated over `R`. -/
  kernelFinite : Module.Finite R (LinearMap.ker projection)
  /-- The kernel of the projection is free over `R`. -/
  kernelFree : Module.Free R (LinearMap.ker projection)
  /-- The kernel of the projection has `R`-finrank `d`. -/
  kernelFinrank : Module.finrank R (LinearMap.ker projection) = d
  /-- The quotient module is torsion over `R`. -/
  quotientTorsion : Module.IsTorsion R Q

/-- The projection-free form of the finite-rank/torsion output.  Keeping the
large concrete quotient map out of downstream result types substantially
reduces elaboration. -/
structure FiniteRankTorsionData
    (R M Q : Type*) [CommRing R]
    [AddCommGroup M] [AddCommGroup Q] [Module R M] [Module R Q]
    (d : ℕ) where
  /-- The middle module is finitely generated over `R`. -/
  moduleFinite : Module.Finite R M
  /-- The torsion submodule of the middle module is finite. -/
  finiteTorsion : Finite (Submodule.torsion R M)
  /-- A linear map from the torsion submodule into the quotient module. -/
  torsionProjection : Submodule.torsion R M →ₗ[R] Q
  /-- The torsion projection is injective. -/
  torsionProjection_injective : Function.Injective torsionProjection
  /-- The middle module has `R`-finrank `d`. -/
  finrankMiddle : Module.finrank R M = d
  /-- The torsion-free quotient of the middle module has `R`-finrank `d`. -/
  finrankFree :
    Module.finrank R (M ⧸ Submodule.torsion R M) = d

/-- Algebraic bookkeeping for a finite torsion quotient of a finite free
kernel.  This is the PID step used in the mixed-characteristic field-unit structure theorem: it proves finite
generation and rank of the middle term, and embeds its torsion into the
finite quotient. -/
theorem finite_rank_and_torsion_projection_of_surjective
    {R M Q : Type*} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R]
    [AddCommGroup M] [AddCommGroup Q] [Module R M] [Module R Q]
    (f : M →ₗ[R] Q) (hf : Function.Surjective f)
    [Finite Q] [Module.Finite R Q]
    [Module.Finite R (LinearMap.ker f)] [Module.Free R (LinearMap.ker f)]
    (d : ℕ) (hrankKer : Module.finrank R (LinearMap.ker f) = d)
    (hQtorsion : Module.IsTorsion R Q) :
    FiniteRankTorsionProjectionData R M Q f d := by
  let N := LinearMap.ker f
  let eQuot : (M ⧸ N) ≃ₗ[R] Q :=
    LinearMap.quotKerEquivOfSurjective f hf
  let : Module.Finite R (M ⧸ N) := Module.Finite.equiv eQuot.symm
  let hM : Module.Finite R M := Module.Finite.of_submodule_quotient N
  have hquotTorsion : Module.IsTorsion R (M ⧸ N) := by
    intro x
    rcases @hQtorsion (eQuot x) with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    apply eQuot.injective
    calc
      eQuot (a • x) = a • eQuot x := eQuot.map_smul a x
      _ = 0 := ha
      _ = eQuot 0 := (eQuot.map_zero).symm
  have hrankQuot : Module.finrank R (M ⧸ N) = 0 :=
    Module.finrank_eq_zero_iff_isTorsion.mpr hquotTorsion
  have hrankM : Module.finrank R M = d := by
    have hsum := N.finrank_quotient_add_finrank
    rw [hrankQuot, zero_add] at hsum
    exact hsum.symm.trans hrankKer
  let T := Submodule.torsion R M
  let tproj : T →ₗ[R] Q := f.domRestrict T
  have htproj : Function.Injective tproj := by
    intro x y hxy
    apply Subtype.ext
    apply sub_eq_zero.mp
    have hzero : tproj (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hzN : (((x - y : T) : M)) ∈ N := by
      change f (((x - y : T) : M)) = 0
      exact hzero
    let zN : N := ⟨(((x - y : T) : M)), hzN⟩
    rcases (x - y).property with ⟨a, ha⟩
    have haz : (a : R) • zN = 0 := by
      apply Subtype.ext
      exact ha
    have ha_ne : (a : R) ≠ 0 :=
      mem_nonZeroDivisors_iff_ne_zero.mp a.property
    have hzN_zero : zN = 0 :=
      (smul_eq_zero.mp haz).resolve_left ha_ne
    exact congrArg Subtype.val hzN_zero
  let hT : Finite T := Finite.of_injective tproj htproj
  let : Module.Finite R T := inferInstance
  have hTtorsion : Module.IsTorsion R T := by
    intro x
    rcases x.property with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    apply Subtype.ext
    exact ha
  have hrankT : Module.finrank R T = 0 :=
    Module.finrank_eq_zero_iff_isTorsion.mpr hTtorsion
  let : Module.Finite R (M ⧸ T) := Module.Finite.quotient R T
  have hrankFree : Module.finrank R (M ⧸ T) = d := by
    have hsum := T.finrank_quotient_add_finrank
    rw [hrankT, add_zero] at hsum
    exact hsum.trans hrankM
  exact
    { moduleFinite := hM
      finiteTorsion := hT
      torsionProjection_injective := htproj
      finrankMiddle := hrankM
      finrankFree := hrankFree }

/-- Consume a finite quotient setup and forget the concrete quotient map
from the result type. -/
noncomputable def finite_rank_torsion_data_of_setup
    {R M Q : Type*} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R]
    [AddCommGroup M] [AddCommGroup Q] [Module R M] [Module R Q]
    [Finite Q] [Module.Finite R Q]
    (d : ℕ) (setup : FiniteQuotientSetup R M Q d) :
    FiniteRankTorsionData R M Q d := by
  letI : Module.Finite R (LinearMap.ker setup.projection) :=
    setup.kernelFinite
  letI : Module.Free R (LinearMap.ker setup.projection) :=
    setup.kernelFree
  let core := finite_rank_and_torsion_projection_of_surjective
    setup.projection setup.projection_surjective d
      setup.kernelFinrank setup.quotientTorsion
  exact
    { moduleFinite := core.moduleFinite
      finiteTorsion := core.finiteTorsion
      torsionProjection :=
        setup.projection.domRestrict (Submodule.torsion R M)
      torsionProjection_injective := core.torsionProjection_injective
      finrankMiddle := core.finrankMiddle
      finrankFree := core.finrankFree }

/-- The proof-relevant algebraic package used to assemble the topological
classification of the first principal units. -/
structure FirstPrincipalUnitAlgebraicData
    (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (p d : ℕ) where
  /-- The exponent in the prime-power order `p ^ a` of the torsion subgroup. -/
  a : ℕ
  /-- The first principal-unit module is finitely generated over `R`. -/
  moduleFinite : Module.Finite R M
  /-- The torsion submodule is finite. -/
  finiteTorsion : Finite (Submodule.torsion R M)
  /-- The torsion submodule is cyclic as an additive group. -/
  cyclicTorsion : IsAddCyclic (Submodule.torsion R M)
  /-- The torsion submodule has cardinality `p ^ a`. -/
  cardTorsion :
    letI := finiteTorsion
    Nat.card (Submodule.torsion R M) = p ^ a
  /-- The torsion-free quotient has `R`-finrank `d`. -/
  finrankFree :
    Module.finrank R (M ⧸ Submodule.torsion R M) = d

/-- A finite additive group that embeds, after changing notation, into the
multiplicative group of a domain is cyclic.  Keeping the type-tag conversion at
this general boundary avoids repeating it for complicated submodule types. -/
theorem isAddCyclic_of_injective_multiplicative_map
    {A U D : Type*} [AddGroup A] [Group U]
    [CommRing D] [IsDomain D] [Finite A]
    (f : A →+ Additive U) (g : U →* D)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    IsAddCyclic A := by
  let fmul : Multiplicative A →* U :=
    AddMonoidHom.toMultiplicativeLeft f
  have hfmul : Function.Injective fmul := by
    intro x y hxy
    exact Multiplicative.toAdd.injective
      (hf (Additive.toMul.injective hxy))
  exact isCyclic_multiplicative_iff.mp
    (isCyclic_of_injective_ringHom (g.comp fmul) (hg.comp hfmul))

/-- Transfer the prime-power cardinality of a finite additive quotient across
an injective additive map. -/
theorem exists_card_eq_prime_power_of_injective_addMonoidHom
    {p : ℕ} {A B : Type*} [Fact p.Prime]
    [AddGroup A] [AddGroup B] [Finite A]
    (f : A →+ B) (hf : Function.Injective f)
    (hB : IsPGroup p (Multiplicative B)) :
    ∃ a : ℕ, Nat.card A = p ^ a := by
  let fmul : Multiplicative A →* Multiplicative B :=
    AddMonoidHom.toMultiplicative f
  have hfmul : Function.Injective fmul := by
    intro x y hxy
    apply Multiplicative.toAdd.injective
    apply hf
    simpa [fmul] using congrArg Multiplicative.toAdd hxy
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (hB.of_injective fmul hfmul)
  exact ⟨a, (Nat.card_congr Multiplicative.ofAdd).trans ha⟩

/-- A finite free submodule together with its rank. -/
structure FiniteFreeSubmoduleData
    (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) (d : ℕ) where
  /-- The submodule `N` is finitely generated over `R`. -/
  moduleFinite : Module.Finite R N
  /-- The submodule `N` is free over `R`. -/
  moduleFree : Module.Free R N
  /-- The submodule `N` has `R`-finrank `d`. -/
  finrank : Module.finrank R N = d

end LocalField
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PadicPowerIndex
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero
attribute [-simp] _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# The `n`-fold multiple quotient of `Z_p`

This is the free p-adic factor in the local-field structure theory, the local-field power-index formula.
-/

noncomputable section

universe u

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory

namespace LocalFieldTheory.DiscreteValuationField

variable {p : ℕ} [Fact p.Prime]

/-- Additive `n`-fold multiples in `Z_p` are the principal ideal generated
by the natural number `n`. -/
theorem nsmulAddSubgroup_padicInt_eq_span (n : ℕ) :
    LocalFieldTheory.nsmulAddSubgroup ℤ_[p] n =
      (Ideal.span ({(n : ℤ_[p])} : Set ℤ_[p])).toAddSubgroup := by
  ext x
  rw [LocalFieldTheory.mem_nsmulAddSubgroup_iff]
  change (∃ y : ℤ_[p], n • y = x) ↔
    x ∈ Ideal.span ({(n : ℤ_[p])} : Set ℤ_[p])
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    simp [nsmul_eq_mul]
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    simp [nsmul_eq_mul]

/-- The valuation of a nonzero natural number in `Z_p` is `v_p(n)`. -/
theorem padicInt_valuation_natCast (n : ℕ) :
    (n : ℤ_[p]).valuation = padicValNat p n := by
  have h : (((n : ℤ_[p]) : ℚ_[p])).valuation =
      (padicValNat p n : ℤ) := by
    simpa only [PadicInt.coe_natCast] using
      Padic.valuation_natCast (p := p) n
  rw [PadicInt.valuation_coe] at h
  exact_mod_cast h

/-- A nonzero natural number generates the same ideal in `Z_p` as the
corresponding power of `p`. -/
theorem padicInt_span_natCast_eq_span_p_pow_padicValNat
    (n : ℕ) (hn : n ≠ 0) :
    Ideal.span ({(n : ℤ_[p])} : Set ℤ_[p]) =
      Ideal.span ({(p : ℤ_[p]) ^ padicValNat p n} : Set ℤ_[p]) := by
  rw [Ideal.span_singleton_eq_span_singleton]
  have hnZ : (n : ℤ_[p]) ≠ 0 := by exact_mod_cast hn
  have hfactor := PadicInt.unitCoeff_spec hnZ
  rw [padicInt_valuation_natCast] at hfactor
  rw [hfactor]
  exact associated_unit_mul_left _ _ (PadicInt.unitCoeff hnZ).isUnit

/-- The subgroup of `n`-fold multiples is the kernel of reduction modulo
`p ^ v_p(n)`. -/
theorem nsmulAddSubgroup_padicInt_eq_ker_toZModPow
    (n : ℕ) (hn : n ≠ 0) :
    LocalFieldTheory.nsmulAddSubgroup ℤ_[p] n =
      (PadicInt.toZModPow (p := p) (padicValNat p n)).toAddMonoidHom.ker := by
  rw [nsmulAddSubgroup_padicInt_eq_span,
    padicInt_span_natCast_eq_span_p_pow_padicValNat n hn,
    ← PadicInt.ker_toZModPow]
  rfl

/-- Coordinatewise reduction identifies the quotient of an arbitrary product
of copies of `Z_p` by `n`-fold multiples with a product of finite cyclic
groups. -/
noncomputable def padicIntPiNsmulQuotientEquiv
    {ι : Type u} (n : ℕ) (hn : n ≠ 0) :
    (ι → ℤ_[p]) ⧸ LocalFieldTheory.nsmulAddSubgroup (ι → ℤ_[p]) n ≃+
      (ι → ZMod (p ^ padicValNat p n)) := by
  let a := padicValNat p n
  let f : (ι → ℤ_[p]) →+ (ι → ZMod (p ^ a)) :=
    { toFun := fun x i => PadicInt.toZModPow a (x i)
      map_zero' := by ext i; simp
      map_add' := by intro x y; ext i; simp }
  have hf : Function.Surjective f := by
    intro y
    have hcoord : ∀ i : ι, ∃ x : ℤ_[p],
        PadicInt.toZModPow a x = y i := by
      intro i
      exact ZMod.ringHom_surjective (PadicInt.toZModPow a) (y i)
    choose x hx using hcoord
    refine ⟨x, ?_⟩
    ext i
    exact hx i
  have hkerOne : LocalFieldTheory.nsmulAddSubgroup ℤ_[p] n =
      (PadicInt.toZModPow (p := p) a).toAddMonoidHom.ker := by
    simpa [a] using nsmulAddSubgroup_padicInt_eq_ker_toZModPow
      (p := p) n hn
  have hker : LocalFieldTheory.nsmulAddSubgroup (ι → ℤ_[p]) n = f.ker := by
    ext x
    constructor
    · intro hx
      rw [LocalFieldTheory.mem_nsmulAddSubgroup_iff] at hx
      rcases hx with ⟨y, rfl⟩
      change f (n • y) = 0
      ext i
      have hi : n • y i ∈ LocalFieldTheory.nsmulAddSubgroup ℤ_[p] n :=
        (LocalFieldTheory.mem_nsmulAddSubgroup_iff (A := ℤ_[p])).2 ⟨y i, rfl⟩
      rw [hkerOne] at hi
      exact hi
    · intro hx
      change f x = 0 at hx
      have hcoord : ∀ i : ι, ∃ y : ℤ_[p], n • y = x i := by
        intro i
        rw [← LocalFieldTheory.mem_nsmulAddSubgroup_iff]
        rw [hkerOne]
        change PadicInt.toZModPow a (x i) = 0
        exact congrFun hx i
      choose y hy using hcoord
      rw [LocalFieldTheory.mem_nsmulAddSubgroup_iff]
      refine ⟨y, ?_⟩
      funext i
      exact hy i
  exact (QuotientAddGroup.quotientAddEquivOfEq hker).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective f hf)

/-- A finite product of nonzero scalar quotients of `Z_p` is finite. -/
noncomputable instance finite_padicInt_finPi_nsmulQuotient
    (d n : ℕ) [NeZero n] :
    Finite ((Fin d → ℤ_[p]) ⧸
      LocalFieldTheory.nsmulAddSubgroup (Fin d → ℤ_[p]) n) :=
  Finite.of_equiv
    (Fin d → ZMod (p ^ padicValNat p n))
    (padicIntPiNsmulQuotientEquiv
      (p := p) (ι := Fin d) n (NeZero.ne n)).symm.toEquiv

/-- A finite product of `d` copies contributes the expected
`p^(d v_p(n))` factor. -/
theorem card_padicInt_finPi_nsmulQuotient
    (d n : ℕ) [NeZero n] :
    Nat.card ((Fin d → ℤ_[p]) ⧸
        LocalFieldTheory.nsmulAddSubgroup (Fin d → ℤ_[p]) n) =
      p ^ (d * padicValNat p n) := by
  rw [Nat.card_congr
    (padicIntPiNsmulQuotientEquiv
      (p := p) (ι := Fin d) n (NeZero.ne n)).toEquiv,
    Nat.card_pi]
  simp only [Nat.card_zmod, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [← pow_mul, Nat.mul_comm]

/-- A nonzero natural scalar has trivial kernel on any product of `Z_p`. -/
theorem nsmulAddKernel_padicInt_pi_eq_bot
    {ι : Type u} (n : ℕ) (hn : n ≠ 0) :
    LocalFieldTheory.nsmulAddKernel (ι → ℤ_[p]) n = ⊥ := by
  have hnZ : (n : ℤ_[p]) ≠ 0 := by exact_mod_cast hn
  ext x
  rw [LocalFieldTheory.mem_nsmulAddKernel_iff]
  simp only [AddSubgroup.mem_bot]
  constructor
  · intro hx
    funext i
    have hi := congrFun hx i
    change n • x i = 0 at hi
    rw [nsmul_eq_mul] at hi
    exact (mul_eq_zero.mp hi).resolve_left hnZ
  · rintro rfl
    simp

/-- Nonzero scalar multiplication has a finite (trivial) kernel on any
product of copies of `Z_p`. -/
noncomputable instance finite_nsmulAddKernel_padicInt_pi
    {ι : Type u} (n : ℕ) [NeZero n] :
    Finite (LocalFieldTheory.nsmulAddKernel (ι → ℤ_[p]) n) := by
  rw [nsmulAddKernel_padicInt_pi_eq_bot (p := p) n (NeZero.ne n)]
  infer_instance

/-- Cardinal form of the preceding torsion-freeness statement. -/
theorem card_nsmulAddKernel_padicInt_pi
    {ι : Type u} (n : ℕ) [NeZero n] :
    Nat.card (LocalFieldTheory.nsmulAddKernel (ι → ℤ_[p]) n) = 1 := by
  rw [nsmulAddKernel_padicInt_pi_eq_bot (p := p) n (NeZero.ne n)]
  exact Nat.card_unique

section Product

variable (A B : Type*) [AddCommGroup A] [AddCommGroup B]

/-- Additive quotients by `n`-fold multiples commute with binary products at
the level of cardinality. -/
theorem card_nsmulAddQuotient_product (n : ℕ)
    [Finite (A ⧸ LocalFieldTheory.nsmulAddSubgroup A n)]
    [Finite (B ⧸ LocalFieldTheory.nsmulAddSubgroup B n)] :
    Nat.card ((A × B) ⧸ LocalFieldTheory.nsmulAddSubgroup (A × B) n) =
      Nat.card (A ⧸ LocalFieldTheory.nsmulAddSubgroup A n) *
        Nat.card (B ⧸ LocalFieldTheory.nsmulAddSubgroup B n) := by
  calc
    Nat.card ((A × B) ⧸ LocalFieldTheory.nsmulAddSubgroup (A × B) n) =
        Nat.card (Multiplicative (A × B) ⧸
          (powMonoidHom n : (Multiplicative (A × B)) →* (Multiplicative (A × B))).range) :=
      (LocalFieldTheory.card_multiplicative_nthPowerQuotient_eq_additive_nsmulQuotient
        (A × B) n).symm
    _ = Nat.card (Multiplicative A ⧸
          (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range) *
        Nat.card (Multiplicative B ⧸
          (powMonoidHom n : (Multiplicative B) →* (Multiplicative B)).range) :=
      LocalFieldTheory.card_nthPowerQuotient_eq_mul_of_mulEquiv_prod
        (Multiplicative (A × B)) (Multiplicative A) (Multiplicative B) n
        (MulEquiv.prodMultiplicative A B)
    _ = Nat.card (A ⧸ LocalFieldTheory.nsmulAddSubgroup A n) *
        Nat.card (B ⧸ LocalFieldTheory.nsmulAddSubgroup B n) := by
      rw [LocalFieldTheory.card_multiplicative_nthPowerQuotient_eq_additive_nsmulQuotient,
        LocalFieldTheory.card_multiplicative_nthPowerQuotient_eq_additive_nsmulQuotient]

/-- Kernels of `n`-fold multiplication commute with binary products at the
level of cardinality. -/
theorem card_nsmulAddKernel_product (n : ℕ)
    [Finite (LocalFieldTheory.nsmulAddKernel A n)]
    [Finite (LocalFieldTheory.nsmulAddKernel B n)] :
    Nat.card (LocalFieldTheory.nsmulAddKernel (A × B) n) =
      Nat.card (LocalFieldTheory.nsmulAddKernel A n) * Nat.card (LocalFieldTheory.nsmulAddKernel B n) := by
  calc
    Nat.card (LocalFieldTheory.nsmulAddKernel (A × B) n) =
        Nat.card ((powMonoidHom n : (Multiplicative (A × B)) →* (Multiplicative (A × B))).ker) :=
      (LocalFieldTheory.card_multiplicative_nthPowerKernel_eq_nsmulAddKernel
        (A × B) n).symm
    _ = Nat.card ((powMonoidHom n : (Multiplicative A × Multiplicative B) →* (Multiplicative A × Multiplicative B)).ker) := by
      rw [Nat.card_congr
        (LocalFieldTheory.nthPowerKernelEquivOfMulEquiv
          (Multiplicative (A × B))
          (Multiplicative A × Multiplicative B) n
          (MulEquiv.prodMultiplicative A B)).toEquiv]
    _ = Nat.card ((powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).ker) *
        Nat.card ((powMonoidHom n : (Multiplicative B) →* (Multiplicative B)).ker) :=
      LocalFieldTheory.card_nthPowerKernelProduct (Multiplicative A) (Multiplicative B) n
    _ = Nat.card (LocalFieldTheory.nsmulAddKernel A n) * Nat.card (LocalFieldTheory.nsmulAddKernel B n) := by
      rw [LocalFieldTheory.card_multiplicative_nthPowerKernel_eq_nsmulAddKernel,
        LocalFieldTheory.card_multiplicative_nthPowerKernel_eq_nsmulAddKernel]

end Product

/-- Mixed-characteristic free-factor calculation in the exact kernel-times-
defect form used by the local-field power-index formula. -/
theorem card_finite_prod_padicInt_finPi_nsmulQuotient_eq_kernel_mul
    (T : Type*) [AddCommGroup T] [Finite T]
    (d n : ℕ) [NeZero n] :
    Nat.card ((T × (Fin d → ℤ_[p])) ⧸
        LocalFieldTheory.nsmulAddSubgroup (T × (Fin d → ℤ_[p])) n) =
      Nat.card (LocalFieldTheory.nsmulAddKernel (T × (Fin d → ℤ_[p])) n) *
        p ^ (d * padicValNat p n) := by
  rw [card_nsmulAddQuotient_product,
    LocalFieldTheory.card_additive_nsmulQuotient_eq_nsmulKernel,
    card_padicInt_finPi_nsmulQuotient (p := p) d n,
    card_nsmulAddKernel_product,
    card_nsmulAddKernel_padicInt_pi (p := p) n]
  simp

end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_MaximalKummerSubgroup
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.KummerTheory.finiteSupportKummerQuotient_commGroupInstance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# The maximal Kummer subgroup

The largest admissible Kummer subgroup is the full unit group.  Its
restricted radical quotient is canonically the ordinary power-class group.
-/

noncomputable section

namespace KummerTheory

variable (K : Type) [Field K]

/-- The largest admissible Kummer subgroup, corresponding to adjoining all
`n`-th roots of elements of `Kˣ`. -/
def maximalKummerSubgroup (n : ℕ+) : KummerSubgroup K n :=
  ⟨⊤, le_top⟩

end KummerTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_SimpleExtension
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- A chosen `n`-th root of `b` in the separable closure. -/
noncomputable def chosenSimpleKummerRoot
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0) (b : Kˣ) :
    SeparableClosure K :=
  Classical.choose
    (exists_kummerRootSet
      (K := K) (Omega := SeparableClosure K) n hnK
      (maximalKummerSubgroup K n).1
      (⟨b, by simp [maximalKummerSubgroup]⟩ :
        (maximalKummerSubgroup K n).1))

/-- The chosen root belongs to the maximal Kummer root set. -/
theorem chosenSimpleKummerRoot_mem
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0) (b : Kˣ) :
    chosenSimpleKummerRoot K n hnK b ∈
      kummerRootSet (K := K) (Omega := SeparableClosure K) n
        (maximalKummerSubgroup K n).1 :=
  (Classical.choose_spec
    (exists_kummerRootSet
      (K := K) (Omega := SeparableClosure K) n hnK
      (maximalKummerSubgroup K n).1
      (⟨b, by simp [maximalKummerSubgroup]⟩ :
        (maximalKummerSubgroup K n).1))).1

/-- The simple Kummer extension generated by the chosen root of `b`. -/
def chosenSimpleKummerExtension
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0) (b : Kˣ) :
    IntermediateField K (SeparableClosure K) :=
  IntermediateField.adjoin K {chosenSimpleKummerRoot K n hnK b}

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.KummerTheory_Concrete_SUnitPreparation_FiniteRadicalSupport
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- The finite Kummer radical `D ∩ Kˢ`, where
`D = Lˣⁿ ∩ Kˣ`. -/
def sUnitFiniteKummerRadical
    {L : Type*} [Field L] [Algebra K L]
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup Kˣ :=
  SUnitGroup (K := K) S ⊓
    KummerTheory.finiteKummerRadicalSubgroup
      (K := K) (L := L) n

/-- An `S`-unit belongs to the finite Kummer radical exactly when it has
an `n`-th root in `L`. -/
@[simp]
theorem mem_sUnitFiniteKummerRadical_iff
    {L : Type*} [Field L] [Algebra K L]
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : Kˣ) :
    x ∈ sUnitFiniteKummerRadical (K := K) (L := L) n S ↔
      x ∈ SUnitGroup (K := K) S ∧
        ∃ beta : Lˣ,
          beta ^ (n : ℕ) =
            Units.map (algebraMap K L).toMonoidHom x :=
  Iff.rfl

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_SupportedIdelePowerLocalUnitQuotient
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Supported idele power-local-unit quotient

This module restricts the power-local-unit subgroup to ideles supported at
the prescribed finite places and identifies the resulting quotient with the
product of its archimedean and finite local power-class groups.
-/

open scoped NumberField Classical NNReal IsMulCommutative
open NumberField IsDedekindDomain
open KummerTheory

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type*} [Field K] [NumberField K]

noncomputable def quotientEquivOfSurjectiveWithKernel
    {G H : Type*} [Group G] [Group H]
    (f : G →* H)
    (N : Subgroup G) [N.Normal]
    (hf : Function.Surjective f)
    (hker : f.ker = N) :
    G ⧸ N ≃* H :=
  (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)


end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_IdeleClassPowerLocalUnitQuotient_SupportedIdeleIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Supported idele power quotient

This file expresses the supported idele quotient as the product of its local
archimedean and finite-place power indices and evaluates its cardinality.
-/

open scoped NumberField Classical NNReal ValuativeRel TensorProduct
open NumberField IsDedekindDomain
open KummerTheory
open LocalFieldTheory

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type} [Field K] [NumberField K]

/-- The finite-place product-formula calculation, stated directly for
the prime-ideal factors of the principal ideal `(n)`.
The hypothesis says exactly that `S` contains every finite place
dividing `n`; places added to `S` contribute the factor `1`. -/
theorem prod_absNorm_maxPowDividing_natCast
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS :
      ∀ v : HeightOneSpectrum (𝓞 K),
        v.asIdeal ∣ Ideal.span {((n : ℕ) : 𝓞 K)} →
          v ∈ S) :
    (∏ v : ↥S,
        Ideal.absNorm
          (v.1.maxPowDividing
            (Ideal.span {((n : ℕ) : 𝓞 K)}))) =
      (n : ℕ) ^ Module.finrank ℚ K := by
  classical
  let I : Ideal (𝓞 K) :=
    Ideal.span {((n : ℕ) : 𝓞 K)}
  have hI : I ≠ 0 := by
    simp [I, n.ne_zero]
  let f : HeightOneSpectrum (𝓞 K) → ℕ :=
    fun v => Ideal.absNorm (v.maxPowDividing I)
  have hsupport : Function.mulSupport f ⊆ (S : Set _) := by
    intro v hv
    apply hS v
    have hcount :
        (Associates.mk v.asIdeal).count
            (Associates.mk I).factors ≠ 0 := by
      intro hzero
      apply hv
      simp [f, IsDedekindDomain.HeightOneSpectrum.maxPowDividing,
        hzero]
    exact
      (Associates.count_ne_zero_iff_dvd
        hI v.irreducible).mp hcount
  have hmap :
      Ideal.absNorm
          (∏ᶠ v : HeightOneSpectrum (𝓞 K),
            v.maxPowDividing I) =
        ∏ᶠ v : HeightOneSpectrum (𝓞 K),
          Ideal.absNorm (v.maxPowDividing I) :=
    Ideal.absNorm.map_finprod
      (Ideal.hasFiniteMulSupport hI)
  calc
    (∏ v : ↥S,
        Ideal.absNorm
          (v.1.maxPowDividing
            (Ideal.span {((n : ℕ) : 𝓞 K)}))) =
        ∏ v ∈ S, f v := by
      simpa [f, I] using Finset.prod_coe_sort S f
    _ = ∏ᶠ v : HeightOneSpectrum (𝓞 K), f v :=
      (finprod_eq_prod_of_mulSupport_subset f hsupport).symm
    _ =
        Ideal.absNorm
          (∏ᶠ v : HeightOneSpectrum (𝓞 K),
            v.maxPowDividing I) := hmap.symm
    _ = Ideal.absNorm I := by
      rw [Ideal.finprod_heightOneSpectrum_factorization hI]
    _ = (n : ℕ) ^ Module.finrank ℚ K := by
      change
        Ideal.absNorm
            (Ideal.span {(((n : ℕ) : ℕ) : 𝓞 K)}) =
          (n : ℕ) ^ Module.finrank ℚ K
      rw [Ideal.absNorm_span_natCast,
        NumberField.RingOfIntegers.rank]


end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_CyclicIdeleClassNormIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# The global class-field axiom

This file proves the cyclic idele-class norm-index formula.  The first
input is the `H⁻¹` calculation for the principal-idele term in

`1 → Lˣ → I_L → C_L → 1`.

For a cyclic extension this term vanishes by Hilbert 90.  The result below
is transported through the actual low-degree Tate comparison and then
through the equivariant identification of `Lˣ` with the subgroup of
principal relative ideles.
-/

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

section NormQuotientCommutativity

/-- If a commutative group has exponent dividing `p`, then every
`d`-power map with `d` coprime to `p` is injective.  In the prime-degree
argument, `p` is the extension degree and `d` is the roots-of-unity
base-change degree. -/
theorem pow_injective_of_exponent_of_coprime
    {A : Type} [CommGroup A]
    (p d : ℕ)
    (hexponent : ∀ x : A, x ^ p = 1)
    (hcoprime : d.Coprime p) :
    Function.Injective (fun x : A => x ^ d) := by
  intro x y hxy
  change x ^ d = y ^ d at hxy
  have hdpow : (x * y⁻¹) ^ d = 1 := by
    calc
      (x * y⁻¹) ^ d = x ^ d * (y ^ d)⁻¹ := by
        rw [mul_pow, inv_pow]
      _ = 1 := by rw [hxy, mul_inv_cancel]
  have horder_d : orderOf (x * y⁻¹) ∣ d :=
    orderOf_dvd_of_pow_eq_one hdpow
  have horder_p : orderOf (x * y⁻¹) ∣ p :=
    orderOf_dvd_of_pow_eq_one (hexponent (x * y⁻¹))
  have horder_gcd :
      orderOf (x * y⁻¹) ∣ Nat.gcd d p :=
    Nat.dvd_gcd horder_d horder_p
  rw [hcoprime.gcd_eq_one] at horder_gcd
  have hxy_one : x * y⁻¹ = 1 :=
    orderOf_eq_one_iff.mp (Nat.dvd_one.mp horder_gcd)
  exact mul_inv_eq_one.mp hxy_one

end NormQuotientCommutativity

end GlobalClassFieldTheory.ClassFieldAxiom
end
end


