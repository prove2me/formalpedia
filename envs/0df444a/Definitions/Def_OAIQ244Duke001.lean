-- Prove2me | Definitions.Def_OAIQ244Duke001
-- name    : OAIQ244Duke001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:11:22.328262+00:00
-- url     : https://prove2.me/theorems/530ad1c8-196a-4d6c-8fa0-dbac916f964d
-- title:
--   Definitions bundle OAIQ244Duke001 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 320 declarations of OpenAI's Lean: 70 definitions, 6 inductive types or structures, 7 instances and 237 theorems. The definitions and types are `AlgebraicNumberTheory.Ramification.heightOnePrimeBelow`, `AlgebraicNumberTheory.Valuations.HasUniqueValuationSubringExtension`, `AlgebraicNumberTheory.Valuations.HenselFactorizationFinitePrefixState`, `AlgebraicNumberTheory.Valuations.IsCompleteForAbsoluteValue`, `AlgebraicNumberTheory.Valuations.absoluteValueConjugate`, `AlgebraicNumberTheory.Valuations.absoluteValueExponentialValuation`, `AlgebraicNumberTheory.Valuations.absoluteValueRestrictIntermediateField`, `AlgebraicNumberTheory.Valuations.absoluteValueUnitBallSubring`, `AlgebraicNumberTheory.Valuations.absoluteValueValuationSubring`, `AlgebraicNumberTheory.Valuations.completionTensorDecomposition_powerBasis`, `AlgebraicNumberTheory.Valuations.exponentialAssociatedAbsoluteValue`, `AlgebraicNumberTheory.Valuations.exponentialValuationRestrict`, `AlgebraicNumberTheory.Valuations.exponentialValuationRingMap`, `AlgebraicNumberTheory.Valuations.finiteExtensionNormFormulaValue`, `AlgebraicNumberTheory.Valuations.henselFactorization_adicCoeffCauchy`, `AlgebraicNumberTheory.Valuations.henselFactorization_henselIterate`, `AlgebraicNumberTheory.Valuations.henselFactorization_lowPart`, `AlgebraicNumberTheory.Valuations.henselFactorization_twoPolynomialCoeffFinset`, `AlgebraicNumberTheory.Valuations.ramificationAddValuation`, `AlgebraicNumberTheory.Valuations.unramifiedValuationRingValuationRingMap`, `HilbertRamification.absoluteValueDecompositionField`, `HilbertRamification.absoluteValueDecompositionGroup`, `LubinTate.Valuations.AssociatedAbsoluteValue`, `LubinTate.Valuations.EquivalentAbsoluteValues`, `LubinTate.Valuations.ExponentialValuation`, `LubinTate.Valuations.NonarchimedeanAbsoluteValue`, `LubinTate.Valuations.StrongTriangle`, `LubinTate.Valuations.exponentialMaxIdeal`, `LubinTate.Valuations.exponentialValuationRing`, `LubinTate.Valuations.exponentialValuationSubring`, `LubinTate.Valuations.exponentialValuationSubringAsValuationSubring`, `OAI.DukePrimeDegree.transverseLabelSigma`, `OAI.DukePrimeDegree.withinBlockPart`, `ValuationTheory.Completion.adjoinRootEquivBaseChange`, `ValuationTheory.Completion.adjoinRootProdEquivPi`, `ValuationTheory.Completion.adjoinRootToBaseChange`, `ValuationTheory.Completion.baseChangeEquivAdjoinRoot`, `ValuationTheory.Completion.powerBasisBaseChange`, `ValuationTheory.Completion.quotientInfAlgEquivPiQuotient`, `ValuationTheory.DiscreteValuationField.CompleteDVF` and 36 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Ramification_FiniteRamifiedPrimes`, `AlgebraicNumberTheory_RayClass_Ideal`, `DukePrimeDegree_Dynamics_BlockMatrixProjection`, `DukePrimeDegree_Entropy_InfiniteLabelEntropy`, `LocalField_Unramified_Definitions`, `Ramification_HilbertRamification_AbsoluteValueConjugacy`, `Ramification_HilbertRamification_DecompositionField`, `Ramification_HilbertRamification_DecompositionFieldExtension`, `Ramification_HilbertRamification_DecompositionGroup`, `Valuation_AbsoluteValue_AlgebraicExtension_NormFormula`, `Valuation_AbsoluteValue_AlgebraicExtension_NormFormulaCoefficients`, `Valuation_AbsoluteValue_AlgebraicExtension_NormFormulaExtension`, `Valuation_AbsoluteValue_AlgebraicExtension_NormFormulaIntegralClosure`, `Valuation_AbsoluteValue_AlgebraicExtension_RamificationInvariants`, `Valuation_AbsoluteValue_AlgebraicExtension_UniqueValuationSubring`, `Valuation_AbsoluteValue_Completeness`, `Valuation_AbsoluteValue_ExponentialValuation`, `Valuation_AbsoluteValue_PrincipalAdicCompleteness`, `Valuation_AbsoluteValue_Theory_AbsoluteValues`, `Valuation_AbsoluteValue_Theory_ExponentialValuations`, `Valuation_AbsoluteValue_ValuationSubring`, `Valuation_Completion_BaseChangeAdjoinRoot`, `Valuation_Completion_ExtensionFactorClassification`, `Valuation_Completion_ExtensionInvariants`, `Valuation_Completion_FiniteProductNormTrace`, `Valuation_Completion_PolynomialCRT`, `Valuation_Completion_TensorProductDecomposition`, `Valuation_DiscreteValuationField_Basic`, `Valuation_DiscreteValuationField_ChevalleyExtension`, `Valuation_DiscreteValuationField_Complete`, `Valuation_DiscreteValuationField_Extensions`, `Valuation_DiscreteValuationField_FiniteExtension_Core`, `Valuation_DiscreteValuationField_FiniteExtension_Degree`, `Valuation_DiscreteValuationField_Henselian`, `Valuation_DiscreteValuationField_IntegralClosure`, `Valuation_DiscreteValuationField_ResidueField`, `Valuation_Henselian_Core`, `Valuation_Henselian_Factorization_AdicLimits`, `Valuation_Henselian_Factorization_Basic`, `Valuation_Henselian_Factorization_CoefficientMinimum`, `Valuation_Henselian_Factorization_DegreeBounds`, `Valuation_Henselian_Factorization_ErrorPowers`, `Valuation_Henselian_Factorization_InfiniteApproximation`, `Valuation_Henselian_Factorization_Iteration`, `Valuation_Henselian_Factorization_Step`, `Valuation_Henselian_Factorization_Truncation`, `Valuation_Henselian_IrreduciblePolynomialBounds`, `Valuation_Henselian_IrreduciblePolynomialLifting`, `Valuation_Henselian_UniqueAlgebraicExtensions`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke014`, `OAIQ244Duke015`, `OAIQ244Duke017`, `OAIQ244Duke018`, `OAIQ244Duke019`, `OAIQ244Duke020`, `OAIQ244Duke021`, `OAIQ244Duke022` and `OAIQ244Duke023`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.CharP.Subring
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.LinearMap.Polynomial
import Mathlib.Algebra.Module.Shrink
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Order.WithTop.Untop0
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Normed.Algebra.GelfandMazur
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Field.ProperSpace
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finite.Perm
import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.Coset.Card
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
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.Ostrowski
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.RepresentationTheory.Homological.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RepresentationTheory.Homological.GroupHomology.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Flat.IsBaseChange
import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Polynomial.ContentIdeal
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
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
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Algebra.Ring.Compact
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.Algebra.Valued.ValuativeRel
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.AbsoluteValue
import Mathlib.Topology.UniformSpace.HeineCantor

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Ramification_FiniteRamifiedPrimes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Finiteness of ramified primes in Dedekind extensions

In a finite separable extension of Dedekind domains, only finitely many
height-one primes of either the extension ring or the base ring ramify.
-/

noncomputable section

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace AlgebraicNumberTheory.Ramification

variable (A B : Type*)
variable [CommRing A] [CommRing B] [Algebra A B]
variable [IsDedekindDomain A] [IsDedekindDomain B]
variable [Module.IsTorsionFree A B] [Module.Finite A B]
variable [Algebra.IsSeparable (FractionRing A) (FractionRing B)]

variable {A B}

/-- The height-one prime of the base lying below a height-one prime of a
finite Dedekind extension. -/
def heightOnePrimeBelow (w : IsDedekindDomain.HeightOneSpectrum B) :
    IsDedekindDomain.HeightOneSpectrum A where
  asIdeal := w.asIdeal.under A
  isPrime := inferInstance
  ne_bot := by
    have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
    exact mt Ideal.eq_bot_of_comap_eq_bot w.ne_bot

variable (A B)

/-- Only finitely many height-one primes of a finite separable Dedekind
extension ramify over the base. -/
theorem finite_ramified_heightOne_primes :
    {v : IsDedekindDomain.HeightOneSpectrum B |
        ¬ Algebra.IsUnramifiedAt A v.asIdeal}.Finite := by
  exact
    (Ideal.finite_factors (R := B) (I := differentIdeal A B)
        (differentIdeal_ne_bot (A := A) (B := B))).subset (by
      intro v hv
      exact (dvd_differentIdeal_iff (A := A) (B := B) (P := v.asIdeal)).mpr hv)

/-- Only finitely many height-one primes of the base ramify in a finite
separable Dedekind extension. -/
theorem finite_ramified_base_heightOne_primes :
    {v : IsDedekindDomain.HeightOneSpectrum A |
        ∃ w : IsDedekindDomain.HeightOneSpectrum B,
          w.asIdeal.LiesOver v.asIdeal ∧ ¬ Algebra.IsUnramifiedAt A w.asIdeal}.Finite := by
  let f : IsDedekindDomain.HeightOneSpectrum B →
      IsDedekindDomain.HeightOneSpectrum A :=
    heightOnePrimeBelow (A := A) (B := B)
  refine (finite_ramified_heightOne_primes A B).image f |>.subset ?_
  intro v hv
  rcases hv with ⟨w, hlie, hram⟩
  refine ⟨w, hram, ?_⟩
  apply IsDedekindDomain.HeightOneSpectrum.ext
  dsimp [f, heightOnePrimeBelow]
  let : w.asIdeal.LiesOver v.asIdeal := hlie
  exact (Ideal.over_def w.asIdeal v.asIdeal).symm

end AlgebraicNumberTheory.Ramification
end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_AbsoluteValue_Theory_AbsoluteValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Absolute values and exponential valuations

This module collects the valuation-theory material used by local class field
theory. General results on equivalence of absolute values, Ostrowski theory,
approximation, and rational-function examples are imported from Mathlib where
needed.
-/

noncomputable section

open Filter
open scoped BigOperators Topology

namespace LubinTate
namespace Valuations

/-- Finite triangle inequality for a absolute values. -/
theorem absoluteValue_finset_sum_le
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    {ι : Type*} (s : Finset ι) (f : ι → K) :
    v (s.sum f) ≤ s.sum (fun i => v (f i)) := by
  classical
  refine Finset.induction_on s ?empty ?insert
  · simp
  · intro i s his ih
    rw [Finset.sum_insert his, Finset.sum_insert his]
    exact (v.add_le (f i) (s.sum f)).trans
      (by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left ih (v (f i)))

/-- The equivalence relation on absolute values: two absolute values are equivalent if they induce the
same topology. -/
def EquivalentAbsoluteValues {K : Type*} [Field K]
    (v w : AbsoluteValue K ℝ) : Prop :=
  IsHomeomorph (WithAbs.congr v w (.refl K))

/-- absolute-value equivalence is the same as mathlib's equivalence relation on real
absolute values. -/
theorem equivalentAbsoluteValues_iff_isEquiv
    {K : Type*} [Field K] (v w : AbsoluteValue K ℝ) :
    EquivalentAbsoluteValues v w ↔ v.IsEquiv w :=
  (AbsoluteValue.isEquiv_iff_isHomeomorph v w).symm

/-- Mathlib-equivalent absolute values are equivalent under the defining equivalence relation. -/
theorem equivalentAbsoluteValues_of_isEquiv
    {K : Type*} [Field K] {v w : AbsoluteValue K ℝ}
    (h : v.IsEquiv w) :
    EquivalentAbsoluteValues v w :=
  (equivalentAbsoluteValues_iff_isEquiv v w).mpr h

/-- absolute-value equivalence is reflexive. -/
theorem equivalentAbsoluteValues_refl
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) :
    EquivalentAbsoluteValues v v :=
  equivalentAbsoluteValues_of_isEquiv (AbsoluteValue.IsEquiv.rfl (v := v))

/-- The power characterization of equivalent absolute values: two real absolute values are equivalent exactly when
one is a positive real power of the other. -/
theorem equivalentAbsoluteValues_iff_exists_rpow_eq
    {K : Type*} [Field K] (v w : AbsoluteValue K ℝ) :
    EquivalentAbsoluteValues v w ↔ ∃ s : ℝ, 0 < s ∧ (v · ^ s) = w := by
  exact
    (equivalentAbsoluteValues_iff_isEquiv v w).trans
      (AbsoluteValue.isEquiv_iff_exists_rpow_eq (v := v) (w := w))

/-- The archimedean/nonarchimedean dichotomy: a valuation is nonarchimedean when its values on the
natural numbers are bounded. -/
def NonarchimedeanAbsoluteValue {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, v (n : K) ≤ C

/-- The strong triangle inequality appearing in the boundedness characterization of nonarchimedean absolute values. -/
def StrongTriangle {K : Type*} [Field K] (v : AbsoluteValue K ℝ) : Prop :=
  ∀ x y : K, v (x + y) ≤ max (v x) (v y)

/-- The boundedness characterization of nonarchimedean absolute values, strong triangle inequality as mathlib's
`IsNonarchimedean` predicate. -/
theorem strong_triangle_iff_isNonarchimedean
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) :
    StrongTriangle v ↔ IsNonarchimedean (v : K → ℝ) :=
  Iff.rfl

/-- The easy direction of the boundedness characterization of nonarchimedean absolute values: the strong triangle inequality
bounds the values of the natural numbers by `1`. -/
theorem nat_le_one_of_strong_triangle
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hstrong : StrongTriangle v) (n : ℕ) :
    v (n : K) ≤ 1 := by
  exact ((strong_triangle_iff_isNonarchimedean v).mp hstrong).apply_natCast_le_one

/-- The easy direction of the boundedness characterization of nonarchimedean absolute values: a valuation satisfying the strong
triangle inequality is nonarchimedean in the boundedness-on-integers sense. -/
theorem nonarchimedean_of_strong_triangle
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hstrong : StrongTriangle v) :
    NonarchimedeanAbsoluteValue v :=
  ⟨1, nat_le_one_of_strong_triangle v hstrong⟩

/-- In the boundedness characterization of nonarchimedean absolute values, any bound for the values of the natural numbers is at
least `1`. -/
theorem nat_bound_ge_one
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) {C : ℝ}
    (hC : ∀ n : ℕ, v (n : K) ≤ C) :
    1 ≤ C := by
  simpa using hC 1

/-- The binomial-estimate step in the proof of the boundedness characterization of nonarchimedean absolute values: boundedness
of the values of natural numbers gives a polynomial factor in the estimate for
`(x + y)^n`. -/
theorem add_pow_le_of_bounded_nat
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) {C : ℝ}
    (hC : ∀ n : ℕ, v (n : K) ≤ C) (x y : K) (n : ℕ) :
    v ((x + y) ^ n) ≤
      ((n + 1 : ℕ) : ℝ) * C * (max (v x) (v y)) ^ n := by
  classical
  let M : ℝ := max (v x) (v y)
  have hC_nonneg : 0 ≤ C :=
    (zero_le_one : (0 : ℝ) ≤ 1).trans
      (nat_bound_ge_one v hC)
  have hM_nonneg : 0 ≤ M :=
    (v.nonneg x).trans (le_max_left (v x) (v y))
  have hsum_le :
      v ((Finset.range (n + 1)).sum
          (fun m => x ^ m * y ^ (n - m) * (n.choose m : K))) ≤
        (Finset.range (n + 1)).sum
          (fun m => v (x ^ m * y ^ (n - m) * (n.choose m : K))) :=
    absoluteValue_finset_sum_le v (Finset.range (n + 1))
      (fun m => x ^ m * y ^ (n - m) * (n.choose m : K))
  have hterm :
      ∀ m ∈ Finset.range (n + 1),
        v (x ^ m * y ^ (n - m) * (n.choose m : K)) ≤ C * M ^ n := by
    intro m hm
    have hmle : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hxpow : v (x ^ m) ≤ M ^ m := by
      rw [map_pow]
      exact pow_le_pow_left₀ (v.nonneg x) (le_max_left (v x) (v y)) m
    have hypow : v (y ^ (n - m)) ≤ M ^ (n - m) := by
      rw [map_pow]
      exact pow_le_pow_left₀ (v.nonneg y) (le_max_right (v x) (v y)) (n - m)
    have hxy :
        v (x ^ m) * v (y ^ (n - m)) ≤ M ^ m * M ^ (n - m) :=
      mul_le_mul hxpow hypow (v.nonneg (y ^ (n - m))) (pow_nonneg hM_nonneg m)
    have hchoose : v ((n.choose m : ℕ) : K) ≤ C := hC (n.choose m)
    calc
      v (x ^ m * y ^ (n - m) * (n.choose m : K))
          = v (x ^ m) * v (y ^ (n - m)) * v ((n.choose m : ℕ) : K) := by
              rw [map_mul, map_mul]
      _ ≤ (M ^ m * M ^ (n - m)) * C := by
              exact mul_le_mul hxy hchoose
                (v.nonneg ((n.choose m : ℕ) : K))
                (mul_nonneg (pow_nonneg hM_nonneg m)
                  (pow_nonneg hM_nonneg (n - m)))
      _ = C * M ^ n := by
              rw [← pow_add, Nat.add_sub_of_le hmle]
              ring
  calc
    v ((x + y) ^ n)
        = v ((Finset.range (n + 1)).sum
            (fun m => x ^ m * y ^ (n - m) * (n.choose m : K))) := by
            rw [add_pow]
    _ ≤ (Finset.range (n + 1)).sum
          (fun m => v (x ^ m * y ^ (n - m) * (n.choose m : K))) := hsum_le
    _ ≤ (Finset.range (n + 1)).sum (fun _m => C * M ^ n) :=
          Finset.sum_le_sum hterm
    _ = ((n + 1 : ℕ) : ℝ) * C * M ^ n := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]

/-- The real-variable limit used at the end of the boundedness characterization of nonarchimedean absolute values: after taking
`n`-th roots, the polynomial factor `(n+1)C` disappears. -/
theorem tendsto_linear_bound_rpow_inv
    {C : ℝ} (hC : 0 < C) :
    Tendsto
      (fun n : ℕ => ((((n + 1 : ℕ) : ℝ) * C) ^ ((n : ℝ)⁻¹)))
      atTop (𝓝 1) := by
  have hCroot :
      Tendsto (fun n : ℕ => C ^ ((n : ℝ)⁻¹)) atTop (𝓝 1) := by
    have hcont : ContinuousAt (fun t : ℝ => C ^ t) 0 :=
      Real.continuousAt_const_rpow hC.ne'
    have hzero : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    change Tendsto
      ((fun t : ℝ => C ^ t) ∘ fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 1)
    simpa only [Real.rpow_zero] using hcont.tendsto.comp hzero
  have hshiftReal :
      Tendsto (fun x : ℝ => x ^ ((1 : ℝ) / (1 * x + (-1)))) atTop (𝓝 1) :=
    tendsto_rpow_div_mul_add 1 1 (-1) zero_ne_one
  have hshiftNat :
      Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ ((n : ℝ)⁻¹)))
        atTop (𝓝 1) := by
    have hnatshift : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    refine (hshiftReal.comp hnatshift).congr' ?_
    exact Eventually.of_forall fun n => by
      simp [Nat.cast_add, Nat.cast_one, one_div, add_assoc]
  have htarget :
      Tendsto
        (fun n : ℕ => ((((n + 1 : ℕ) : ℝ) * C) ^ ((n : ℝ)⁻¹)))
        atTop (𝓝 (1 * 1)) := by
    refine (hshiftNat.mul hCroot).congr' ?_
    exact Eventually.of_forall fun n => by
      have hn_nonneg : 0 ≤ ((n + 1 : ℕ) : ℝ) := by positivity
      have hmul :=
        (Real.mul_rpow (z := ((n : ℝ)⁻¹)) hn_nonneg (le_of_lt hC)).symm
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  simpa using htarget

/-- The root form of the binomial estimate in the boundedness characterization of nonarchimedean absolute values. -/
theorem add_le_root_bound_of_bounded_nat
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) {C : ℝ}
    (hC : ∀ n : ℕ, v (n : K) ≤ C) (x y : K)
    {n : ℕ} (hn : n ≠ 0) :
    v (x + y) ≤
      ((((n + 1 : ℕ) : ℝ) * C) ^ ((n : ℝ)⁻¹)) *
        max (v x) (v y) := by
  classical
  let M : ℝ := max (v x) (v y)
  have hC_pos : 0 < C :=
    zero_lt_one.trans_le (nat_bound_ge_one v hC)
  have hM_nonneg : 0 ≤ M :=
    (v.nonneg x).trans (le_max_left (v x) (v y))
  by_cases hMzero : M = 0
  · have hx_le_zero : v x ≤ 0 := by
      simpa [M, hMzero] using (le_max_left (v x) (v y))
    have hy_le_zero : v y ≤ 0 := by
      simpa [M, hMzero] using (le_max_right (v x) (v y))
    have hxzero : x = 0 := (v.eq_zero).mp (le_antisymm hx_le_zero (v.nonneg x))
    have hyzero : y = 0 := (v.eq_zero).mp (le_antisymm hy_le_zero (v.nonneg y))
    simp [hxzero, hyzero]
  · have hpow :
        (v (x + y)) ^ n ≤ ((n + 1 : ℕ) : ℝ) * C * M ^ n := by
      simpa [map_pow, M] using
        add_pow_le_of_bounded_nat v hC x y n
    have hright_nonneg :
        0 ≤ ((n + 1 : ℕ) : ℝ) * C * M ^ n := by
      exact mul_nonneg
        (mul_nonneg (by positivity) (le_of_lt hC_pos))
        (pow_nonneg hM_nonneg n)
    have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hroot :
        v (x + y) ≤
          (((n + 1 : ℕ) : ℝ) * C * M ^ n) ^ ((n : ℝ)⁻¹) := by
      rw [Real.le_rpow_inv_iff_of_pos (v.nonneg (x + y)) hright_nonneg hn_pos]
      simpa [Real.rpow_natCast] using hpow
    calc
      v (x + y)
          ≤ (((n + 1 : ℕ) : ℝ) * C * M ^ n) ^ ((n : ℝ)⁻¹) := hroot
      _ = ((((n + 1 : ℕ) : ℝ) * C) ^ ((n : ℝ)⁻¹)) * M := by
            have hcoef_nonneg : 0 ≤ ((n + 1 : ℕ) : ℝ) * C :=
              mul_nonneg (by positivity) (le_of_lt hC_pos)
            rw [Real.mul_rpow hcoef_nonneg (pow_nonneg hM_nonneg n)]
            rw [Real.pow_rpow_inv_natCast hM_nonneg hn]
      _ = ((((n + 1 : ℕ) : ℝ) * C) ^ ((n : ℝ)⁻¹)) *
            max (v x) (v y) := by
            rfl

/-- The converse direction of the boundedness characterization of nonarchimedean absolute values: a bounded-on-integers
valuation satisfies the strong triangle inequality. -/
theorem strong_triangle_of_nonarchimedean
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : NonarchimedeanAbsoluteValue v) :
    StrongTriangle v := by
  rcases hnonarch with ⟨C, hC⟩
  have hC_pos : 0 < C :=
    zero_lt_one.trans_le (nat_bound_ge_one v hC)
  intro x y
  let M : ℝ := max (v x) (v y)
  have hlim :
      Tendsto
        (fun n : ℕ =>
          ((((n + 1 : ℕ) : ℝ) * C) ^ ((n : ℝ)⁻¹)) * M)
        atTop (𝓝 M) := by
    simpa using
      (tendsto_linear_bound_rpow_inv hC_pos).mul
        (tendsto_const_nhds (x := M))
  have heventually :
      ∀ᶠ n : ℕ in atTop,
        v (x + y) ≤
          ((((n + 1 : ℕ) : ℝ) * C) ^ ((n : ℝ)⁻¹)) * M := by
    refine eventually_atTop.2 ⟨1, ?_⟩
    intro n hn
    exact add_le_root_bound_of_bounded_nat
      (v := v) hC x y (n := n) (by omega)
  have hle :
      v (x + y) ≤ M :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim heventually
  simpa [M, StrongTriangle] using hle

end Valuations
end LubinTate
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_RayClass_Ideal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Ideals prime to a ray-class modulus

This file defines the subgroup of fractional ideals prime to a modulus,
connects it with the corresponding finite-idele higher-unit conditions, and
develops the approximation maps used in ray-class ideal constructions.
-/

open scoped NumberField WithZero Classical
open NumberField IsDedekindDomain

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace RayClass

/-! ### Simultaneous approximation at the places in a modulus -/

theorem adicAbv_isNontrivial
    (v : HeightOneSpectrum (𝓞 K)) :
    (NumberField.HeightOneSpectrum.adicAbv K v).IsNontrivial := by
  obtain ⟨x, hxv, hx0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  refine ⟨algebraMap (𝓞 K) K x, ?_, ?_⟩
  · exact (FaithfulSMul.algebraMap_eq_zero_iff (𝓞 K) K).not.mpr hx0
  · apply ne_of_lt
    rw [← FinitePlace.norm_embedding]
    exact (FinitePlace.norm_lt_one_iff_mem (K := K) v x).2 hxv

end RayClass
end
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_BlockMatrixProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The within-block matrix projection

The projection onto the within-block entries commutes with multiplication
by block-diagonal matrices on either side. Hence a scalar within-block
part stays scalar under every within-block conjugation, including the
unipotent shears used in the stopping-time argument.
-/

noncomputable section
open Matrix Set Filter
open scoped Topology Classical

namespace DukePrimeDegree

def withinBlockPart {n : ℕ} (r : Setoid (Fin n))
    (M : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if r i j then M i j else 0

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_InfiniteLabelEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Infinite future conditioning on positive-mass leaf atoms

Finite conditioned kernels converge to restriction to the whole itinerary
atom. Martingale convergence identifies this limit with conditioning on
the increasing union of the actual transverse-and-label sigma algebras.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace DukePrimeDegree

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    [StandardBorelSpace T] [Nonempty T]

@[instance_reducible] def transverseLabelSigma {N : ℕ} (Q : S × T → Fin N) : MeasurableSpace (S × T) :=
  MeasurableSpace.comap (fun z => (z.1,Q z)) inferInstance

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_AbsoluteValue_Completeness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Minimal absolute-value norm API

This file keeps only the lightweight explicit definitions used by the
current Section 4 formalization.  The old experimental completion and norm
formula development was removed because it duplicated mathlib APIs and no
longer compiled.
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

/-- A valued field is complete if it is complete for the uniformity
induced by its absolute value. -/
def IsCompleteForAbsoluteValue {K : Type*} [Field K] (v : AbsoluteValue K ℝ) : Prop :=
  @CompleteSpace K v.uniformSpace

/-- The uniformity attached directly to an absolute value agrees with the
uniformity coming from the normed-field structure induced by that absolute
value. -/
theorem absoluteValue_uniformSpace_eq_toNormedField
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) :
    v.uniformSpace = (AbsoluteValue.toNormedField v).toUniformSpace := by
  let : NormedField K := AbsoluteValue.toNormedField v
  ext s
  rw [(AbsoluteValue.hasBasis_uniformity v).mem_iff,
    Metric.uniformity_basis_dist.mem_iff]
  have hdist : ∀ p : K × K, dist p.1 p.2 = v (p.1 - p.2) := by
    intro p
    change v (-p.1 + p.2) = v (p.1 - p.2)
    simpa [sub_eq_add_neg, add_comm] using (v.map_sub p.1 p.2).symm
  simp [hdist, AbsoluteValue.map_sub]

/-- Completeness in the absolute-value uniformity is the same as
completeness of the corresponding `WithAbs` normed field. -/
theorem absoluteValueCompleteness_completeSpace_withAbs_iff_complete
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) :
    CompleteSpace (WithAbs v) ↔ IsCompleteForAbsoluteValue v := by
  let : NormedField K := AbsoluteValue.toNormedField v
  let e : WithAbs v ≃ᵢ K :=
    { toEquiv := (WithAbs.equiv v).toEquiv
      isometry_toFun := by
        rw [isometry_iff_dist_eq]
        intro x y
        simp only [dist_eq_norm_sub,
          WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_sub]
        rfl }
  rw [e.completeSpace_iff]
  change @CompleteSpace K (AbsoluteValue.toNormedField v).toUniformSpace ↔
    @CompleteSpace K v.uniformSpace
  rw [← absoluteValue_uniformSpace_eq_toNormedField v]

/-- A complete valued field is complete as the corresponding `WithAbs`
normed field. -/
theorem completeSpace_withAbs_of_isCompleteForAbsoluteValue
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hcomplete : IsCompleteForAbsoluteValue v) :
    CompleteSpace (WithAbs v) :=
  (absoluteValueCompleteness_completeSpace_withAbs_iff_complete v).2 hcomplete

/-- Sequence form of the sequential completeness criterion: a complete valued field is exactly one
where every Cauchy sequence in the absolute-value topology converges. -/
theorem absoluteValueCompleteness_complete_iff_cauchySeq_converges
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) :
    IsCompleteForAbsoluteValue v ↔
      ∀ u : ℕ → WithAbs v, CauchySeq u →
        ∃ a : WithAbs v, Filter.Tendsto u Filter.atTop (nhds a) := by
  constructor
  · intro hcomplete u hu
    let : CompleteSpace (WithAbs v) :=
      completeSpace_withAbs_of_isCompleteForAbsoluteValue v hcomplete
    exact cauchySeq_tendsto_of_complete hu
  · intro hseq
    exact (absoluteValueCompleteness_completeSpace_withAbs_iff_complete v).1
      (Metric.complete_of_cauchySeq_tendsto hseq)

/-- The finite-degree norm-formula candidate:
`x ↦ |N_{L/K}(x)|^{1/[L:K]}`. -/
def finiteExtensionNormFormulaValue
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) (x : L) : ℝ :=
  Real.rpow (v (Algebra.norm K x)) (1 / (Module.finrank K L : ℝ))

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_AbsoluteValue_Theory_ExponentialValuations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-! Provides the public declarations in the `ValuationTheory.AbsoluteValue.Theory.ExponentialValuations` Lean module. -/

noncomputable section

open Filter
open scoped BigOperators Topology

namespace LubinTate
namespace Valuations

/-- The additive exponential valuation with value `∞` at zero. -/
structure ExponentialValuation (K : Type*) [Field K] where
  /-- The value map into `ℝ ∪ {∞}`. -/
  toFun : K → WithTop ℝ
  /-- Exactly zero has value `∞`. -/
  eq_top_iff : ∀ x, toFun x = ⊤ ↔ x = 0
  /-- Multiplication becomes addition of values. -/
  map_mul : ∀ x y, toFun (x * y) = toFun x + toFun y
  /-- The nonarchimedean inequality in additive form. -/
  add_le_min : ∀ x y, min (toFun x) (toFun y) ≤ toFun (x + y)

/-- Coerce an exponential valuation to its function. -/
instance exponentialValuationCoeFun {K : Type*} [Field K] :
    CoeFun (ExponentialValuation K) (fun _ => K → WithTop ℝ) where
  coe v := v.toFun

/-- A multiplicative absolute value associated to an exponential valuation by `|x| = q^{-v(x)}`. -/
def AssociatedAbsoluteValue {K : Type*} [Field K]
    (v : ExponentialValuation K) (q : ℝ) (abv : AbsoluteValue K ℝ) : Prop :=
  1 < q ∧ ∀ x : K, x ≠ 0 → ∃ r : ℝ,
    v x = (r : WithTop ℝ) ∧ abv x = Real.rpow q (-r)

/-- The valuation ring `{x | v(x) ≥ 0}` attached to an exponential valuation. -/
def exponentialValuationRing {K : Type*} [Field K]
    (v : ExponentialValuation K) : Set K :=
  {x | (0 : WithTop ℝ) ≤ v x}

/-- Nonzero elements have finite value for a exponential valuation. -/
theorem exponentialValuation_ne_top_of_ne_zero {K : Type*} [Field K]
    (v : ExponentialValuation K) {x : K} (hx : x ≠ 0) :
    v x ≠ ⊤ := by
  intro htop
  exact hx ((v.eq_top_iff x).mp htop)

/-- A nonzero element has a real-valued exponential valuation. -/
theorem exponentialValuation_exists_real_of_ne_zero {K : Type*} [Field K]
    (v : ExponentialValuation K) {x : K} (hx : x ≠ 0) :
    ∃ r : ℝ, v x = (r : WithTop ℝ) := by
  rcases WithTop.ne_top_iff_exists.mp
      (exponentialValuation_ne_top_of_ne_zero v hx) with ⟨r, hr⟩
  exact ⟨r, hr.symm⟩

/-- The value of `1` is `0` for a exponential valuation. -/
@[simp]
theorem exponentialValuation_one {K : Type*} [Field K]
    (v : ExponentialValuation K) :
    v (1 : K) = 0 := by
  obtain ⟨r, hr⟩ :=
    exponentialValuation_exists_real_of_ne_zero v (one_ne_zero : (1 : K) ≠ 0)
  have hmul := v.map_mul (1 : K) (1 : K)
  rw [one_mul, hr] at hmul
  have hmul_real : r = r + r :=
    WithTop.coe_eq_coe.mp (by simpa [WithTop.coe_add] using hmul)
  have hr0 : r = 0 := by linarith
  simp [hr, hr0]

/-- The value of `-1` is `0` for a exponential valuation. -/
@[simp]
theorem exponentialValuation_neg_one {K : Type*} [Field K]
    (v : ExponentialValuation K) :
    v (-1 : K) = 0 := by
  obtain ⟨r, hr⟩ :=
    exponentialValuation_exists_real_of_ne_zero v
      (neg_ne_zero.mpr (one_ne_zero : (1 : K) ≠ 0))
  have hmul := v.map_mul (-1 : K) (-1 : K)
  have hsq : (-1 : K) * (-1 : K) = 1 := by ring
  rw [hsq, exponentialValuation_one v, hr] at hmul
  have hmul_real : (0 : ℝ) = r + r :=
    WithTop.coe_eq_coe.mp (by simpa [WithTop.coe_add] using hmul)
  have hr0 : r = 0 := by linarith
  simp [hr, hr0]

/-- Negation does not change a exponential valuation. -/
@[simp]
theorem exponentialValuation_neg {K : Type*} [Field K]
    (v : ExponentialValuation K) (x : K) :
    v (-x) = v x := by
  rw [← neg_one_mul, v.map_mul, exponentialValuation_neg_one, zero_add]

/-- An element of value zero is nonzero. -/
theorem exponentialValuation_ne_zero_of_value_eq_zero {K : Type*} [Field K]
    (v : ExponentialValuation K) {x : K} (hx : v x = 0) :
    x ≠ 0 := by
  intro hzero
  have htop : v x = ⊤ := (v.eq_top_iff x).mpr hzero
  rw [hx] at htop
  simp at htop

/-- The inverse of a value-zero element again has value zero. -/
theorem exponentialValuation_inv_of_value_eq_zero {K : Type*} [Field K]
    (v : ExponentialValuation K) {x : K} (hx : v x = 0) :
    v x⁻¹ = 0 := by
  have hx0 : x ≠ 0 := exponentialValuation_ne_zero_of_value_eq_zero v hx
  have hmul := v.map_mul x x⁻¹
  rw [mul_inv_cancel₀ hx0, exponentialValuation_one v, hx] at hmul
  simpa using hmul.symm

/-- Finite inverse-value formula for a exponential valuation. -/
theorem exponentialValuation_inv_value {K : Type*} [Field K]
    (v : ExponentialValuation K) {x : K} (hx : x ≠ 0) {r : ℝ}
    (hval : v x = (r : WithTop ℝ)) :
    v x⁻¹ = ((-r : ℝ) : WithTop ℝ) := by
  obtain ⟨s, hs⟩ :=
    exponentialValuation_exists_real_of_ne_zero v (inv_ne_zero hx)
  have hmul := v.map_mul x x⁻¹
  rw [mul_inv_cancel₀ hx, exponentialValuation_one v, hval, hs] at hmul
  have hmul_real : (0 : ℝ) = r + s :=
    WithTop.coe_eq_coe.mp (by simpa [WithTop.coe_add] using hmul)
  have hs_eq : s = -r := by
    linarith
  simp [hs, hs_eq]

/-- The set `{x | 0 ≤ v x}` is a subring. -/
def exponentialValuationSubring {K : Type*} [Field K]
    (v : ExponentialValuation K) : Subring K where
  carrier := exponentialValuationRing v
  zero_mem' := by
    change (0 : WithTop ℝ) ≤ v (0 : K)
    rw [(v.eq_top_iff 0).mpr rfl]
    simp
  one_mem' := by
    change (0 : WithTop ℝ) ≤ v (1 : K)
    simp
  add_mem' := by
    intro x y hx hy
    change (0 : WithTop ℝ) ≤ v (x + y)
    exact (le_min hx hy).trans (v.add_le_min x y)
  neg_mem' := by
    intro x hx
    change (0 : WithTop ℝ) ≤ v x at hx
    change (0 : WithTop ℝ) ≤ v (-x)
    simpa using hx
  mul_mem' := by
    intro x y hx hy
    change (0 : WithTop ℝ) ≤ v (x * y)
    rw [v.map_mul]
    exact add_nonneg hx hy

/-- Membership in the exponential-valuation subring is exactly the defining
condition `0 ≤ v x`. -/
theorem mem_exponentialValuationSubring_iff {K : Type*} [Field K]
    (v : ExponentialValuation K) (x : K) :
    x ∈ exponentialValuationSubring v ↔ (0 : WithTop ℝ) ≤ v x :=
  Iff.rfl

/-- Every element of the field or its inverse lies in the exponential-valuation ring. -/
theorem exponentialValuationRing_mem_or_inv_mem {K : Type*} [Field K]
    (v : ExponentialValuation K) (x : K) :
    x ∈ exponentialValuationRing v ∨ x⁻¹ ∈ exponentialValuationRing v := by
  by_cases hx : x = 0
  · left
    subst x
    change (0 : WithTop ℝ) ≤ v (0 : K)
    rw [(v.eq_top_iff 0).mpr rfl]
    simp
  · obtain ⟨r, hr⟩ := exponentialValuation_exists_real_of_ne_zero v hx
    by_cases hr_nonneg : 0 ≤ r
    · left
      change (0 : WithTop ℝ) ≤ v x
      rw [hr]
      exact WithTop.coe_le_coe.mpr hr_nonneg
    · right
      have hneg_nonneg : 0 ≤ -r := by
        linarith
      change (0 : WithTop ℝ) ≤ v x⁻¹
      rw [exponentialValuation_inv_value v hx hr]
      exact WithTop.coe_le_coe.mpr hneg_nonneg

/-- The absolute values subring satisfies mathlib's valuation-subring
membership alternative. -/
theorem exponentialValuationSubring_mem_or_inv_mem {K : Type*} [Field K]
    (v : ExponentialValuation K) (x : K) :
    x ∈ exponentialValuationSubring v ∨
      x⁻¹ ∈ exponentialValuationSubring v := by
  simpa [exponentialValuationSubring] using
    exponentialValuationRing_mem_or_inv_mem v x

/-- The exponential-valuation ring, bundled as mathlib's `ValuationSubring`. -/
def exponentialValuationSubringAsValuationSubring
    {K : Type*} [Field K] (v : ExponentialValuation K) :
    ValuationSubring K :=
  ValuationSubring.ofSubring (exponentialValuationSubring v)
    (exponentialValuationSubring_mem_or_inv_mem v)

/-- Membership in the bundled mathlib valuation subring is the defining condition
`0 ≤ v x`. -/
theorem mem_exponentialValuationSubringAsValuationSubring_iff
    {K : Type*} [Field K] (v : ExponentialValuation K) (x : K) :
    x ∈ exponentialValuationSubringAsValuationSubring v ↔
      (0 : WithTop ℝ) ≤ v x :=
  Iff.rfl

/-- For an associated multiplicative absolute value, `|x| ≤ 1` is the same as
the exponential value being nonnegative. -/
theorem associatedAbsoluteValue_le_one_iff
    {K : Type*} [Field K] {v : ExponentialValuation K}
    {q : ℝ} {abv : AbsoluteValue K ℝ}
    (hassoc : AssociatedAbsoluteValue v q abv) {x : K} (hx : x ≠ 0) :
    abv x ≤ 1 ↔ (0 : WithTop ℝ) ≤ v x := by
  rcases hassoc.2 x hx with ⟨r, hval, habv⟩
  have hq : 1 < q := hassoc.1
  have hq_pos : 0 < q := zero_lt_one.trans hq
  have hq_not_le_one : ¬ q ≤ 1 := not_le.mpr hq
  constructor
  · intro habv_le
    have hpow : q ^ (-r) ≤ 1 := by
      simpa [habv] using habv_le
    have hneg_nonpos : -r ≤ 0 := by
      rcases (Real.rpow_le_one_iff_of_pos hq_pos).mp hpow with hcase | hcase
      · exact hcase.2
      · exact (hq_not_le_one hcase.1).elim
    have hr_nonneg : 0 ≤ r := by linarith
    have hwt : ((0 : ℝ) : WithTop ℝ) ≤ (r : WithTop ℝ) :=
      WithTop.coe_le_coe.mpr hr_nonneg
    simpa [hval] using hwt
  · intro hval_nonneg
    have hr_nonneg : 0 ≤ r := by
      have hwt : ((0 : ℝ) : WithTop ℝ) ≤ (r : WithTop ℝ) := by
        simpa [hval] using hval_nonneg
      exact WithTop.coe_le_coe.mp hwt
    have hneg_nonpos : -r ≤ 0 := by linarith
    have hpow : q ^ (-r) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt hq) hneg_nonpos
    simpa [habv] using hpow

/-- For an associated multiplicative absolute value, `|x| < 1` is the same as
the exponential value being positive. -/
theorem associatedAbsoluteValue_lt_one_iff
    {K : Type*} [Field K] {v : ExponentialValuation K}
    {q : ℝ} {abv : AbsoluteValue K ℝ}
    (hassoc : AssociatedAbsoluteValue v q abv) {x : K} (hx : x ≠ 0) :
    abv x < 1 ↔ (0 : WithTop ℝ) < v x := by
  rcases hassoc.2 x hx with ⟨r, hval, habv⟩
  have hq : 1 < q := hassoc.1
  have hq_pos : 0 < q := zero_lt_one.trans hq
  have hq_not_lt_one : ¬ q < 1 := not_lt.mpr (le_of_lt hq)
  constructor
  · intro habv_lt
    have hpow : q ^ (-r) < 1 := by
      simpa [habv] using habv_lt
    have hneg_neg : -r < 0 := by
      rcases (Real.rpow_lt_one_iff_of_pos hq_pos).mp hpow with hcase | hcase
      · exact hcase.2
      · exact (hq_not_lt_one hcase.1).elim
    have hr_pos : 0 < r := by linarith
    have hwt : ((0 : ℝ) : WithTop ℝ) < (r : WithTop ℝ) :=
      WithTop.coe_lt_coe.mpr hr_pos
    simpa [hval] using hwt
  · intro hval_pos
    have hr_pos : 0 < r := by
      have hwt : ((0 : ℝ) : WithTop ℝ) < (r : WithTop ℝ) := by
        simpa [hval] using hval_pos
      exact WithTop.coe_lt_coe.mp hwt
    have hneg_neg : -r < 0 := by linarith
    have hpow : q ^ (-r) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hq hneg_neg
    simpa [habv] using hpow

/-- For an associated multiplicative absolute value, `|x| = 1` is the same as
the exponential value being zero. -/
theorem associatedAbsoluteValue_eq_one_iff
    {K : Type*} [Field K] {v : ExponentialValuation K}
    {q : ℝ} {abv : AbsoluteValue K ℝ}
    (hassoc : AssociatedAbsoluteValue v q abv) {x : K} (hx : x ≠ 0) :
    abv x = 1 ↔ v x = 0 := by
  constructor
  · intro habv_one
    have hle : (0 : WithTop ℝ) ≤ v x :=
      (associatedAbsoluteValue_le_one_iff
        (v := v) (q := q) (abv := abv) hassoc hx).mp
        (le_of_eq habv_one)
    have hnlt : ¬ (0 : WithTop ℝ) < v x := by
      intro hvpos
      have habv_lt :
          abv x < 1 :=
        (associatedAbsoluteValue_lt_one_iff
          (v := v) (q := q) (abv := abv) hassoc hx).mpr hvpos
      exact (not_lt_of_ge (le_of_eq habv_one.symm)) habv_lt
    exact le_antisymm (le_of_not_gt hnlt) hle
  · intro hvzero
    have hle : abv x ≤ 1 :=
      (associatedAbsoluteValue_le_one_iff
        (v := v) (q := q) (abv := abv) hassoc hx).mpr
        (by simp [hvzero])
    have hnlt : ¬ abv x < 1 := by
      intro habv_lt
      have hvpos :
          (0 : WithTop ℝ) < v x :=
        (associatedAbsoluteValue_lt_one_iff
          (v := v) (q := q) (abv := abv) hassoc hx).mp habv_lt
      simp [hvzero] at hvpos
    exact le_antisymm hle (le_of_not_gt hnlt)

/-- The positive-value elements form an ideal of the exponential-valuation ring. -/
def exponentialMaxIdeal {K : Type*} [Field K]
    (v : ExponentialValuation K) : Ideal (exponentialValuationSubring v) where
  carrier := {x | (0 : WithTop ℝ) < v (x : K)}
  zero_mem' := by
    change (0 : WithTop ℝ) < v (0 : K)
    rw [(v.eq_top_iff 0).mpr rfl]
    simp
  add_mem' := by
    intro x y hx hy
    change (0 : WithTop ℝ) < v ((x + y : exponentialValuationSubring v) : K)
    have hmin : (0 : WithTop ℝ) < min (v (x : K)) (v (y : K)) :=
      lt_min hx hy
    exact lt_of_lt_of_le hmin (by simpa using v.add_le_min (x : K) (y : K))
  smul_mem' := by
    intro a x hx
    change (0 : WithTop ℝ) < v ((a : K) * (x : K))
    have ha : (0 : WithTop ℝ) ≤ v (a : K) := a.property
    rw [v.map_mul]
    have hx_le : v (x : K) ≤ v (a : K) + v (x : K) := by
      simpa [zero_add] using
        (add_le_add ha (le_rfl : v (x : K) ≤ v (x : K)))
    exact lt_of_lt_of_le hx hx_le

/-- The unit element is not in the positive-value ideal. -/
theorem one_not_mem_exponentialMaxIdeal {K : Type*} [Field K]
    (v : ExponentialValuation K) :
    (1 : exponentialValuationSubring v) ∉ exponentialMaxIdeal v := by
  change ¬ (0 : WithTop ℝ) < v (1 : K)
  simp

/-- Inside the valuation ring, not lying in the positive-value ideal is the same
as having value zero. -/
theorem not_mem_exponentialMaxIdeal_iff_value_eq_zero {K : Type*} [Field K]
    (v : ExponentialValuation K) (x : exponentialValuationSubring v) :
    x ∉ exponentialMaxIdeal v ↔ v (x : K) = 0 := by
  constructor
  · intro hx
    change ¬ (0 : WithTop ℝ) < v (x : K) at hx
    exact le_antisymm (le_of_not_gt hx) x.property
  · intro hx
    change ¬ (0 : WithTop ℝ) < v (x : K)
    simp [hx]

/-- Value-zero elements of the valuation ring are units of that ring. -/
theorem isUnit_of_exponentialValuation_eq_zero {K : Type*} [Field K]
    (v : ExponentialValuation K) {x : exponentialValuationSubring v}
    (hx : v (x : K) = 0) :
    IsUnit x := by
  rw [Submonoid.isUnit_iff_and (S := exponentialValuationSubring v) (a := x)]
  constructor
  · exact exponentialValuation_ne_zero_of_value_eq_zero v hx
  · change (0 : WithTop ℝ) ≤ v ((x : K)⁻¹)
    simp [exponentialValuation_inv_of_value_eq_zero v hx]

/-- Units of the valuation ring have value zero. -/
theorem exponentialValuation_eq_zero_of_isUnit {K : Type*} [Field K]
    (v : ExponentialValuation K) {x : exponentialValuationSubring v}
    (hx : IsUnit x) :
    v (x : K) = 0 := by
  have hx_inv :=
    (Submonoid.isUnit_iff_and (S := exponentialValuationSubring v) (a := x)).mp hx
  have hx_nonneg : (0 : WithTop ℝ) ≤ v (x : K) := x.property
  have hinv_nonneg : (0 : WithTop ℝ) ≤ v ((x : K)⁻¹) := hx_inv.2
  have hmul := v.map_mul (x : K) ((x : K)⁻¹)
  rw [mul_inv_cancel₀ hx_inv.1, exponentialValuation_one v] at hmul
  have hx_le_zero : v (x : K) ≤ 0 := by
    calc
      v (x : K) ≤ v (x : K) + v ((x : K)⁻¹) :=
        le_add_of_nonneg_right hinv_nonneg
      _ = 0 := hmul.symm
  exact le_antisymm hx_le_zero hx_nonneg

/-- A valuation-ring element outside the positive-value ideal is a unit. -/
theorem isUnit_of_not_mem_exponentialMaxIdeal {K : Type*} [Field K]
    (v : ExponentialValuation K) {x : exponentialValuationSubring v}
    (hx : x ∉ exponentialMaxIdeal v) :
    IsUnit x :=
  isUnit_of_exponentialValuation_eq_zero v
    ((not_mem_exponentialMaxIdeal_iff_value_eq_zero v x).mp hx)

/-- Units of the valuation ring do not lie in the positive-value ideal. -/
theorem not_mem_exponentialMaxIdeal_of_isUnit {K : Type*} [Field K]
    (v : ExponentialValuation K) {x : exponentialValuationSubring v}
    (hx : IsUnit x) :
    x ∉ exponentialMaxIdeal v := by
  have hzero : v (x : K) = 0 :=
    exponentialValuation_eq_zero_of_isUnit v hx
  change ¬ (0 : WithTop ℝ) < v (x : K)
  simp [hzero]

/-- In the valuation ring, the units are exactly the complement of the
positive-value ideal. -/
theorem isUnit_iff_not_mem_exponentialMaxIdeal {K : Type*} [Field K]
    (v : ExponentialValuation K) (x : exponentialValuationSubring v) :
    IsUnit x ↔ x ∉ exponentialMaxIdeal v := by
  constructor
  · exact not_mem_exponentialMaxIdeal_of_isUnit v
  · exact isUnit_of_not_mem_exponentialMaxIdeal v

/-- For an associated absolute value, the units of the valuation ring are
exactly the elements of absolute value `1`. -/
theorem associatedAbsoluteValue_isUnit_iff_eq_one
    {K : Type*} [Field K] {v : ExponentialValuation K}
    {q : ℝ} {abv : AbsoluteValue K ℝ}
    (hassoc : AssociatedAbsoluteValue v q abv)
    (x : exponentialValuationSubring v) :
    IsUnit x ↔ abv (x : K) = 1 := by
  constructor
  · intro hx
    have hvzero : v (x : K) = 0 :=
      exponentialValuation_eq_zero_of_isUnit v hx
    have hx0 : (x : K) ≠ 0 :=
      exponentialValuation_ne_zero_of_value_eq_zero v hvzero
    exact
      (associatedAbsoluteValue_eq_one_iff
        (v := v) (q := q) (abv := abv) hassoc hx0).mpr hvzero
  · intro habv_one
    have hx0 : (x : K) ≠ 0 := by
      intro hx_zero
      have hzero : abv (x : K) = 0 := by
        simp [hx_zero]
      rw [hzero] at habv_one
      norm_num at habv_one
    have hvzero : v (x : K) = 0 :=
      (associatedAbsoluteValue_eq_one_iff
        (v := v) (q := q) (abv := abv) hassoc hx0).mp habv_one
    exact isUnit_of_exponentialValuation_eq_zero v hvzero

/-- The positive-value ideal is maximal in the exponential-valuation ring. -/
theorem exponentialMaxIdeal_isMaximal {K : Type*} [Field K]
    (v : ExponentialValuation K) :
    (exponentialMaxIdeal v).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  constructor
  · exact one_not_mem_exponentialMaxIdeal v
  · intro J x hIJ hx_not_mem hxJ
    exact (Ideal.eq_top_iff_one J).mp
      (J.eq_top_of_isUnit_mem hxJ
        ((isUnit_iff_not_mem_exponentialMaxIdeal v x).mpr hx_not_mem))

/-- The exponential-valuation ring is local. -/
instance exponentialValuationSubringIsLocalRing {K : Type*} [Field K]
    (v : ExponentialValuation K) :
    IsLocalRing (exponentialValuationSubring v) :=
  IsLocalRing.of_nonunits_add fun x y hx hy => by
    have hx_mem : x ∈ exponentialMaxIdeal v := by
      by_contra hx_not_mem
      exact hx ((isUnit_iff_not_mem_exponentialMaxIdeal v x).mpr hx_not_mem)
    have hy_mem : y ∈ exponentialMaxIdeal v := by
      by_contra hy_not_mem
      exact hy ((isUnit_iff_not_mem_exponentialMaxIdeal v y).mpr hy_not_mem)
    have hxy_mem : x + y ∈ exponentialMaxIdeal v :=
      (exponentialMaxIdeal v).add_mem hx_mem hy_mem
    exact fun hxy_unit =>
      (not_mem_exponentialMaxIdeal_of_isUnit v hxy_unit) hxy_mem

/-- The positive-value ideal agrees with mathlib's maximal ideal of the
valuation ring. -/
theorem exponentialMaxIdeal_eq_maximalIdeal {K : Type*} [Field K]
    (v : ExponentialValuation K) :
    exponentialMaxIdeal v =
      IsLocalRing.maximalIdeal (exponentialValuationSubring v) :=
  IsLocalRing.eq_maximalIdeal (exponentialMaxIdeal_isMaximal v)

end Valuations
end LubinTate
end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_AbsoluteValue_ValuationSubring
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Closed unit balls of nonarchimedean absolute values

This file records the valuation ring attached directly to a multiplicative
absolute value in the nonarchimedean case.  It is the section-3 object used by
the finite-degree norm construction before any discrete-valuation-field packaging.
-/

noncomputable section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- The closed unit ball `{x | |x| ≤ 1}` of a nonarchimedean absolute value,
bundled as a subring. -/
def absoluteValueUnitBallSubring
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v) : Subring K where
  carrier := {x | v x ≤ 1}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro x y hx hy
    exact (LubinTate.Valuations.strong_triangle_of_nonarchimedean
      v hnonarch x y).trans (max_le hx hy)
  neg_mem' := by
    intro x hx
    simpa using hx
  mul_mem' := by
    intro x y hx hy
    change v (x * y) ≤ 1
    rw [v.map_mul]
    exact (mul_le_of_le_one_left (v.nonneg y) hx).trans hy

/-- Membership in the absolute-value valuation subring is the closed-unit-ball
condition. -/
theorem mem_absoluteValueUnitBallSubring_iff
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v) (x : K) :
    x ∈ absoluteValueUnitBallSubring v hnonarch ↔ v x ≤ 1 :=
  Iff.rfl

/-- Every field element or its inverse lies in the closed unit ball of a
nonarchimedean absolute value. -/
theorem absoluteValueUnitBallSubring_mem_or_inv_mem
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v) (x : K) :
    x ∈ absoluteValueUnitBallSubring v hnonarch ∨
      x⁻¹ ∈ absoluteValueUnitBallSubring v hnonarch := by
  by_cases hx : v x ≤ 1
  · exact Or.inl ((mem_absoluteValueUnitBallSubring_iff
      v hnonarch x).2 hx)
  · right
    have hx_gt : 1 < v x := lt_of_not_ge hx
    rw [mem_absoluteValueUnitBallSubring_iff, map_inv₀]
    exact inv_le_one_of_one_le₀ hx_gt.le

/-- The closed unit ball of a nonarchimedean absolute value, bundled as
mathlib's `ValuationSubring`. -/
def absoluteValueValuationSubring
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v) :
    ValuationSubring K :=
  ValuationSubring.ofSubring
    (absoluteValueUnitBallSubring v hnonarch)
    (absoluteValueUnitBallSubring_mem_or_inv_mem v hnonarch)

/-- Membership in the bundled valuation subring is again the closed-unit-ball
condition. -/
theorem mem_absoluteValueValuationSubring_iff
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v) (x : K) :
    x ∈ absoluteValueValuationSubring v hnonarch ↔
      v x ≤ 1 := by
  exact (ValuationSubring.mem_ofSubring
    (absoluteValueUnitBallSubring v hnonarch)
    (absoluteValueUnitBallSubring_mem_or_inv_mem v hnonarch) x).trans
    (mem_absoluteValueUnitBallSubring_iff v hnonarch x)

/-- In any submonoid of a field whose elements are exactly the closed unit
ball of an absolute value, the units are exactly the elements of absolute
value `1`. -/
theorem isUnit_iff_abs_eq_one_of_mem_iff_le_one
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    {C : Type*} [SetLike C K] [SubmonoidClass C K]
    (S : C) (hS : ∀ x : K, x ∈ S ↔ v x ≤ 1) (x : S) :
    IsUnit x ↔ v (x : K) = 1 := by
  constructor
  · intro hx
    have hx_inv :=
      (Submonoid.isUnit_iff_and (S := S) (a := x)).mp hx
    have hx_le : v (x : K) ≤ 1 := (hS (x : K)).1 x.property
    have hinv_le : v ((x : K)⁻¹) ≤ 1 :=
      (hS ((x : K)⁻¹)).1 hx_inv.2
    have hmul : v (x : K) * v ((x : K)⁻¹) = 1 := by
      rw [← v.map_mul, mul_inv_cancel₀ hx_inv.1]
      simp
    have hge : 1 ≤ v (x : K) := by
      calc
        1 = v (x : K) * v ((x : K)⁻¹) := hmul.symm
        _ ≤ v (x : K) * 1 :=
          mul_le_mul_of_nonneg_left hinv_le (v.nonneg (x : K))
        _ = v (x : K) := by simp
    exact le_antisymm hx_le hge
  · intro hx
    rw [Submonoid.isUnit_iff_and (S := S) (a := x)]
    constructor
    · intro hx_zero
      have hzero_one : (0 : ℝ) = 1 := by
        simp [hx_zero] at hx
      exact zero_ne_one hzero_one
    · exact (hS ((x : K)⁻¹)).2 <| by
        rw [map_inv₀, hx]
        simp

/-- In the same closed-unit-ball situation, nonunits are exactly the elements
of absolute value strictly less than `1`. -/
theorem not_isUnit_iff_abs_lt_one_of_mem_iff_le_one
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    {C : Type*} [SetLike C K] [SubmonoidClass C K]
    (S : C) (hS : ∀ x : K, x ∈ S ↔ v x ≤ 1) (x : S) :
    ¬ IsUnit x ↔ v (x : K) < 1 := by
  have hx_le : v (x : K) ≤ 1 := (hS (x : K)).1 x.property
  rw [isUnit_iff_abs_eq_one_of_mem_iff_le_one v S hS]
  exact hx_le.lt_iff_ne.symm

/-- The maximal ideal of the closed-unit-ball valuation subring consists
exactly of the elements of absolute value strictly less than `1`. -/
theorem absoluteValueValuationSubring_mem_maximalIdeal_iff_abs_lt_one
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (x : absoluteValueValuationSubring v hnonarch) :
    x ∈ IsLocalRing.maximalIdeal
        (absoluteValueValuationSubring v hnonarch) ↔
      v (x : K) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact not_isUnit_iff_abs_lt_one_of_mem_iff_le_one
    v (absoluteValueValuationSubring v hnonarch)
    (mem_absoluteValueValuationSubring_iff v hnonarch) x

/-- A closed-unit-ball element reduces to zero in the residue field exactly
when its absolute value is strictly less than `1`. -/
theorem absoluteValueUnitBallSubringAsValuationSubring_residue_eq_zero_iff_abs_lt_one
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (x : absoluteValueValuationSubring v hnonarch) :
    IsLocalRing.residue
        (absoluteValueValuationSubring v hnonarch) x = 0 ↔
      v (x : K) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff,
    absoluteValueValuationSubring_mem_maximalIdeal_iff_abs_lt_one]

/-- A closed-unit-ball element has nonzero residue exactly when its absolute
value is `1`. -/
theorem absoluteValueUnitBallSubringAsValuationSubring_residue_ne_zero_iff_abs_eq_one
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (x : absoluteValueValuationSubring v hnonarch) :
    IsLocalRing.residue
        (absoluteValueValuationSubring v hnonarch) x ≠ 0 ↔
      v (x : K) = 1 := by
  have hx_le : v (x : K) ≤ 1 :=
    (mem_absoluteValueValuationSubring_iff
      v hnonarch (x : K)).1 x.property
  rw [ne_eq,
    absoluteValueUnitBallSubringAsValuationSubring_residue_eq_zero_iff_abs_lt_one]
  constructor
  · intro hx
    exact le_antisymm hx_le (not_lt.mp hx)
  · intro hx
    rw [hx]
    exact not_lt_of_ge le_rfl

/-- If an absolute value on `L` extends one on `K`, then its valuation subring
pulls back to the base valuation subring. -/
theorem comap_absoluteValueUnitBallSubring_eq_of_extends
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ)
    (hvnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hwnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue w)
    (hw_ext : ∀ x : K, w (algebraMap K L x) = v x) :
    (absoluteValueUnitBallSubring w hwnonarch).comap
        (algebraMap K L) =
      absoluteValueUnitBallSubring v hvnonarch := by
  ext x
  change w (algebraMap K L x) ≤ 1 ↔ v x ≤ 1
  rw [hw_ext x]

/-- A field polynomial whose coefficients lie in the closed unit ball has a
degree-preserving lift to the actual valuation-subring bundle used for
residue fields.  The lift may be chosen coefficientwise, so the absolute
values of the lifted coefficients are the original coefficient values. -/
theorem exists_polynomial_over_absoluteValueUnitBallSubringAsValuationSubring_of_coeff_abs_le_one
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v) (f : K[X])
    (hfcoeff : ∀ n : ℕ, v (f.coeff n) ≤ 1) :
    ∃ F : (absoluteValueValuationSubring v hnonarch)[X],
      F.map (algebraMap
          (absoluteValueValuationSubring v hnonarch) K) = f ∧
        F.natDegree = f.natDegree ∧
          ∀ n : ℕ, v (F.coeff n : K) = v (f.coeff n) := by
  let V := absoluteValueValuationSubring v hnonarch
  have hlifts : f ∈ Polynomial.lifts (algebraMap V K) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact
      ⟨⟨f.coeff n,
          (mem_absoluteValueValuationSubring_iff
            v hnonarch (f.coeff n)).2 (hfcoeff n)⟩,
        by simp [V]⟩
  rcases Polynomial.exists_degree_eq_of_mem_lifts hlifts with
    ⟨F, hmap, hdegree⟩
  refine ⟨F, hmap, Polynomial.natDegree_eq_of_degree_eq hdegree, ?_⟩
  intro n
  have hcoeff :
      (F.coeff n : K) = f.coeff n := by
    have h := congrArg (fun P : K[X] => P.coeff n) hmap
    simpa [Polynomial.coeff_map, V] using h
  rw [hcoeff]

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_Basic
attribute [-instance] _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing
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

/-- A field with a chosen rank-one discrete valuation. -/
structure DVF (K : Type u) [Field K] where
  /-- The ordered multiplicative value group. -/
  ValueGroup : Type v
  /-- The ordered commutative group-with-zero structure on the value group. -/
  [instValueGroup : LinearOrderedCommGroupWithZero ValueGroup]
  /-- The chosen valuation on the field. -/
  valuation : _root_.Valuation K ValueGroup
  /-- The chosen valuation has discrete rank one. -/
  [instRankOneDiscrete : valuation.IsRankOneDiscrete]

attribute [instance] DVF.instValueGroup DVF.instRankOneDiscrete

namespace DVF

variable {K : Type u} [Field K]

/-- The valuation subring of a DVF. -/
abbrev valuationSubring (F : DVF.{u, v} K) : Type u :=
  F.valuation.valuationSubring

/-- The valuation subring of a discrete valuation field is a commutative ring. -/
instance valuationSubring.commRing (F : DVF.{u, v} K) :
    CommRing F.valuationSubring :=
  ValuationSubring.instCommRingSubtypeMem F.valuation.valuationSubring

/-- The valuation subring of a discrete valuation field is local. -/
instance valuationSubring.isLocalRing (F : DVF.{u, v} K) :
    IsLocalRing F.valuationSubring :=
  ValuationSubring.isLocalRing F.valuation.valuationSubring

/-- The maximal ideal of the valuation subring. -/
abbrev maximalIdeal (F : DVF.{u, v} K) : Ideal F.valuationSubring :=
  IsLocalRing.maximalIdeal F.valuationSubring

/-- The residue field of the valuation subring. -/
abbrev residueField (F : DVF.{u, v} K) : Type u :=
  IsLocalRing.ResidueField F.valuationSubring

/-- The residue ring of a discrete valuation field carries its canonical field structure. -/
instance residueField.field (F : DVF.{u, v} K) : Field F.residueField :=
  IsLocalRing.ResidueField.field F.valuation.valuationSubring

/-- The residue map of a DVF. -/
abbrev residueMap (F : DVF.{u, v} K) :
    RingHom F.valuationSubring F.residueField :=
  IsLocalRing.residue F.valuationSubring

/-- A uniformizer generates the maximal ideal. -/
theorem maximalIdeal_eq_span_uniformizer (F : DVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K)) :
    F.maximalIdeal = Ideal.span (Set.singleton pi) := by
  change IsLocalRing.maximalIdeal F.valuation.valuationSubring =
    Ideal.span (Set.singleton pi)
  exact Valuation.IsUniformizer.is_generator (v := F.valuation) hpi

/-- Powers of the maximal ideal are generated by powers of any chosen
uniformizer. -/
theorem maximalIdeal_pow_eq_span_uniformizer_pow (F : DVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) :
    F.maximalIdeal ^ n = Ideal.span ({pi ^ n} : Set F.valuationSubring) := by
  rw [F.maximalIdeal_eq_span_uniformizer hpi]
  exact Ideal.span_singleton_pow pi n

/-! ### Successive quotients of powers of the maximal ideal -/

/-- The submodule `m^(n+1)` inside `m^n`. -/
abbrev maximalIdealPowSuccSubmodule (F : DVF.{u, v} K) (n : ℕ) :
    Submodule F.valuationSubring ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) :=
  Submodule.comap (Submodule.subtype (p := (F.maximalIdeal ^ n : Ideal F.valuationSubring)))
    ((F.maximalIdeal ^ (n + 1) : Ideal F.valuationSubring) :
      Submodule F.valuationSubring F.valuationSubring)

/-- The additive ideal-power quotient `m^n/m^(n+1)`. -/
def MaximalIdealPowSuccQuot (F : DVF.{u, v} K) (n : ℕ) : Type u :=
  ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) ⧸
    F.maximalIdealPowSuccSubmodule n

/-- A successive maximal-ideal quotient is an additive commutative group. -/
instance maximalIdealPowSuccQuotAddCommGroup
    (F : DVF.{u, v} K) (n : ℕ) :
    AddCommGroup (F.MaximalIdealPowSuccQuot n) := by
  change AddCommGroup
    (((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) ⧸
      F.maximalIdealPowSuccSubmodule n)
  infer_instance

/-- A successive maximal-ideal quotient is a module over the valuation subring. -/
instance maximalIdealPowSuccQuotModule
    (F : DVF.{u, v} K) (n : ℕ) :
    Module F.valuationSubring (F.MaximalIdealPowSuccQuot n) := by
  change Module F.valuationSubring
    (((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) ⧸
      F.maximalIdealPowSuccSubmodule n)
  infer_instance

/-- Explicit access to the concrete submodule-quotient representation. -/
def maximalIdealPowSuccQuotConcreteLinearEquiv
    (F : DVF.{u, v} K) (n : ℕ) :
    F.MaximalIdealPowSuccQuot n ≃ₗ[F.valuationSubring]
      (((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) ⧸
        F.maximalIdealPowSuccSubmodule n) := by
  change
    (((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) ⧸
        F.maximalIdealPowSuccSubmodule n) ≃ₗ[F.valuationSubring]
      (((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) ⧸
        F.maximalIdealPowSuccSubmodule n)
  exact LinearEquiv.refl F.valuationSubring _

/-- The quotient map `m^n → m^n/m^(n+1)`. -/
def maximalIdealPowSuccQuotMk (F : DVF.{u, v} K) (n : ℕ) :
    ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) →ₗ[F.valuationSubring]
      F.MaximalIdealPowSuccQuot n := by
  change
    ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u)
      →ₗ[F.valuationSubring]
        (((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) ⧸
          F.maximalIdealPowSuccSubmodule n)
  exact Submodule.mkQ (F.maximalIdealPowSuccSubmodule n)

/-- The concrete linear equivalence sends a quotient representative to the same coset. -/
@[simp]
theorem maximalIdealPowSuccQuotConcreteLinearEquiv_mk
    (F : DVF.{u, v} K) (n : ℕ)
    (a : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u)) :
    F.maximalIdealPowSuccQuotConcreteLinearEquiv n
        (F.maximalIdealPowSuccQuotMk n a) =
      Submodule.Quotient.mk a :=
  rfl

/-- Eliminate an ideal-power quotient class through its canonical map. -/
protected theorem MaximalIdealPowSuccQuot.inductionOn
    (F : DVF.{u, v} K) (n : ℕ)
    {motive : F.MaximalIdealPowSuccQuot n → Prop}
    (q : F.MaximalIdealPowSuccQuot n)
    (h : ∀ a : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u),
      motive (F.maximalIdealPowSuccQuotMk n a)) :
    motive q := by
  change motive
    (show ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) ⧸
      F.maximalIdealPowSuccSubmodule n from q)
  refine Submodule.Quotient.induction_on
    (F.maximalIdealPowSuccSubmodule n) q ?_
  intro a
  exact h a

/-- Descend a representative-level function constant modulo `m^(n+1)`. -/
def maximalIdealPowSuccQuotLift
    (F : DVF.{u, v} K) {P : Sort*} (n : ℕ)
    (f : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) → P)
    (h : ∀ a b, a - b ∈ F.maximalIdealPowSuccSubmodule n →
      f a = f b) :
    F.MaximalIdealPowSuccQuot n → P := by
  change
    ((((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) ⧸
      F.maximalIdealPowSuccSubmodule n) → P)
  refine Quotient.lift f ?_
  intro a b hab
  have hq :
      (Submodule.Quotient.mk a :
        ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) ⧸
          F.maximalIdealPowSuccSubmodule n) =
        Submodule.Quotient.mk b :=
    Quotient.sound hab
  exact h a b
    ((Submodule.Quotient.eq (F.maximalIdealPowSuccSubmodule n)).1 hq)

/-- A lift from the successive ideal quotient evaluates on representatives by the supplied map. -/
@[simp]
theorem maximalIdealPowSuccQuotLift_mk
    (F : DVF.{u, v} K) {P : Sort*} (n : ℕ)
    (f : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) → P)
    (h : ∀ a b, a - b ∈ F.maximalIdealPowSuccSubmodule n →
      f a = f b)
    (a : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u)) :
    F.maximalIdealPowSuccQuotLift n f h
        (F.maximalIdealPowSuccQuotMk n a) = f a :=
  rfl

/-- Descend a linear map vanishing on `m^(n+1)` inside `m^n`. -/
def maximalIdealPowSuccQuotLinearLift
    (F : DVF.{u, v} K) {M : Type*} [AddCommGroup M]
    [Module F.valuationSubring M] (n : ℕ)
    (f : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u)
      →ₗ[F.valuationSubring] M)
    (h : F.maximalIdealPowSuccSubmodule n ≤ f.ker) :
    F.MaximalIdealPowSuccQuot n →ₗ[F.valuationSubring] M := by
  change
    (((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) ⧸
      F.maximalIdealPowSuccSubmodule n) →ₗ[F.valuationSubring] M
  exact (F.maximalIdealPowSuccSubmodule n).liftQ f h

/-- The linear lift from a successive ideal quotient has the prescribed value on representatives. -/
@[simp]
theorem maximalIdealPowSuccQuotLinearLift_mk
    (F : DVF.{u, v} K) {M : Type*} [AddCommGroup M]
    [Module F.valuationSubring M] (n : ℕ)
    (f : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u)
      →ₗ[F.valuationSubring] M)
    (h : F.maximalIdealPowSuccSubmodule n ≤ f.ker)
    (a : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u)) :
    F.maximalIdealPowSuccQuotLinearLift n f h
        (F.maximalIdealPowSuccQuotMk n a) = f a :=
  rfl

/-- A successive ideal-quotient class is zero exactly when its representative
lies in the next power. -/
theorem maximalIdealPowSuccQuotMk_eq_zero_iff (F : DVF.{u, v} K) (n : ℕ)
    (a : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u)) :
    F.maximalIdealPowSuccQuotMk n a = 0 ↔
      (a : F.valuationSubring) ∈ F.maximalIdeal ^ (n + 1) := by
  change (Submodule.Quotient.mk a :
    ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) ⧸
      F.maximalIdealPowSuccSubmodule n) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

/-- Two successive ideal-quotient classes agree exactly when their difference
lies in the next power. -/
@[simp]
theorem maximalIdealPowSuccQuotMk_eq_iff
    (F : DVF.{u, v} K) (n : ℕ)
    (a b : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u)) :
    F.maximalIdealPowSuccQuotMk n a =
        F.maximalIdealPowSuccQuotMk n b ↔
      a - b ∈ F.maximalIdealPowSuccSubmodule n := by
  change (Submodule.Quotient.mk a :
    ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) ⧸
      F.maximalIdealPowSuccSubmodule n) =
    Submodule.Quotient.mk b ↔ _
  exact Submodule.Quotient.eq (F.maximalIdealPowSuccSubmodule n)

/-- Multiplication by the corresponding uniformizer power lands in the required
maximal-ideal power. -/
theorem mul_uniformizer_pow_mem_maximalIdeal_pow (F : DVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (r : F.valuationSubring) :
    r * pi ^ n ∈ F.maximalIdeal ^ n := by
  rw [F.maximalIdeal_pow_eq_span_uniformizer_pow hpi n]
  rw [Ideal.mem_span_singleton]
  exact ⟨r, mul_comm _ _⟩

/-- Multiplication by `pi^n`, landing in `m^n`. -/
def maximalIdealPowMulUniformizerPowMap (F : DVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K)) (n : ℕ) :
    F.valuationSubring →ₗ[F.valuationSubring]
      ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) where
  toFun r := ⟨r * pi ^ n, F.mul_uniformizer_pow_mem_maximalIdeal_pow hpi n r⟩
  map_add' r s := by
    ext
    simp [add_mul]
  map_smul' a r := by
    ext
    simp [mul_assoc]

/-- After multiplying by a uniformizer power, next-level membership is equivalent
to maximal-ideal membership. -/
theorem mul_uniformizer_pow_mem_maximalIdeal_pow_succ_iff (F : DVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (r : F.valuationSubring) :
    r * pi ^ n ∈ F.maximalIdeal ^ (n + 1) ↔ r ∈ F.maximalIdeal := by
  rw [F.maximalIdeal_pow_eq_span_uniformizer_pow hpi (n + 1),
    F.maximalIdeal_eq_span_uniformizer hpi]
  constructor
  · intro h
    rcases (Ideal.mem_span_singleton.mp h) with ⟨c, hc⟩
    refine Ideal.mem_span_singleton.mpr ⟨c, ?_⟩
    have hpi_ne : pi ≠ 0 := by
      intro hzero
      exact hpi.ne_zero (by simpa using congrArg (fun x : F.valuationSubring => (x : K)) hzero)
    have hne : pi ^ n ≠ 0 := pow_ne_zero n hpi_ne
    have hcancel : r * pi ^ n = (pi * c) * pi ^ n := by
      calc
        r * pi ^ n = pi ^ (n + 1) * c := hc
        _ = (pi * c) * pi ^ n := by
          rw [pow_succ']
          ring
    exact mul_right_cancel₀ hne hcancel
  · intro h
    rcases (Ideal.mem_span_singleton.mp h) with ⟨c, hc⟩
    refine Ideal.mem_span_singleton.mpr ⟨c, ?_⟩
    rw [hc]
    rw [pow_succ']
    ring

/-- The map `O → m^n/m^(n+1)` induced by multiplication by `pi^n`. -/
def maximalIdealPowSuccQuotMulUniformizerPowMap (F : DVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K)) (n : ℕ) :
    F.valuationSubring →ₗ[F.valuationSubring] F.MaximalIdealPowSuccQuot n :=
  (F.maximalIdealPowSuccQuotMk n).comp
    (F.maximalIdealPowMulUniformizerPowMap hpi n)

/-- The kernel of multiplication by a uniformizer power is the residue-level defining submodule. -/
theorem maximalIdealPowSuccQuotMulUniformizerPowMap_ker (F : DVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K)) (n : ℕ) :
    LinearMap.ker (F.maximalIdealPowSuccQuotMulUniformizerPowMap hpi n) =
      F.maximalIdeal := by
  ext r
  rw [LinearMap.mem_ker]
  change F.maximalIdealPowSuccQuotMk n
      (F.maximalIdealPowMulUniformizerPowMap hpi n r) = 0 ↔
    r ∈ F.maximalIdeal
  rw [F.maximalIdealPowSuccQuotMk_eq_zero_iff n]
  change r * pi ^ n ∈ F.maximalIdeal ^ (n + 1) ↔ r ∈ F.maximalIdeal
  exact F.mul_uniformizer_pow_mem_maximalIdeal_pow_succ_iff hpi n r

/-- Multiplication by a uniformizer power surjects onto the successive ideal quotient. -/
theorem maximalIdealPowSuccQuotMulUniformizerPowMap_surjective (F : DVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K)) (n : ℕ) :
    Function.Surjective (F.maximalIdealPowSuccQuotMulUniformizerPowMap hpi n) := by
  intro x
  refine MaximalIdealPowSuccQuot.inductionOn F n
    (motive := fun x' ↦
      ∃ a, F.maximalIdealPowSuccQuotMulUniformizerPowMap hpi n a = x') x ?_
  intro a
  have ha_span : (a : F.valuationSubring) ∈
      Ideal.span ({pi ^ n} : Set F.valuationSubring) := by
    simpa [F.maximalIdeal_pow_eq_span_uniformizer_pow hpi n] using a.2
  rcases (Ideal.mem_span_singleton.mp ha_span) with ⟨r, hr⟩
  refine ⟨r, ?_⟩
  change F.maximalIdealPowSuccQuotMk n
      (F.maximalIdealPowMulUniformizerPowMap hpi n r) =
    F.maximalIdealPowSuccQuotMk n a
  have hrep : F.maximalIdealPowMulUniformizerPowMap hpi n r = a := by
    ext
    simp [maximalIdealPowMulUniformizerPowMap, hr, mul_comm]
  rw [hrep]

/-- Principal-ideal scaling: multiplication by `pi^n` identifies
`O/m` linearly with `m^n/m^(n+1)`. -/
noncomputable def residueLinearEquivMaximalIdealPowSuccQuotOfUniformizer
    (F : DVF.{u, v} K) {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K)) (n : ℕ) :
    F.residueField ≃ₗ[F.valuationSubring] F.MaximalIdealPowSuccQuot n :=
  (Submodule.quotEquivOfEq (F.maximalIdeal : Submodule F.valuationSubring F.valuationSubring)
      (LinearMap.ker (F.maximalIdealPowSuccQuotMulUniformizerPowMap hpi n))
      (F.maximalIdealPowSuccQuotMulUniformizerPowMap_ker hpi n).symm).trans
    ((F.maximalIdealPowSuccQuotMulUniformizerPowMap hpi n).quotKerEquivOfSurjective
      (F.maximalIdealPowSuccQuotMulUniformizerPowMap_surjective hpi n))

/-- Additive form of `O/m ≃ m^n/m^(n+1)`. -/
noncomputable def residueAddEquivMaximalIdealPowSuccQuotOfUniformizer
    (F : DVF.{u, v} K) {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K)) (n : ℕ) :
    F.residueField ≃+ F.MaximalIdealPowSuccQuot n :=
  (F.residueLinearEquivMaximalIdealPowSuccQuotOfUniformizer hpi n).toAddEquiv

/-- The residue-to-graded-piece equivalence sends a residue class to its
uniformizer-scaled quotient class. -/
@[simp] theorem residueAddEquivMaximalIdealPowSuccQuotOfUniformizer_residue
    (F : DVF.{u, v} K) {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K)) (n : ℕ)
    (r : F.valuationSubring) :
    F.residueAddEquivMaximalIdealPowSuccQuotOfUniformizer hpi n
        (F.residueMap r) =
      F.maximalIdealPowSuccQuotMulUniformizerPowMap hpi n r := by
  let f := F.maximalIdealPowSuccQuotMulUniformizerPowMap hpi n
  let hker :
      (F.maximalIdeal : Submodule F.valuationSubring F.valuationSubring) =
        LinearMap.ker f :=
    (F.maximalIdealPowSuccQuotMulUniformizerPowMap_ker hpi n).symm
  change (Submodule.quotEquivOfEq
        (F.maximalIdeal : Submodule F.valuationSubring F.valuationSubring)
        (LinearMap.ker f) hker).trans
      (f.quotKerEquivOfSurjective
        (F.maximalIdealPowSuccQuotMulUniformizerPowMap_surjective hpi n))
      (Submodule.Quotient.mk r) = f r
  rw [LinearEquiv.trans_apply]
  have hquot :
      Submodule.quotEquivOfEq
          (F.maximalIdeal : Submodule F.valuationSubring F.valuationSubring)
          (LinearMap.ker f) hker (Submodule.Quotient.mk r) =
        (Submodule.Quotient.mk r :
          F.valuationSubring ⧸ LinearMap.ker f) := by
    exact Submodule.quotEquivOfEq_mk
      (p := (F.maximalIdeal : Submodule F.valuationSubring F.valuationSubring))
      (p' := LinearMap.ker f) hker r
  rw [hquot]
  rw [LinearMap.quotKerEquivOfSurjective_apply_mk]

end DVF
end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_Henselian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ValuationTheory

/-!
# Henselian discretely valued fields

This file contains the lightweight package for a discretely valued field whose
valuation ring is Henselian at its maximal ideal.
-/

noncomputable section

universe u v

namespace DiscreteValuationField

/-- A Henselian discretely valued field. -/
structure HenselianDVF (K : Type u) [Field K] extends DVF.{u, v} K where
  /-- The valuation ring is Henselian along its maximal ideal. -/
  [instHenselian : HenselianRing toDVF.valuationSubring toDVF.maximalIdeal]

attribute [instance] HenselianDVF.instHenselian

namespace HenselianDVF

variable {K : Type u} [Field K]

/-- Introduces the abbreviation `valuationSubring`. -/
abbrev valuationSubring (F : HenselianDVF.{u, v} K) : Type u :=
  F.toDVF.valuationSubring

end HenselianDVF

end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_Complete
attribute [-instance] _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing
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

variable {K : Type u} [Field K]
variable {Gamma : Type v} [LinearOrderedCommGroupWithZero Gamma]

/-- A complete discrete valuation. -/
class IsCompleteDiscrete (val : _root_.Valuation K Gamma) : Prop where
  /-- A complete discrete valuation has discrete rank one. -/
  [isRankOneDiscrete : val.IsRankOneDiscrete]
  /-- The valuation ring is complete for its maximal-ideal adic topology. -/
  isAdicComplete :
    IsAdicComplete (IsLocalRing.maximalIdeal val.valuationSubring) val.valuationSubring

attribute [instance] IsCompleteDiscrete.isRankOneDiscrete

/-- Completeness of the valued field implies adic completeness of its valuation subring. -/
theorem isAdicComplete (val : _root_.Valuation K Gamma) [IsCompleteDiscrete val] :
    IsAdicComplete (IsLocalRing.maximalIdeal val.valuationSubring) val.valuationSubring :=
  IsCompleteDiscrete.isAdicComplete (val := val)

/-- The valuation subring of a complete discrete valuation field is henselian. -/
theorem henselianRing (val : _root_.Valuation K Gamma) [IsCompleteDiscrete val] :
    HenselianRing val.valuationSubring (IsLocalRing.maximalIdeal val.valuationSubring) := by
  let : IsAdicComplete (IsLocalRing.maximalIdeal val.valuationSubring)
      val.valuationSubring := isAdicComplete val
  infer_instance

end Valuation

/-- A field with a chosen complete rank-one discrete valuation. -/
structure CompleteDVF (K : Type u) [Field K] where
  /-- The ordered multiplicative value group. -/
  ValueGroup : Type v
  /-- The ordered commutative group-with-zero structure on the value group. -/
  [instValueGroup : LinearOrderedCommGroupWithZero ValueGroup]
  /-- The chosen valuation on the field. -/
  valuation : _root_.Valuation K ValueGroup
  /-- The chosen valuation is complete and discretely rank one. -/
  [instCompleteDiscrete : Valuation.IsCompleteDiscrete valuation]

attribute [instance] CompleteDVF.instValueGroup CompleteDVF.instCompleteDiscrete

namespace CompleteDVF

variable {K : Type u} [Field K]

/-- A complete DVF is Henselian.  This is the canonical forgetful projection:
all weaker DVF data are obtained through this object. -/
abbrev toHenselianDVF (F : CompleteDVF.{u, v} K) : HenselianDVF.{u, v} K where
  toDVF :=
    { ValueGroup := F.ValueGroup
      valuation := F.valuation }
  instHenselian := by
    change HenselianRing F.valuation.valuationSubring
      (IsLocalRing.maximalIdeal F.valuation.valuationSubring)
    exact Valuation.henselianRing F.valuation

/-- The underlying DVF, obtained along the canonical
`CompleteDVF -> HenselianDVF -> DVF` path. -/
abbrev toDVF (F : CompleteDVF.{u, v} K) : DVF.{u, v} K :=
  F.toHenselianDVF.toDVF

/-- Introduces the abbreviation `valuationSubring`. -/
abbrev valuationSubring (F : CompleteDVF.{u, v} K) : Type u :=
  F.toHenselianDVF.valuationSubring

end CompleteDVF
end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_ResidueField
attribute [-instance] _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ValuationTheory

/-!
# Residue-field API for local maps

This file adds reusable local-ring residue-field lemmas that are used by the
Henselian and unramified parts of the DVF library.  It keeps mathlib's
`IsLocalRing.ResidueField.map` and `IsLocalRing.residue` as the primary
objects.
-/

noncomputable section

universe u v w

namespace DiscreteValuationField
namespace ResidueField

variable {R : Type u} {S : Type v} {T : Type w}

section LocalRing

variable [CommRing R] [IsLocalRing R]

/-- Equality in the residue field is equality modulo the maximal ideal. -/
theorem residue_eq_residue_iff_sub_mem_maximalIdeal (x y : R) :
    IsLocalRing.residue R x = IsLocalRing.residue R y ↔
      x - y ∈ IsLocalRing.maximalIdeal R := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]

end LocalRing

section LocalHom

variable [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
variable (f : R →+* S) [IsLocalHom f]

/-- A local homomorphism pulls back the target maximal ideal to the source
maximal ideal. -/
theorem comap_maximalIdeal_eq :
    (IsLocalRing.maximalIdeal S).comap f = IsLocalRing.maximalIdeal R :=
  IsLocalRing.maximalIdeal_comap f

/-- A local homomorphism induces an injective map on residue fields. -/
theorem map_injective :
    Function.Injective (IsLocalRing.ResidueField.map f) := by
  intro x y hxy
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
  obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective y
  rw [IsLocalRing.ResidueField.map_residue,
    IsLocalRing.ResidueField.map_residue] at hxy
  rw [residue_eq_residue_iff_sub_mem_maximalIdeal]
  have hsubS : f (r - s) ∈ IsLocalRing.maximalIdeal S := by
    rw [map_sub]
    exact
      (residue_eq_residue_iff_sub_mem_maximalIdeal
        (R := S) (f r) (f s)).1 hxy
  have hpre : r - s ∈ (IsLocalRing.maximalIdeal S).comap f := hsubS
  rwa [comap_maximalIdeal_eq f] at hpre

/-- The residue-field isomorphism induced by a surjective residue-field map
coming from a local homomorphism. -/
noncomputable def ringEquivOfSurjective
    (hsurj : Function.Surjective (IsLocalRing.ResidueField.map f)) :
    IsLocalRing.ResidueField R ≃+* IsLocalRing.ResidueField S :=
  RingEquiv.ofBijective (IsLocalRing.ResidueField.map f)
    ⟨map_injective f, hsurj⟩

/-- The residue-ring equivalence induced by a surjective map evaluates by that map. -/
@[simp]
theorem ringEquivOfSurjective_apply
    (hsurj : Function.Surjective (IsLocalRing.ResidueField.map f))
    (x : IsLocalRing.ResidueField R) :
    ringEquivOfSurjective f hsurj x =
      IsLocalRing.ResidueField.map f x :=
  rfl

end LocalHom

section Algebra

variable [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
variable [Algebra R S] [IsLocalHom (algebraMap R S)]

/-- For a local algebra map, mathlib's residue-field algebra map agrees with
the residue-field map induced by the structure homomorphism. -/
theorem algebraMap_eq_map_algebraMap :
    algebraMap (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField S) =
      IsLocalRing.ResidueField.map (algebraMap R S) := by
  ext x
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
  simp [IsLocalRing.ResidueField.map_residue,
    IsLocalRing.ResidueField.algebraMap_residue]

/-- The residue-field map induced by a local algebra map is injective. -/
theorem map_algebraMap_injective :
    Function.Injective
      (IsLocalRing.ResidueField.map (algebraMap R S)) :=
  map_injective (algebraMap R S)

end Algebra

end ResidueField
end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_Extensions
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

/-- The field degree of a finite valued extension. -/
def degree (_base : DVF.{u, v} K) (_target : DVF.{w, x} L) : ℕ :=
  Module.finrank K L

omit [FiniteDimensional K L]
    [base.valuation.HasExtension target.valuation] in
/-- The degree of a finite extension of discrete valuation fields is its linear `finrank`. -/
@[simp] theorem degree_eq_finrank :
    degree base target = Module.finrank K L :=
  rfl

/-- The induced map between valuation subrings. -/
def integerMap :
    base.valuationSubring →+* target.valuationSubring :=
  algebraMap base.valuationSubring target.valuationSubring

omit [FiniteDimensional K L] in
/-- The valuation-subring map evaluates through the ambient algebra map. -/
@[simp] theorem integerMap_apply (a : base.valuationSubring) :
    (((integerMap base target) a : target.valuationSubring) : L) =
      algebraMap K L (a : K) := by
  change ((algebraMap base.valuation.valuationSubring
    target.valuation.valuationSubring) a : L) = algebraMap K L (a : K)
  rfl

/-- The induced map on residue fields. -/
def residueMap :
    base.residueField →+* target.residueField :=
  algebraMap base.residueField target.residueField

omit [FiniteDimensional K L] in
/-- The residue-field map sends the residue of an integer to its target residue. -/
@[simp] theorem residueMap_residue (a : base.valuationSubring) :
    residueMap base target (base.residueMap a) =
      target.residueMap (integerMap base target a) := by
  change
    (algebraMap
      (_root_.IsLocalRing.ResidueField base.valuation.valuationSubring)
      (_root_.IsLocalRing.ResidueField target.valuation.valuationSubring))
      (_root_.IsLocalRing.residue base.valuation.valuationSubring a) =
    _root_.IsLocalRing.residue target.valuation.valuationSubring
      ((algebraMap base.valuation.valuationSubring
        target.valuation.valuationSubring) a)
  rfl

omit [FiniteDimensional K L] in
/-- The residue-field map of a valued extension is injective. -/
theorem residueMap_injective :
    Function.Injective (residueMap base target) := by
  change Function.Injective
    (algebraMap
      (_root_.IsLocalRing.ResidueField base.valuation.valuationSubring)
      (_root_.IsLocalRing.ResidueField target.valuation.valuationSubring))
  rw [ValuationTheory.DiscreteValuationField.ResidueField.algebraMap_eq_map_algebraMap]
  exact ValuationTheory.DiscreteValuationField.ResidueField.map_algebraMap_injective

omit [FiniteDimensional K L] in
/-- Surjectivity of the residue map upgrades its canonical injectivity to
bijectivity. -/
theorem residueMap_bijective_of_surjective
    (hSurj : Function.Surjective (residueMap base target)) :
    Function.Bijective (residueMap base target) :=
  ⟨residueMap_injective base target, hSurj⟩

omit [FiniteDimensional K L] in
/-- The residue-field isomorphism attached to a surjective residue map. -/
noncomputable def residueFieldEquivOfSurjective
    (hSurj : Function.Surjective (residueMap base target)) :
    base.residueField ≃+* target.residueField :=
  RingEquiv.ofBijective (residueMap base target)
    (residueMap_bijective_of_surjective base target hSurj)

omit [FiniteDimensional K L] in
/-- The residue-field equivalence induced by surjectivity evaluates by the residue map. -/
@[simp] theorem residueFieldEquivOfSurjective_apply
    (hSurj : Function.Surjective (residueMap base target))
    (z : base.residueField) :
    residueFieldEquivOfSurjective base target hSurj z =
      residueMap base target z :=
  rfl

omit [FiniteDimensional K L] in
/-- The inverse residue-field equivalence recovers a source class after applying the residue map. -/
@[simp] theorem residueFieldEquivOfSurjective_symm_apply_residueMap
    (hSurj : Function.Surjective (residueMap base target))
    (z : base.residueField) :
    (residueFieldEquivOfSurjective base target hSurj).symm
        (residueMap base target z) = z := by
  simpa using
    (residueFieldEquivOfSurjective base target hSurj).symm_apply_apply z

omit [FiniteDimensional K L] in
/-- Applying the residue map after the inverse residue-field equivalence recovers
the target class. -/
@[simp] theorem residueMap_residueFieldEquivOfSurjective_symm_apply
    (hSurj : Function.Surjective (residueMap base target))
    (z : target.residueField) :
    residueMap base target
        ((residueFieldEquivOfSurjective base target hSurj).symm z) = z :=
  (residueFieldEquivOfSurjective base target hSurj).apply_symm_apply z

/-- The induced map on unit groups of valuation rings. -/
def unitMap :
    base.valuationSubringˣ →* target.valuationSubringˣ :=
  Units.map (integerMap base target).toMonoidHom

omit [FiniteDimensional K L] in
/-- The induced unit map agrees with the valuation-ring map on underlying elements. -/
@[simp] theorem unitMap_apply (a : base.valuationSubringˣ) :
    ((unitMap base target a : target.valuationSubringˣ) :
        target.valuationSubring) =
      integerMap base target (a : base.valuationSubring) :=
  rfl

omit [FiniteDimensional K L] in
/-- The induced map on residue-field units is injective. -/
theorem residueUnitsMap_injective :
    Function.Injective
      (Units.map (residueMap base target).toMonoidHom) :=
  Units.map_injective (residueMap_injective base target)

omit [FiniteDimensional K L] in
/-- Surjectivity of the residue map implies surjectivity on residue-field units. -/
theorem residueUnitsMap_surjective_of_residueMap_surjective
    (hSurj : Function.Surjective (residueMap base target)) :
    Function.Surjective
      (Units.map (residueMap base target).toMonoidHom) := by
  intro y
  obtain ⟨z, hz⟩ := hSurj (y : target.residueField)
  have hz0 : z ≠ 0 := by
    intro h
    exact y.ne_zero (by simpa [h] using hz.symm)
  refine ⟨Units.mk0 z hz0, ?_⟩
  apply Units.ext
  simpa using hz

omit [FiniteDimensional K L] in
/-- A surjective residue map induces a bijection on residue-field units. -/
theorem residueUnitsMap_bijective_of_residueMap_surjective
    (hSurj : Function.Surjective (residueMap base target)) :
    Function.Bijective
      (Units.map (residueMap base target).toMonoidHom) :=
  ⟨residueUnitsMap_injective base target,
    residueUnitsMap_surjective_of_residueMap_surjective base target hSurj⟩

omit [FiniteDimensional K L] in
/-- The unit-group equivalence induced by a surjective residue map. -/
noncomputable def residueUnitsEquivOfResidueMapSurjective
    (hSurj : Function.Surjective (residueMap base target)) :
    base.residueFieldˣ ≃* target.residueFieldˣ :=
  MulEquiv.ofBijective (Units.map (residueMap base target).toMonoidHom)
    (residueUnitsMap_bijective_of_residueMap_surjective
      base target hSurj)

omit [FiniteDimensional K L] in
/-- The residue-unit equivalence evaluates by the induced residue-unit map. -/
@[simp] theorem residueUnitsEquivOfResidueMapSurjective_apply
    (hSurj : Function.Surjective (residueMap base target))
    (a : base.residueFieldˣ) :
    residueUnitsEquivOfResidueMapSurjective base target hSurj a =
      Units.map (residueMap base target).toMonoidHom a :=
  rfl

omit [FiniteDimensional K L] in
/-- The residue-field equivalence sends a source residue to the corresponding target residue. -/
@[simp] theorem residueFieldEquivOfSurjective_apply_residue
    (hSurj : Function.Surjective (residueMap base target))
    (a : base.valuationSubring) :
    residueFieldEquivOfSurjective base target hSurj (base.residueMap a) =
      target.residueMap (integerMap base target a) := by
  rw [residueFieldEquivOfSurjective_apply,
    residueMap_residue]

omit [FiniteDimensional K L] in
/-- The inverse residue-field equivalence sends a target residue back to its source residue. -/
@[simp] theorem residueFieldEquivOfSurjective_symm_apply_target_residue
    (hSurj : Function.Surjective (residueMap base target))
    (a : base.valuationSubring) :
    (residueFieldEquivOfSurjective base target hSurj).symm
        (target.residueMap (integerMap base target a)) =
      base.residueMap a := by
  rw [← residueMap_residue base target,
    residueFieldEquivOfSurjective_symm_apply_residueMap]

end ValuedExtension
end DiscreteValuationField
end
end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_ChevalleyExtension
attribute [-instance] _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing
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

/-- Exact pullback of valuation subrings gives a `HasExtension` proof for the
canonical valuation attached to the target valuation subring. -/
theorem hasExtension_valuation_of_valuationSubring_pullback
    (vK : _root_.Valuation K ΓK) (B : ValuationSubring L)
    (hpullback : ∀ x : K, algebraMap K L x ∈ B.toSubring ↔
      x ∈ vK.valuationSubring) :
    vK.HasExtension B.valuation := by
  apply _root_.Valuation.HasExtension.ofComapInteger
  apply le_antisymm
  · intro x hx
    have hxB : algebraMap K L x ∈ B.toSubring := by
      exact B.mem_of_valuation_le_one _ hx
    have hxA : x ∈ vK.valuationSubring := (hpullback x).1 hxB
    exact (vK.mem_integer_iff x).2
      ((vK.mem_valuationSubring_iff x).2 hxA)
  · intro x hx
    have hxA : x ∈ vK.valuationSubring := by
      exact (vK.mem_valuationSubring_iff x).1
        ((vK.mem_integer_iff x).1 hx)
    have hxB : algebraMap K L x ∈ B.toSubring := (hpullback x).2 hxA
    exact (B.valuation_le_one_iff (algebraMap K L x)).2 hxB

/-- Every element integral over the base valuation ring lies in any valuation
ring extending the base valuation.  This is the valuation-theoretic integral
closure bridge used before specializing to complete or Henselian DVFs. -/
theorem integralClosure_mem_valuationSubring_of_hasExtension
    {ΓL : Type x} [LinearOrderedCommGroupWithZero ΓL]
    (vK : _root_.Valuation K ΓK) (vL : _root_.Valuation L ΓL)
    [vK.HasExtension vL] (z : integralClosure vK.valuationSubring L) :
    (z : L) ∈ vL.valuationSubring := by
  have hz_base : IsIntegral vK.valuationSubring (z : L) :=
    z.2
  have hz_target : IsIntegral vL.valuationSubring (z : L) :=
    IsIntegral.tower_top (A := vL.valuationSubring) hz_base
  exact _root_.Valuation.Integers.mem_of_integral
    (_root_.Valuation.valuationSubring.integers (v := vL)) hz_target

/-- The actual integral closure over the base valuation ring has exact
pullback to the base field: a base-field element is integral over the base
valuation ring in the extension field exactly when it already belongs to the
base valuation ring.

This is the construction-level input needed to turn the actual integral
closure into a valuation subring extending `vK` once the Henselian frontier
proves the valuative dichotomy for that integral closure. -/
theorem algebraMap_mem_integralClosure_valuationSubring_iff
    (vK : _root_.Valuation K ΓK) (a : K) :
    algebraMap K L a ∈ (integralClosure vK.valuationSubring L).toSubring ↔
      a ∈ vK.valuationSubring := by
  let A := vK.valuationSubring
  constructor
  · intro ha
    have ha_integral_L : IsIntegral A (algebraMap K L a) := ha
    have ha_integral_K : IsIntegral A a := by
      let f : K →ₐ[A] L := IsScalarTower.toAlgHom A K L
      exact (isIntegral_algHom_iff f (RingHom.injective _)).mp ha_integral_L
    have hclosed : IsIntegrallyClosedIn A K :=
      (isIntegrallyClosed_iff_isIntegrallyClosedIn (R := A) (K := K)).mp
        inferInstance
    let : IsIntegrallyClosedIn A K := hclosed
    rcases IsIntegrallyClosedIn.algebraMap_eq_of_integral
        (R := A) (A := K) ha_integral_K with
      ⟨b, hb⟩
    rw [← hb]
    exact b.2
  · intro ha
    change algebraMap A L (⟨a, ha⟩ : A) ∈
      (integralClosure A L).toSubring
    exact algebraMap_mem (integralClosure A L) (⟨a, ha⟩ : A)

/-- If the actual integral closure over the base valuation ring satisfies the
valuation-ring dichotomy inside the extension field, then it is the underlying
subring of an actual `ValuationSubring L`.

This is not a replacement for the Henselian uniqueness theorem: the remaining
frontier is to prove the dichotomy from Henselian hypotheses.  The theorem
constructs the valuation object that that proof will feed into. -/
def integralClosureValuationSubringOfMemOrInv
    (vK : _root_.Valuation K ΓK)
    (hval :
      ∀ z : L,
        z ∈ (integralClosure vK.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure vK.valuationSubring L).toSubring) :
    ValuationSubring L :=
  ValuationSubring.ofSubring
    (integralClosure vK.valuationSubring L).toSubring hval

/-- The Chevalley valuation ring contains every integral element or its inverse. -/
@[simp] theorem mem_integralClosureValuationSubringOfMemOrInv
    (vK : _root_.Valuation K ΓK)
    (hval :
      ∀ z : L,
        z ∈ (integralClosure vK.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure vK.valuationSubring L).toSubring)
    (z : L) :
    z ∈ integralClosureValuationSubringOfMemOrInv (L := L) vK hval ↔
      z ∈ (integralClosure vK.valuationSubring L).toSubring :=
  ValuationSubring.mem_ofSubring _ _ z

/-- The valuation subring built from the actual integral closure has exact
base-field pullback. -/
theorem integralClosureValuationSubringOfMemOrInv_pullback
    (vK : _root_.Valuation K ΓK)
    (hval :
      ∀ z : L,
        z ∈ (integralClosure vK.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure vK.valuationSubring L).toSubring)
    (a : K) :
    algebraMap K L a ∈
        integralClosureValuationSubringOfMemOrInv (L := L) vK hval ↔
      a ∈ vK.valuationSubring := by
  rw [mem_integralClosureValuationSubringOfMemOrInv]
  exact algebraMap_mem_integralClosure_valuationSubring_iff (L := L) vK a

/-- Once the actual integral closure over the base valuation ring has been
proved to be a valuation subring, its canonical valuation is an extension of
the base valuation. -/
theorem integralClosureValuationSubringOfMemOrInv_hasExtension
    (vK : _root_.Valuation K ΓK)
    (hval :
      ∀ z : L,
        z ∈ (integralClosure vK.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure vK.valuationSubring L).toSubring) :
    vK.HasExtension
      (integralClosureValuationSubringOfMemOrInv (L := L) vK hval).valuation := by
  exact hasExtension_valuation_of_valuationSubring_pullback vK
    (integralClosureValuationSubringOfMemOrInv (L := L) vK hval)
    (integralClosureValuationSubringOfMemOrInv_pullback (L := L) vK hval)

/-- The valuation subring built from the actual integral closure is the actual
integral closure of the base valuation ring in the extension field.

This removes the earlier packaging gap: after the Henselian frontier supplies
the valuative dichotomy for `integralClosure vK.valuationSubring L`, the
constructed valuation subring carries the canonical extension valuation and
satisfies the defining `IsIntegralClosure` equivalence, not merely equality of
underlying subrings. -/
theorem integralClosureValuationSubringOfMemOrInv_isIntegralClosure
    (vK : _root_.Valuation K ΓK)
    (hval :
      ∀ z : L,
        z ∈ (integralClosure vK.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure vK.valuationSubring L).toSubring) :
    let B := integralClosureValuationSubringOfMemOrInv (L := L) vK hval
    letI : vK.HasExtension B.valuation :=
      integralClosureValuationSubringOfMemOrInv_hasExtension (L := L) vK hval
    IsIntegralClosure B vK.valuationSubring L := by
  let B := integralClosureValuationSubringOfMemOrInv (L := L) vK hval
  let : vK.HasExtension B.valuation :=
    integralClosureValuationSubringOfMemOrInv_hasExtension (L := L) vK hval
  change IsIntegralClosure B vK.valuationSubring L
  refine
    { algebraMap_injective := Subtype.coe_injective
      isIntegral_iff := ?_ }
  intro z
  constructor
  · intro hz
    refine ⟨⟨z, ?_⟩, ?_⟩
    · exact
        (mem_integralClosureValuationSubringOfMemOrInv
          (L := L) vK hval z).2 hz
    · rfl
  · rintro ⟨y, rfl⟩
    exact
      (mem_integralClosureValuationSubringOfMemOrInv
        (L := L) vK hval (y : L)).1 y.2

/-- The integral-closure valuation subring is contained in every valuation
subring whose canonical valuation extends the base valuation. -/
theorem integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
    {ΓL : Type x} [LinearOrderedCommGroupWithZero ΓL]
    (vK : _root_.Valuation K ΓK) (vL : _root_.Valuation L ΓL)
    (hval :
      ∀ z : L,
        z ∈ (integralClosure vK.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure vK.valuationSubring L).toSubring)
    [vK.HasExtension vL] :
    integralClosureValuationSubringOfMemOrInv (L := L) vK hval ≤
      vL.valuationSubring := by
  intro z hz
  have hz_integral :
      z ∈ (integralClosure vK.valuationSubring L).toSubring := by
    exact
      (mem_integralClosureValuationSubringOfMemOrInv
        (L := L) vK hval z).1 hz
  exact integralClosure_mem_valuationSubring_of_hasExtension
    (L := L) vK vL ⟨z, hz_integral⟩

/-- A valuation overring of a valuation subring is equal to it when the
corresponding localization prime is the maximal ideal of the smaller valuation
subring.  This is the prime-theoretic comparison bridge used after proving
that an integral closure has a unique prime above the base maximal ideal. -/
theorem valuationSubring_eq_of_le_of_idealOfLE_eq_maximalIdeal
    (R S : ValuationSubring L) (hRS : R ≤ S)
    (hcenter :
      ValuationSubring.idealOfLE R S hRS = IsLocalRing.maximalIdeal R) :
    S = R := by
  have hcenter_self :
      ValuationSubring.idealOfLE R R le_rfl = IsLocalRing.maximalIdeal R := by
    change (IsLocalRing.maximalIdeal R).comap (R.inclusion R le_rfl) =
      IsLocalRing.maximalIdeal R
    ext x
    rfl
  have hle :
      ValuationSubring.idealOfLE R R le_rfl ≤
        ValuationSubring.idealOfLE R S hRS := by
    intro x hx
    rw [hcenter_self] at hx
    rw [hcenter]
    exact hx
  have hOfPrime :
      ValuationSubring.ofPrime R (ValuationSubring.idealOfLE R S hRS) ≤
        ValuationSubring.ofPrime R (ValuationSubring.idealOfLE R R le_rfl) :=
    ValuationSubring.ofPrime_le_of_le (A := R)
      (ValuationSubring.idealOfLE R R le_rfl)
      (ValuationSubring.idealOfLE R S hRS) hle
  have hSR : S ≤ R := by
    intro x hx
    have hx' :
        x ∈ ValuationSubring.ofPrime R
          (ValuationSubring.idealOfLE R S hRS) := by
      rwa [ValuationSubring.ofPrime_idealOfLE R S hRS]
    have hx'' := hOfPrime hx'
    rwa [ValuationSubring.ofPrime_idealOfLE R R le_rfl] at hx''
  exact le_antisymm hSR hRS

end Valuation
end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_IntegralClosure
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

omit [FiniteDimensional K L] in
/-- Every element integral over the base valuation ring lies in any valuation
ring extending the base valuation.  This is the construction-level inclusion
from the actual integral closure into an extension valuation ring. -/
theorem integralClosure_mem_target_valuationSubring_of_hasExtension
    (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
    [base.valuation.HasExtension target.valuation]
    [IsScalarTower base.toDVF.valuationSubring target.toDVF.valuationSubring L]
    (z : integralClosure base.toDVF.valuationSubring L) :
    (z : L) ∈ target.valuation.valuationSubring := by
  have hz_base : IsIntegral base.toDVF.valuationSubring (z : L) :=
    z.2
  have hz_target : IsIntegral target.toDVF.valuationSubring (z : L) :=
    IsIntegral.tower_top (A := target.toDVF.valuationSubring) hz_base
  exact Valuation.Integers.mem_of_integral
    (Valuation.valuationSubring.integers (v := target.valuation)) hz_target

/-- The canonical map from the actual integral closure of the base valuation
ring in `L` to any valuation ring extending the base valuation. -/
def integralClosureToTargetValuationSubringOfHasExtension
    (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
    [base.valuation.HasExtension target.valuation]
    [IsScalarTower base.toDVF.valuationSubring target.toDVF.valuationSubring L] :
    integralClosure base.toDVF.valuationSubring L →+* target.toDVF.valuationSubring where
  toFun z :=
    ⟨(z : L),
      integralClosure_mem_target_valuationSubring_of_hasExtension
        (K := K) (L := L) base target z⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' z₁ z₂ := by ext; simp
  map_mul' z₁ z₂ := by ext; simp

omit [FiniteDimensional K L] in
/-- The map from the integral closure to the target valuation ring uses the ambient inclusion. -/
@[simp] theorem integralClosureToTargetValuationSubringOfHasExtension_apply
    (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
    [base.valuation.HasExtension target.valuation]
    [IsScalarTower base.toDVF.valuationSubring target.toDVF.valuationSubring L]
    (z : integralClosure base.toDVF.valuationSubring L) :
    ((integralClosureToTargetValuationSubringOfHasExtension
      (K := K) (L := L) base target z : target.toDVF.valuationSubring) : L) = z :=
  rfl

omit [FiniteDimensional K L] in
/-- The canonical map from the integral closure to an extension valuation ring
is injective. -/
theorem integralClosureToTargetValuationSubringOfHasExtension_injective
    (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
    [base.valuation.HasExtension target.valuation]
    [IsScalarTower base.toDVF.valuationSubring target.toDVF.valuationSubring L] :
    Function.Injective
      (integralClosureToTargetValuationSubringOfHasExtension
        (K := K) (L := L) base target) := by
  intro z₁ z₂ hz
  apply Subtype.ext
  exact congrArg (fun z : target.toDVF.valuationSubring => (z : L)) hz

omit [FiniteDimensional K L] in
/-- Under module-finiteness of the extension valuation ring over the base
valuation ring, every target valuation-ring element is integral over the base
valuation ring. -/
theorem target_valuationSubring_mem_integralClosure_of_moduleFinite
    (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.toDVF.valuationSubring target.toDVF.valuationSubring]
    [IsScalarTower base.toDVF.valuationSubring target.toDVF.valuationSubring L]
    (z : target.toDVF.valuationSubring) :
    (z : L) ∈ integralClosure base.toDVF.valuationSubring L := by
  have hz_target : IsIntegral base.toDVF.valuationSubring z :=
    IsIntegral.of_finite base.toDVF.valuationSubring z
  have hz_L : IsIntegral base.toDVF.valuationSubring
      (algebraMap target.toDVF.valuationSubring L z) :=
    hz_target.map
      (IsScalarTower.toAlgHom base.toDVF.valuationSubring target.toDVF.valuationSubring L)
  rw [mem_integralClosure_iff]
  simpa using hz_L

/-- The canonical map from a finite extension valuation ring into the actual
integral closure of the base valuation ring. -/
def targetValuationSubringToIntegralClosureOfModuleFinite
    (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.toDVF.valuationSubring target.toDVF.valuationSubring]
    [IsScalarTower base.toDVF.valuationSubring target.toDVF.valuationSubring L] :
    target.toDVF.valuationSubring →+* integralClosure base.toDVF.valuationSubring L where
  toFun z :=
    ⟨(z : L),
      target_valuationSubring_mem_integralClosure_of_moduleFinite
        (K := K) (L := L) base target z⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' z₁ z₂ := by ext; simp
  map_mul' z₁ z₂ := by ext; simp

omit [FiniteDimensional K L] in
/-- The inverse map sends a target integer to its integral-closure representative. -/
@[simp] theorem targetValuationSubringToIntegralClosureOfModuleFinite_apply
    (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.toDVF.valuationSubring target.toDVF.valuationSubring]
    [IsScalarTower base.toDVF.valuationSubring target.toDVF.valuationSubring L]
    (z : target.toDVF.valuationSubring) :
    ((targetValuationSubringToIntegralClosureOfModuleFinite
      (K := K) (L := L) base target z :
        integralClosure base.toDVF.valuationSubring L) : L) = z :=
  rfl

omit [FiniteDimensional K L] in
/-- Under module-finiteness, the canonical map from the integral closure to the
extension valuation ring is surjective. -/
theorem integralClosureToTargetValuationSubringOfHasExtension_surjective_of_moduleFinite
    (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.toDVF.valuationSubring target.toDVF.valuationSubring]
    [IsScalarTower base.toDVF.valuationSubring target.toDVF.valuationSubring L] :
    Function.Surjective
      (integralClosureToTargetValuationSubringOfHasExtension
        (K := K) (L := L) base target) := by
  intro z
  refine ⟨targetValuationSubringToIntegralClosureOfModuleFinite
    (K := K) (L := L) base target z, ?_⟩
  ext
  rfl

omit [FiniteDimensional K L] in
/-- Under module-finiteness, the canonical map from the integral closure to the
extension valuation ring is bijective. -/
theorem integralClosureToTargetValuationSubringOfHasExtension_bijective_of_moduleFinite
    (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.toDVF.valuationSubring target.toDVF.valuationSubring]
    [IsScalarTower base.toDVF.valuationSubring target.toDVF.valuationSubring L] :
    Function.Bijective
      (integralClosureToTargetValuationSubringOfHasExtension
        (K := K) (L := L) base target) :=
  ⟨integralClosureToTargetValuationSubringOfHasExtension_injective
      (K := K) (L := L) base target,
    integralClosureToTargetValuationSubringOfHasExtension_surjective_of_moduleFinite
      (K := K) (L := L) base target⟩

/-- If the extension valuation ring is finite over the base valuation ring,
then it is canonically ring-equivalent to the actual integral closure of the
base valuation ring in the extension field. -/
noncomputable def integralClosureRingEquivTargetValuationSubringOfModuleFinite
    (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.toDVF.valuationSubring target.toDVF.valuationSubring]
    [IsScalarTower base.toDVF.valuationSubring target.toDVF.valuationSubring L] :
    integralClosure base.toDVF.valuationSubring L ≃+* target.toDVF.valuationSubring :=
  RingEquiv.ofBijective
    (integralClosureToTargetValuationSubringOfHasExtension
      (K := K) (L := L) base target)
    (integralClosureToTargetValuationSubringOfHasExtension_bijective_of_moduleFinite
      (K := K) (L := L) base target)

omit [FiniteDimensional K L] in
/-- The finite integral-closure ring equivalence evaluates by the canonical inclusion. -/
@[simp] theorem integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply
    (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.toDVF.valuationSubring target.toDVF.valuationSubring]
    [IsScalarTower base.toDVF.valuationSubring target.toDVF.valuationSubring L]
    (z : integralClosure base.toDVF.valuationSubring L) :
    (integralClosureRingEquivTargetValuationSubringOfModuleFinite
      (K := K) (L := L) base target z :
        target.toDVF.valuationSubring) =
      integralClosureToTargetValuationSubringOfHasExtension
        (K := K) (L := L) base target z :=
  rfl

end ValuedExtension

end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_FiniteExtension_Degree
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

/-- The canonical integer map from the base valuation ring to the valuation
subring constructed from the actual integral closure.  Its definition uses the
exact pullback theorem for the constructed integral-closure valuation subring,
so no auxiliary alias of the base or target valuation ring is introduced. -/
def integralClosureValuationSubringIntegerMapOfMemOrInv
    (base : CompleteDVF.{u, v} K)
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring) :
    base.valuationSubring →+*
      integralClosureValuationSubringOfMemOrInv
        (L := L) base.valuation hval where
  toFun a :=
    ⟨algebraMap K L (a : K),
      (integralClosureValuationSubringOfMemOrInv_pullback
        (L := L) base.valuation hval (a : K)).2 a.2⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' := by intro a b; ext; simp
  map_mul' := by intro a b; ext; simp

omit [FiniteDimensional K L] in
/-- The finite-extension integer map into the integral closure is the ambient algebra map. -/
@[simp] theorem integralClosureValuationSubringIntegerMapOfMemOrInv_apply
    (base : CompleteDVF.{u, v} K)
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring)
    (a : base.valuationSubring) :
    ((integralClosureValuationSubringIntegerMapOfMemOrInv
      (K := K) (L := L) base hval a :
        integralClosureValuationSubringOfMemOrInv
          (L := L) base.valuation hval) : L) =
      algebraMap K L (a : K) :=
  rfl

end ValuedExtension
end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_FiniteExtension_Core
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-! Provides the public declarations in the `ValuationTheory.DiscreteValuationField.FiniteExtension` Lean module. -/

namespace ValuationTheory

noncomputable section

universe u v w x y

namespace DiscreteValuationField

namespace ValuedExtension.Henselian

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L] [FiniteDimensional K L]
variable (base : HenselianDVF.{u, v} K) (target : HenselianDVF.{w, x} L)
variable [base.toDVF.valuation.HasExtension target.toDVF.valuation]

/-- The canonical integer map from a Henselian base valuation ring to the
valuation subring constructed from the actual integral closure. -/
def integralClosureValuationSubringIntegerMapOfMemOrInv
    (base : HenselianDVF.{u, v} K)
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring) :
    base.valuationSubring →+*
      ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
        (L := L) base.toDVF.valuation hval where
  toFun a :=
    ⟨algebraMap K L (a : K),
      (ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_pullback
        (L := L) base.toDVF.valuation hval (a : K)).2 a.2⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' := by intro a b; ext; simp
  map_mul' := by intro a b; ext; simp

omit [FiniteDimensional K L] in
/-- The integer map into the integral-closure valuation ring is the ambient algebra map. -/
@[simp] theorem integralClosureValuationSubringIntegerMapOfMemOrInv_apply
    (base : HenselianDVF.{u, v} K)
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring)
    (a : base.valuationSubring) :
    ((integralClosureValuationSubringIntegerMapOfMemOrInv
      (K := K) (L := L) base hval a :
        ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
          (L := L) base.toDVF.valuation hval) : L) =
      algebraMap K L (a : K) :=
  rfl

end ValuedExtension.Henselian

end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_AbsoluteValue_AlgebraicExtension_NormFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# the finite norm-formula theorem

Algebraic facts about the finite norm formula used in the explicit proof of
The algebraic-extension norm formula, together with restriction of a valued field tower to an
intermediate field.
-/

noncomputable section

universe u v w x y z

namespace AlgebraicNumberTheory
namespace Valuations

theorem normFormula_real_natPow_rpow_inv_mul_cancel
    {a : ℝ} (ha : 0 ≤ a) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (a ^ n) ^ (1 / ((m * n : ℕ) : ℝ)) = a ^ (1 / (m : ℝ)) := by
  by_cases ha0 : a = 0
  · have hmn_ne : ((m * n : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.mul_ne_zero (Nat.ne_of_gt hm) (Nat.ne_of_gt hn)
    have hm_ne : (m : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hm
    rw [ha0, zero_pow (Nat.ne_of_gt hn),
      Real.zero_rpow (one_div_ne_zero hmn_ne),
      Real.zero_rpow (one_div_ne_zero hm_ne)]
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (fun h => ha0 h.symm)
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha_pos.le]
    have hm_ne : (m : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hm
    have hn_ne : (n : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hn
    congr 1
    field_simp [hm_ne, hn_ne]
    norm_num [Nat.cast_mul, mul_comm]

/-- the finite norm-formula theorem, finite absolute-value norm-formula algebraic source: the
candidate `|N_{L/K}(x)|^(1/[L:K])` reduces to the same constant-term
formula as the spectral construction in the complete case.

This is purely algebraic and does not use Henselianity.  The remaining
the finite norm-formula theorem work is to identify the unique Henselian extension with this
candidate absolute value. -/
theorem normFormula_finiteExtensionNormFormulaValue_eq_minpoly_coeff_zero_rpow
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) (x : L) :
    finiteExtensionNormFormulaValue v x =
      v ((minpoly K x).coeff 0) ^
        (1 / ((minpoly K x).natDegree : ℝ)) := by
  let : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  let : Algebra.IsIntegral K L := Algebra.IsAlgebraic.isIntegral
  have hxint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  let : FiniteDimensional K (IntermediateField.adjoin K ({x} : Set L)) :=
    IntermediateField.adjoin.finiteDimensional hxint
  let : FiniteDimensional (IntermediateField.adjoin K ({x} : Set L)) L :=
    FiniteDimensional.right K (IntermediateField.adjoin K ({x} : Set L)) L
  have hd_pos : 0 < (minpoly K x).natDegree :=
    minpoly.natDegree_pos hxint
  have hr_pos :
      0 < Module.finrank (IntermediateField.adjoin K ({x} : Set L)) L :=
    Module.finrank_pos
      (R := IntermediateField.adjoin K ({x} : Set L)) (M := L)
  have hnorm :
      v (Algebra.norm K x) =
        v ((minpoly K x).coeff 0) ^
          Module.finrank (IntermediateField.adjoin K ({x} : Set L)) L := by
    rw [Algebra.norm_eq_norm_adjoin K x, map_pow]
    have hgen :
        Algebra.norm K (IntermediateField.AdjoinSimple.gen K x) =
          (-1 : K) ^ (minpoly K x).natDegree * (minpoly K x).coeff 0 := by
      simpa [IntermediateField.adjoin.powerBasis_gen,
        IntermediateField.minpoly_gen, IntermediateField.adjoin.powerBasis_dim]
        using
          (Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly
            (IntermediateField.adjoin.powerBasis hxint))
    rw [hgen, v.map_mul, v.map_pow, AbsoluteValue.map_neg]
    simp
  rw [finiteExtensionNormFormulaValue, hnorm]
  rw [← Module.finrank_mul_finrank K
      (IntermediateField.adjoin K ({x} : Set L)) L,
    IntermediateField.adjoin.finrank hxint]
  exact normFormula_real_natPow_rpow_inv_mul_cancel
    (v.nonneg ((minpoly K x).coeff 0)) hd_pos hr_pos

/-- the finite norm-formula theorem, finite absolute-value norm-formula inverse source:
the norm-formula candidate sends inverses to inverses. -/
theorem normFormula_finiteExtensionNormFormulaValue_inv
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) (x : L) :
    finiteExtensionNormFormulaValue v x⁻¹ =
      (finiteExtensionNormFormulaValue v x)⁻¹ := by
  rw [finiteExtensionNormFormulaValue, finiteExtensionNormFormulaValue,
    show Algebra.norm K x⁻¹ = (Algebra.norm K x)⁻¹ from
      Algebra.norm_inv (K := K) x,
    map_inv₀ v (Algebra.norm K x)]
  exact Real.inv_rpow (v.nonneg (Algebra.norm K x))
    (1 / (Module.finrank K L : ℝ))

/-- the finite norm-formula theorem, finite absolute-value norm-formula closed-unit/minpoly
source: the candidate is at most one exactly when the constant
coefficient of the minimal polynomial has base absolute value at most one. -/
theorem normFormula_finiteExtensionNormFormulaValue_le_one_iff_minpoly_coeff_zero_le_one
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) (x : L) :
    finiteExtensionNormFormulaValue v x ≤ 1 ↔
      v ((minpoly K x).coeff 0) ≤ 1 := by
  let : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  let : Algebra.IsIntegral K L := Algebra.IsAlgebraic.isIntegral
  have hxint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hd : 0 < (1 / ((minpoly K x).natDegree : ℝ)) := by
    exact one_div_pos.mpr (by
      exact_mod_cast (minpoly.natDegree_pos hxint))
  rw [normFormula_finiteExtensionNormFormulaValue_eq_minpoly_coeff_zero_rpow]
  simpa using
    (Real.rpow_le_rpow_iff
      (v.nonneg ((minpoly K x).coeff 0)) zero_le_one hd)

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Henselian_Factorization_Basic
attribute [-instance] _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# algebraic input for Hensel's lemma

This file records the residue-polynomial data used at the start of the
proof of Hensel's lemma.  The analytic convergence step is kept separate; the
lemmas here are the initial lifts and congruences.
-/

noncomputable section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- Polynomial coefficient maps distribute over `f - g*h`, the first Hensel
congruence expression. -/
theorem henselFactorization_map_sub_mul
    {R k : Type*} [CommRing R] [CommRing k] (φ : R →+* k)
    (f g h : R[X]) :
    (f - g * h).map φ = f.map φ - g.map φ * h.map φ := by
  simp [Polynomial.map_sub, Polynomial.map_mul]

/-- Polynomial coefficient maps distribute over `g*q - A`, the product
congruence used to bound the high coefficients of the quotient. -/
theorem henselFactorization_map_mul_sub
    {R k : Type*} [CommRing R] [CommRing k] (φ : R →+* k)
    (g q A : R[X]) :
    (g * q - A).map φ = g.map φ * q.map φ - A.map φ := by
  simp [Polynomial.map_sub, Polynomial.map_mul]

/-- Polynomial coefficient maps distribute over the Hensel correction expression
`g*q + h*p - fn`. -/
theorem henselFactorization_map_mul_add_mul_sub
    {R k : Type*} [CommRing R] [CommRing k] (φ : R →+* k)
    (g h q p fn : R[X]) :
    (g * q + h * p - fn).map φ =
      g.map φ * q.map φ + h.map φ * p.map φ - fn.map φ := by
  simp [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul]

/-- unit-leading input: a lift with the same natural degree as
a nonzero residual polynomial has unit leading coefficient. -/
theorem henselFactorization_lift_leadingCoeff_isUnit_of_natDegree_eq
    {R : Type*} [CommRing R] [IsLocalRing R]
    {g0 : R[X]} {gbar : (IsLocalRing.ResidueField R)[X]}
    (hg0 : g0.map (IsLocalRing.residue R) = gbar)
    (hdegree : g0.natDegree = gbar.natDegree)
    (hlead : gbar.leadingCoeff ≠ 0) :
    IsUnit g0.leadingCoeff := by
  have hcoeff :=
    congrArg (fun P : (IsLocalRing.ResidueField R)[X] =>
      P.coeff gbar.natDegree) hg0
  have hres_lead :
      IsLocalRing.residue R g0.leadingCoeff = gbar.leadingCoeff := by
    change (g0.map (IsLocalRing.residue R)).coeff gbar.natDegree =
      gbar.coeff gbar.natDegree at hcoeff
    rw [Polynomial.coeff_map] at hcoeff
    change IsLocalRing.residue R (g0.coeff g0.natDegree) =
      gbar.coeff gbar.natDegree
    rw [hdegree]
    exact hcoeff
  have hres_ne : IsLocalRing.residue R g0.leadingCoeff ≠ 0 := by
    rw [hres_lead]
    exact hlead
  exact (IsLocalRing.residue_ne_zero_iff_isUnit g0.leadingCoeff).1 hres_ne

/-- unit-leading normalization: a polynomial whose leading
coefficient is a unit becomes monic after multiplying by the inverse leading
coefficient, and this normalization preserves degree. -/
theorem henselFactorization_monic_normalization_of_unit_leadingCoeff
    {R : Type*} [CommRing R] {g : R[X]} (hunit : IsUnit g.leadingCoeff) :
    ∃ u : Rˣ,
      (u : R) = g.leadingCoeff ∧
        (Polynomial.C ((u⁻¹ : Rˣ) : R) * g).Monic ∧
          (Polynomial.C ((u⁻¹ : Rˣ) : R) * g).degree = g.degree ∧
            (Polynomial.C ((u⁻¹ : Rˣ) : R) * g).natDegree = g.natDegree := by
  rcases hunit with ⟨u, hu⟩
  have hinvUnit : IsUnit (((u⁻¹ : Rˣ) : R)) := ⟨u⁻¹, rfl⟩
  refine ⟨u, hu, ?_, ?_, ?_⟩
  · exact Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
      (p := g) (b := ((u⁻¹ : Rˣ) : R)) (Units.inv_mul_of_eq (u := u) hu)
  · exact Polynomial.degree_C_mul_of_isUnit hinvUnit g
  · exact Polynomial.natDegree_C_mul_of_isUnit hinvUnit g

/-- A polynomial maps to zero iff all of its coefficients lie in the kernel of
the coefficient map.  This is the coefficientwise form used by the Hensel
correction congruences. -/
theorem henselFactorization_map_eq_zero_iff_coeff_mem_ker
    {R k : Type*} [CommRing R] [CommRing k] (φ : R →+* k) (P : R[X]) :
    P.map φ = 0 ↔ ∀ n : ℕ, P.coeff n ∈ RingHom.ker φ := by
  constructor
  · intro h n
    rw [RingHom.mem_ker]
    have hcoeff := congrArg (fun Q : k[X] => Q.coeff n) h
    simpa [Polynomial.coeff_map] using hcoeff
  · intro h
    ext n
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    exact RingHom.mem_ker.mp (h n)

/-- Polynomial coefficient maps are equal iff every coefficient of the
difference lies in the kernel. -/
theorem henselFactorization_map_eq_iff_sub_coeff_mem_ker
    {R k : Type*} [CommRing R] [CommRing k] (φ : R →+* k) (P Q : R[X]) :
    P.map φ = Q.map φ ↔ ∀ n : ℕ, (P - Q).coeff n ∈ RingHom.ker φ := by
  rw [← sub_eq_zero, ← Polynomial.map_sub]
  exact henselFactorization_map_eq_zero_iff_coeff_mem_ker φ (P - Q)

/-- The kernel of the quotient map `R -> R/I` is exactly `I`. -/
theorem henselFactorization_mem_ker_quotient_mk_iff
    {R : Type*} [CommRing R] (I : Ideal R) (x : R) :
    x ∈ RingHom.ker (Ideal.Quotient.mk I) ↔ x ∈ I := by
  rw [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

/-- Specialization of the coefficientwise zero criterion to quotient maps:
a polynomial maps to zero in `(R/I)[X]` iff all of its coefficients lie in
`I`. -/
theorem henselFactorization_map_quotient_eq_zero_iff_coeff_mem
    {R : Type*} [CommRing R] (I : Ideal R) (P : R[X]) :
    P.map (Ideal.Quotient.mk I) = 0 ↔ ∀ n : ℕ, P.coeff n ∈ I := by
  rw [henselFactorization_map_eq_zero_iff_coeff_mem_ker]
  constructor
  · intro h n
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact RingHom.mem_ker.mp (h n)
  · intro h n
    rw [RingHom.mem_ker]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (h n)

/-- Coefficientwise form of
`henselFactorization_map_quotient_eq_zero_iff_coeff_mem`. -/
theorem henselFactorization_quotient_map_coeff_eq_zero_iff_coeff_mem
    {R : Type*} [CommRing R] (I : Ideal R) (P : R[X]) (n : ℕ) :
    (P.map (Ideal.Quotient.mk I)).coeff n = 0 ↔ P.coeff n ∈ I := by
  rw [Polynomial.coeff_map, Ideal.Quotient.eq_zero_iff_mem]

/-- Equality after quotienting coefficients is the same as coefficientwise
membership of the difference in the quotient ideal. -/
theorem henselFactorization_map_quotient_eq_iff_sub_coeff_mem
    {R : Type*} [CommRing R] (I : Ideal R) (P Q : R[X]) :
    P.map (Ideal.Quotient.mk I) = Q.map (Ideal.Quotient.mk I) ↔
      ∀ n : ℕ, (P - Q).coeff n ∈ I := by
  rw [henselFactorization_map_eq_iff_sub_coeff_mem_ker]
  constructor
  · intro h n
    exact (henselFactorization_mem_ker_quotient_mk_iff I _).1 (h n)
  · intro h n
    exact (henselFactorization_mem_ker_quotient_mk_iff I _).2 (h n)

/-- division step: division by a monic polynomial gives the
quotient and remainder used in the correction construction, with remainder
degree strictly smaller than the divisor degree. -/
theorem henselFactorization_division_by_monic_degree_lt
    {R : Type*} [CommRing R] [Nontrivial R] (F g : R[X]) (hg : g.Monic) :
    ∃ q p : R[X], F = g * q + p ∧ p.degree < g.degree := by
  refine ⟨F /ₘ g, F %ₘ g, ?_, ?_⟩
  · calc
      F = F %ₘ g + g * (F /ₘ g) := by
        exact (Polynomial.modByMonic_add_div F g).symm
      _ = g * (F /ₘ g) + F %ₘ g := by
        ring
  · exact Polynomial.degree_modByMonic_lt F hg

/-- division by a unit-leading divisor: the division step used
in the Hensel correction construction does not require the chosen lift `g0` to
be monic; a unit leading coefficient is enough. -/
theorem henselFactorization_division_by_unit_leading_degree_lt
    {R : Type*} [CommRing R] [Nontrivial R] (F g : R[X])
    (hunit : IsUnit g.leadingCoeff) :
    ∃ q p : R[X], F = g * q + p ∧ p.degree < g.degree := by
  rcases henselFactorization_monic_normalization_of_unit_leadingCoeff
    (g := g) hunit with
    ⟨u, _hu, hmonic, hdegree, _hnatDegree⟩
  rcases henselFactorization_division_by_monic_degree_lt F
    (Polynomial.C ((u⁻¹ : Rˣ) : R) * g) hmonic with
    ⟨q, p, hdiv, hpdeg⟩
  refine ⟨Polynomial.C ((u⁻¹ : Rˣ) : R) * q, p, ?_, ?_⟩
  · calc
      F = (Polynomial.C ((u⁻¹ : Rˣ) : R) * g) * q + p := hdiv
      _ = g * (Polynomial.C ((u⁻¹ : Rˣ) : R) * q) + p := by
        ring
  · rwa [hdegree] at hpdeg

/-- division by a lifted residual factor: if `g0` lifts
`gbar` with the same degree and `gbar` is nonzero in leading coefficient, then
the construction division step `F = g0 q + p`, `deg p < deg g0`, is available in the
valuation ring. -/
theorem henselFactorization_division_by_lifted_factor_degree_lt
    {R : Type*} [CommRing R] [IsLocalRing R]
    {g0 : R[X]} {gbar : (IsLocalRing.ResidueField R)[X]}
    (hg0 : g0.map (IsLocalRing.residue R) = gbar)
    (hdegree : g0.natDegree = gbar.natDegree)
    (hlead : gbar.leadingCoeff ≠ 0) (F : R[X]) :
    ∃ q p : R[X], F = g0 * q + p ∧ p.degree < g0.degree := by
  exact henselFactorization_division_by_unit_leading_degree_lt F g0
    (henselFactorization_lift_leadingCoeff_isUnit_of_natDegree_eq hg0 hdegree hlead)

/-- Algebra identity behind the Hensel correction step after the division
`b * fn = g0 * q + p`. -/
theorem henselFactorization_correction_identity_after_division
    {R : Type*} [CommSemiring R] {a b g0 h0 fn q p : R[X]}
    (hdiv : b * fn = g0 * q + p) :
    g0 * (a * fn + h0 * q) + h0 * p = (a * g0 + b * h0) * fn := by
  calc
    g0 * (a * fn + h0 * q) + h0 * p =
        a * g0 * fn + h0 * (g0 * q + p) := by
      ring
    _ = a * g0 * fn + h0 * (b * fn) := by
      rw [← hdiv]
    _ = (a * g0 + b * h0) * fn := by
      ring

/-- correction congruence after division, read directly
modulo the principal ideal `(π)`: if the lifted Bezout error has a displayed
`C π` factor, then the divided correction represents `fn` modulo `(π)`. -/
theorem henselFactorization_correction_congruence_span_singleton_after_division
    {R : Type*} [CommRing R] {π : R}
    {a b g0 h0 fn q p e : R[X]}
    (hbez : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hdiv : b * fn = g0 * q + p) :
    ∀ n : ℕ,
      (g0 * (a * fn + h0 * q) + h0 * p - fn).coeff n ∈
        Ideal.span ({π} : Set R) := by
  have halg :=
    henselFactorization_correction_identity_after_division
      (a := a) (h0 := h0) hdiv
  have hfactor :
      g0 * (a * fn + h0 * q) + h0 * p - fn =
        Polynomial.C π * (e * fn) := by
    calc
      g0 * (a * fn + h0 * q) + h0 * p - fn =
          (a * g0 + b * h0 - 1) * fn := by
        rw [halg]
        ring
      _ = Polynomial.C π * (e * fn) := by
        rw [hbez]
        ring
  intro n
  rw [hfactor, Polynomial.coeff_C_mul, Ideal.mem_span_singleton]
  exact dvd_mul_right π ((e * fn).coeff n)

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Henselian_Factorization_AdicLimits
attribute [-instance] _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# coefficientwise limit preparation

This file records the coefficientwise Cauchy form of the infinite Hensel
approximants.  It is the input needed for the adic-completeness step in
the coefficientwise proof of Hensel's lemma.
-/

noncomputable section

open scoped Polynomial
open scoped BigOperators

namespace AlgebraicNumberTheory
namespace Valuations

/-- the directed adic Cauchy estimate for a coefficient
sequence: later differences from stage `M` lie in `I^(M+1)`. -/
def henselFactorization_adicCoeffCauchy
    {R : Type*} [CommRing R] (I : Ideal R) (x : ℕ → R) : Prop :=
  ∀ {M N : ℕ}, M ≤ N → x N - x M ∈ I ^ (M + 1)

/-- the coefficientwise `I^(M+1)` estimate gives mathlib's
`I`-adic Cauchy condition after weakening `I^(M+1) ≤ I^M`. -/
theorem henselFactorization_adicCoeffCauchy_isAdicCauchy
    {R : Type*} [CommRing R] (I : Ideal R) {x : ℕ → R}
    (hx : henselFactorization_adicCoeffCauchy I x) :
    AdicCompletion.IsAdicCauchy I R x := by
  intro M N hMN
  apply SModEq.sub_mem.mpr
  have hdeep : x N - x M ∈ I ^ M :=
    Ideal.pow_le_pow_right (Nat.le_succ M) (hx hMN)
  have hsign : x M - x N ∈ I ^ M := by
    simpa [neg_sub] using (I ^ M).neg_mem hdeep
  simpa [smul_eq_mul, Ideal.mul_top] using hsign

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Henselian_Factorization_Truncation
attribute [-instance] _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# coefficient truncation for the Hensel correction step

This file contains the finite coefficient-cutting step used in the
proof of Hensel's lemma: after the division step, coefficients already zero in
the residue field may be omitted to impose the required degree bound.
-/

noncomputable section

open scoped Polynomial
open scoped BigOperators

namespace AlgebraicNumberTheory
namespace Valuations

/-- low-degree part of a polynomial up to degree `N`. -/
def henselFactorization_lowPart {R : Type*} [Semiring R] (N : ℕ) (P : R[X]) : R[X] :=
  Finset.sum (Finset.range (N + 1)) fun i => Polynomial.monomial i (P.coeff i)

/-- coefficients at degrees kept by `lowPart`. -/
theorem henselFactorization_lowPart_coeff_of_le
    {R : Type*} [Semiring R] {N n : ℕ} (P : R[X]) (hn : n ≤ N) :
    (henselFactorization_lowPart N P).coeff n = P.coeff n := by
  classical
  unfold henselFactorization_lowPart
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single n]
  · simp
  · intro b _hb hbn
    simp [Polynomial.coeff_monomial, hbn]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr (Nat.lt_succ_of_le hn)))

/-- coefficients above the cutoff vanish in `lowPart`. -/
theorem henselFactorization_lowPart_coeff_eq_zero_of_lt
    {R : Type*} [Semiring R] {N n : ℕ} (P : R[X]) (hn : N < n) :
    (henselFactorization_lowPart N P).coeff n = 0 := by
  classical
  unfold henselFactorization_lowPart
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero ?_
  intro b hb
  have hbn : b ≠ n := by
    intro hbn
    have hn_le : n ≤ N := Nat.lt_succ_iff.mp (by simpa [hbn] using hb)
    exact (Nat.not_lt_of_ge hn_le) hn
  simp [Polynomial.coeff_monomial, hbn]

/-- `lowPart` has the intended degree bound. -/
theorem henselFactorization_lowPart_natDegree_le
    {R : Type*} [Semiring R] (N : ℕ) (P : R[X]) :
    (henselFactorization_lowPart N P).natDegree ≤ N := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  exact henselFactorization_lowPart_coeff_eq_zero_of_lt (P := P) hn

/-- omitting high coefficients already in the kernel does not
change the residual polynomial. -/
theorem henselFactorization_lowPart_map_eq_of_high_coeff_mem_ker
    {R k : Type*} [CommRing R] [CommRing k] (φ : R →+* k)
    (N : ℕ) (P : R[X])
    (hhigh : ∀ n : ℕ, N < n → P.coeff n ∈ RingHom.ker φ) :
    (henselFactorization_lowPart N P).map φ = P.map φ := by
  ext n
  by_cases hn : n ≤ N
  · rw [Polynomial.coeff_map, Polynomial.coeff_map,
      henselFactorization_lowPart_coeff_of_le (P := P) hn]
  · have hlt : N < n := Nat.lt_of_not_ge hn
    have hker := hhigh n hlt
    rw [Polynomial.coeff_map, Polynomial.coeff_map,
      henselFactorization_lowPart_coeff_eq_zero_of_lt (P := P) hlt]
    rw [RingHom.mem_ker] at hker
    simpa using hker.symm

/-- kernel-level truncation: the correction congruence
survives replacing a provisional correction polynomial by its low-degree part
when the omitted coefficients already lie in the same coefficient-map kernel. -/
theorem henselFactorization_correction_after_lowPart_ker
    {R k : Type*} [CommRing R] [CommRing k] (φ : R →+* k)
    {g0 h0 fn p Q : R[X]} (N : ℕ)
    (hcorr :
      ∀ n : ℕ, (g0 * Q + h0 * p - fn).coeff n ∈ RingHom.ker φ)
    (hhigh : ∀ n : ℕ, N < n → Q.coeff n ∈ RingHom.ker φ) :
    (henselFactorization_lowPart N Q).natDegree ≤ N ∧
      ∀ n : ℕ,
        (g0 * henselFactorization_lowPart N Q + h0 * p - fn).coeff n ∈
          RingHom.ker φ := by
  refine ⟨henselFactorization_lowPart_natDegree_le N Q, ?_⟩
  have hmapQ :=
    henselFactorization_lowPart_map_eq_of_high_coeff_mem_ker φ N Q hhigh
  have hmapOld :
      (g0 * Q + h0 * p - fn).map φ = 0 := by
    exact (henselFactorization_map_eq_zero_iff_coeff_mem_ker
      φ (g0 * Q + h0 * p - fn)).2 hcorr
  have hmapNew :
      (g0 * henselFactorization_lowPart N Q + h0 * p - fn).map φ = 0 := by
    calc
      (g0 * henselFactorization_lowPart N Q + h0 * p - fn).map φ =
          g0.map φ * (henselFactorization_lowPart N Q).map φ +
            h0.map φ * p.map φ - fn.map φ := by
        exact henselFactorization_map_mul_add_mul_sub φ g0 h0
          (henselFactorization_lowPart N Q) p fn
      _ = g0.map φ * Q.map φ + h0.map φ * p.map φ - fn.map φ := by
        rw [hmapQ]
      _ = (g0 * Q + h0 * p - fn).map φ := by
        exact (henselFactorization_map_mul_add_mul_sub φ g0 h0 Q p fn).symm
      _ = 0 := hmapOld
  intro n
  exact (henselFactorization_map_eq_zero_iff_coeff_mem_ker
    φ (g0 * henselFactorization_lowPart N Q + h0 * p - fn)).1 hmapNew n

/-- ideal-level truncation: the correction congruence survives
replacing a provisional correction polynomial by its low-degree part when the
omitted coefficients already lie in the same ideal. -/
theorem henselFactorization_correction_after_lowPart_ideal
    {R : Type*} [CommRing R] {I : Ideal R}
    {g0 h0 fn p Q : R[X]} (N : ℕ)
    (hcorr :
      ∀ n : ℕ, (g0 * Q + h0 * p - fn).coeff n ∈ I)
    (hhigh : ∀ n : ℕ, N < n → Q.coeff n ∈ I) :
    (henselFactorization_lowPart N Q).natDegree ≤ N ∧
      ∀ n : ℕ,
        (g0 * henselFactorization_lowPart N Q + h0 * p - fn).coeff n ∈ I := by
  let φ : R →+* R ⧸ I := Ideal.Quotient.mk I
  have hcorrKer :
      ∀ n : ℕ, (g0 * Q + h0 * p - fn).coeff n ∈ RingHom.ker φ := by
    intro n
    exact (henselFactorization_mem_ker_quotient_mk_iff I _).2 (hcorr n)
  have hhighKer :
      ∀ n : ℕ, N < n → Q.coeff n ∈ RingHom.ker φ := by
    intro n hn
    exact (henselFactorization_mem_ker_quotient_mk_iff I _).2 (hhigh n hn)
  rcases henselFactorization_correction_after_lowPart_ker
      φ (N := N) (g0 := g0) (h0 := h0) (fn := fn)
      (p := p) (Q := Q) hcorrKer hhighKer with
    ⟨hdeg, hker⟩
  refine ⟨hdeg, ?_⟩
  intro n
  exact (henselFactorization_mem_ker_quotient_mk_iff I _).1 (hker n)

/-- principal-ideal truncation: if the provisional correction
is congruent modulo `(π)` and all omitted coefficients are divisible by `π`,
then the truncated correction keeps the same congruence modulo `(π)`. -/
theorem henselFactorization_correction_after_lowPart_span_singleton
    {R : Type*} [CommRing R] {π : R}
    {g0 h0 fn p Q : R[X]} (N : ℕ)
    (hcorr :
      ∀ n : ℕ, (g0 * Q + h0 * p - fn).coeff n ∈
        Ideal.span ({π} : Set R))
    (hhigh : ∀ n : ℕ, N < n → Q.coeff n ∈
      Ideal.span ({π} : Set R)) :
    (henselFactorization_lowPart N Q).natDegree ≤ N ∧
      ∀ n : ℕ,
        (g0 * henselFactorization_lowPart N Q + h0 * p - fn).coeff n ∈
          Ideal.span ({π} : Set R) := by
  exact henselFactorization_correction_after_lowPart_ideal
    (I := Ideal.span ({π} : Set R)) N hcorr hhigh

/-- unit-leading degree division over an arbitrary
commutative ring: if the product with a degree-`m` polynomial whose leading
coefficient is a unit has degree at most `d`, then the right factor has degree
at most `d - m`.  This is the form needed over `O/(π)` in the iterative proof. -/
theorem henselFactorization_natDegree_right_le_tsub_of_unit_leading_mul_natDegree_le
    {R : Type*} [CommRing R] {g Q : R[X]} {m d : ℕ}
    (hgunit : IsUnit g.leadingCoeff) (hgdeg : g.natDegree = m)
    (hprod : (g * Q).natDegree ≤ d) :
    Q.natDegree ≤ d - m := by
  by_cases hQ : Q = 0
  · simp [hQ]
  rcases henselFactorization_monic_normalization_of_unit_leadingCoeff
      (g := g) hgunit with
    ⟨u, _hu, hmonic, _hdegree, hnatDegree⟩
  let G : R[X] := Polynomial.C (((u⁻¹ : Rˣ) : R)) * g
  have hGmonic : G.Monic := by
    simpa [G] using hmonic
  have hGnat : G.natDegree = m := by
    simpa [G, hgdeg] using hnatDegree
  have hinvUnit : IsUnit (((u⁻¹ : Rˣ) : R)) := ⟨u⁻¹, rfl⟩
  have hGprod : (G * Q).natDegree ≤ d := by
    have hrewrite :
        G * Q = Polynomial.C (((u⁻¹ : Rˣ) : R)) * (g * Q) := by
      dsimp [G]
      ring
    rw [hrewrite, Polynomial.natDegree_C_mul_of_isUnit hinvUnit]
    exact hprod
  have hsum : m + Q.natDegree ≤ d := by
    have hmul := hGmonic.natDegree_mul' hQ
    rw [hGnat] at hmul
    simpa [hmul] using hGprod
  exact Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using hsum)

/-- a unit-leading polynomial remains unit-leading with the
same natural degree after mapping to a nontrivial target ring.  This supplies
the unit-leading input used over `O/(π)`. -/
theorem henselFactorization_map_unit_leadingCoeff_natDegree_eq
    {R S : Type*} [CommRing R] [CommRing S] [Nontrivial S]
    (φ : R →+* S) {g : R[X]} {m : ℕ}
    (hgunit : IsUnit g.leadingCoeff) (hgdeg : g.natDegree = m) :
    IsUnit (g.map φ).leadingCoeff ∧ (g.map φ).natDegree = m := by
  have hlead :
      (g.map φ).leadingCoeff = φ g.leadingCoeff :=
    Polynomial.leadingCoeff_map_eq_of_isUnit_leadingCoeff φ hgunit
  have hnat :
      (g.map φ).natDegree = g.natDegree :=
    Polynomial.natDegree_map_eq_of_isUnit_leadingCoeff φ hgunit
  exact ⟨by
    rw [hlead]
    exact IsUnit.map φ hgunit, by
    rw [hnat, hgdeg]⟩

/-- quotient specialization of
`henselFactorization_map_unit_leadingCoeff_natDegree_eq`. -/
theorem henselFactorization_quotient_unit_leadingCoeff_natDegree_eq
    {R : Type*} [CommRing R] {I : Ideal R} [Nontrivial (R ⧸ I)]
    {g : R[X]} {m : ℕ}
    (hgunit : IsUnit g.leadingCoeff) (hgdeg : g.natDegree = m) :
    IsUnit (g.map (Ideal.Quotient.mk I)).leadingCoeff ∧
      (g.map (Ideal.Quotient.mk I)).natDegree = m :=
  henselFactorization_map_unit_leadingCoeff_natDegree_eq
    (Ideal.Quotient.mk I) hgunit hgdeg

/-- if `π` lies in the maximal ideal of a local ring, then
the quotient `O/(π)` is nontrivial.  This is the displayed-factor source for the
nontriviality needed in the degree argument modulo `(π)`. -/
theorem henselFactorization_span_singleton_quotient_nontrivial_of_mem_maximalIdeal
    {R : Type*} [CommRing R] [IsLocalRing R] {π : R}
    (hπ : π ∈ IsLocalRing.maximalIdeal R) :
    Nontrivial (R ⧸ Ideal.span ({π} : Set R)) := by
  rw [Ideal.Quotient.nontrivial_iff]
  intro htop
  have hle : Ideal.span ({π} : Set R) ≤ IsLocalRing.maximalIdeal R := by
    rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    simpa [hx] using hπ
  have htop_le :
      (⊤ : Ideal R) ≤ IsLocalRing.maximalIdeal R := by
    simpa [htop] using hle
  have hmaxTop : IsLocalRing.maximalIdeal R = ⊤ :=
    le_antisymm le_top htop_le
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top hmaxTop

/-- local-ring specialization: a unit-leading polynomial of
degree `m` stays unit-leading of degree `m` after reducing modulo `(π)`, for
`π` in the maximal ideal. -/
theorem henselFactorization_span_singleton_quotient_unit_leadingCoeff_natDegree_eq
    {R : Type*} [CommRing R] [IsLocalRing R] {π : R}
    {g : R[X]} {m : ℕ}
    (hπ : π ∈ IsLocalRing.maximalIdeal R)
    (hgunit : IsUnit g.leadingCoeff) (hgdeg : g.natDegree = m) :
    IsUnit
        ((g.map (Ideal.Quotient.mk (Ideal.span ({π} : Set R)))).leadingCoeff) ∧
      (g.map (Ideal.Quotient.mk (Ideal.span ({π} : Set R)))).natDegree = m := by
  let : Nontrivial (R ⧸ Ideal.span ({π} : Set R)) :=
    henselFactorization_span_singleton_quotient_nontrivial_of_mem_maximalIdeal hπ
  exact henselFactorization_quotient_unit_leadingCoeff_natDegree_eq
    (I := Ideal.span ({π} : Set R)) hgunit hgdeg

/-- mapped degree bound for the polynomial `fn - h0*p` from
degree bounds already available before mapping.  This is the quotient-level
replacement for the residue-field degree bound in the principal `(π)` route. -/
theorem henselFactorization_map_sub_mul_natDegree_le_of_degree_bounds
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    {fn h0 P : R[X]} {a b d : ℕ}
    (hfn : fn.natDegree ≤ d)
    (hh0 : h0.natDegree ≤ a)
    (hP : P.natDegree ≤ b)
    (hab : a + b ≤ d) :
    ((fn - h0 * P).map φ).natDegree ≤ d := by
  have hfnmap : (fn.map φ).natDegree ≤ d :=
    Polynomial.natDegree_map_le.trans hfn
  have hh0map : (h0.map φ).natDegree ≤ a :=
    Polynomial.natDegree_map_le.trans hh0
  have hPmap : (P.map φ).natDegree ≤ b :=
    Polynomial.natDegree_map_le.trans hP
  have hmul :
      (h0.map φ * P.map φ).natDegree ≤ d :=
    (Polynomial.natDegree_mul_le_of_le hh0map hPmap).trans hab
  have hmap :
      (fn - h0 * P).map φ =
        fn.map φ - h0.map φ * P.map φ := by
    exact henselFactorization_map_sub_mul φ fn h0 P
  rw [hmap]
  simpa using
    (Polynomial.natDegree_sub_le_of_le
      (p := fn.map φ) (q := h0.map φ * P.map φ) hfnmap hmul)

/-- quotient specialization of the degree bound for
`fn - h0*p` used before truncating the Hensel correction. -/
theorem henselFactorization_span_singleton_quotient_sub_mul_natDegree_le_of_degree_bounds
    {R : Type*} [CommRing R] {π : R}
    {fn h0 P : R[X]} {a b d : ℕ}
    (hfn : fn.natDegree ≤ d)
    (hh0 : h0.natDegree ≤ a)
    (hP : P.natDegree ≤ b)
    (hab : a + b ≤ d) :
    ((fn - h0 * P).map
      (Ideal.Quotient.mk (Ideal.span ({π} : Set R)))).natDegree ≤ d :=
  henselFactorization_map_sub_mul_natDegree_le_of_degree_bounds
    (Ideal.Quotient.mk (Ideal.span ({π} : Set R))) hfn hh0 hP hab

/-- high-coefficient source modulo `(π)`: if `g0 * Q` is
congruent to a polynomial of degree at most `d` modulo `(π)`, and `g0` has
degree `m` with unit leading coefficient after reduction modulo `(π)`, then
every coefficient of `Q` above `d - m` is divisible by `π`. -/
theorem henselFactorization_high_coeff_mem_span_singleton_of_product_congruence_degree
    {R : Type*} [CommRing R] {π : R}
    {g0 Q A : R[X]} {m d : ℕ}
    (hgunit :
      IsUnit
        ((g0.map (Ideal.Quotient.mk (Ideal.span ({π} : Set R)))).leadingCoeff))
    (hgdeg :
      (g0.map (Ideal.Quotient.mk (Ideal.span ({π} : Set R)))).natDegree = m)
    (hcong : ∀ n : ℕ, (g0 * Q - A).coeff n ∈
      Ideal.span ({π} : Set R))
    (hAdeg :
      (A.map (Ideal.Quotient.mk (Ideal.span ({π} : Set R)))).natDegree ≤ d) :
    ∀ n : ℕ, d - m < n → Q.coeff n ∈ Ideal.span ({π} : Set R) := by
  let φ : R →+* R ⧸ Ideal.span ({π} : Set R) :=
    Ideal.Quotient.mk (Ideal.span ({π} : Set R))
  have hmap :
      (g0 * Q - A).map φ = 0 := by
    simpa [φ] using
      (henselFactorization_map_quotient_eq_zero_iff_coeff_mem
        (Ideal.span ({π} : Set R)) (g0 * Q - A)).2 hcong
  have hsub :
      g0.map φ * Q.map φ - A.map φ = 0 := by
    simpa [henselFactorization_map_mul_sub] using hmap
  have hprod_eq : g0.map φ * Q.map φ = A.map φ :=
    sub_eq_zero.mp hsub
  have hprod_degree : (g0.map φ * Q.map φ).natDegree ≤ d := by
    rw [hprod_eq]
    exact hAdeg
  have hQdeg :
      (Q.map φ).natDegree ≤ d - m :=
    henselFactorization_natDegree_right_le_tsub_of_unit_leading_mul_natDegree_le
      (g := g0.map φ) (Q := Q.map φ) (m := m) (d := d)
      (by simpa [φ] using hgunit) (by simpa [φ] using hgdeg) hprod_degree
  intro n hn
  have hcoeff : (Q.map φ).coeff n = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hQdeg hn)
  exact
    (henselFactorization_quotient_map_coeff_eq_zero_iff_coeff_mem
      (Ideal.span ({π} : Set R)) Q n).1 (by simpa [φ] using hcoeff)

/-- high-coefficient source modulo `(π)` specialized to the
correction congruence produced by the division step. -/
theorem henselFactorization_high_coeff_mem_span_singleton_of_correction_degree
    {R : Type*} [CommRing R] {π : R}
    {g0 h0 fn p Q : R[X]} {m d : ℕ}
    (hgunit :
      IsUnit
        ((g0.map (Ideal.Quotient.mk (Ideal.span ({π} : Set R)))).leadingCoeff))
    (hgdeg :
      (g0.map (Ideal.Quotient.mk (Ideal.span ({π} : Set R)))).natDegree = m)
    (hcorr :
      ∀ n : ℕ, (g0 * Q + h0 * p - fn).coeff n ∈
        Ideal.span ({π} : Set R))
    (hAdeg :
      ((fn - h0 * p).map
        (Ideal.Quotient.mk (Ideal.span ({π} : Set R)))).natDegree ≤ d) :
    ∀ n : ℕ, d - m < n → Q.coeff n ∈ Ideal.span ({π} : Set R) := by
  have hcong :
      ∀ n : ℕ, (g0 * Q - (fn - h0 * p)).coeff n ∈
        Ideal.span ({π} : Set R) := by
    intro n
    have heq : g0 * Q - (fn - h0 * p) = g0 * Q + h0 * p - fn := by
      ring
    rw [heq]
    exact hcorr n
  exact henselFactorization_high_coeff_mem_span_singleton_of_product_congruence_degree
    (π := π) (g0 := g0) (Q := Q) (A := fn - h0 * p)
    (m := m) (d := d) hgunit hgdeg hcong hAdeg

/-- one-step degree truncation modulo `(π)`: under the
principal correction congruence, the quotient-degree bound for `fn - h0*p`,
and the unit-leading degree data for `g0` modulo `(π)`, the low-degree part of
`Q` has degree at most `d-m` and keeps the correction congruence modulo `(π)`. -/
theorem henselFactorization_correction_after_degree_truncation_span_singleton
    {R : Type*} [CommRing R] {π : R}
    {g0 h0 fn p Q : R[X]} {m d : ℕ}
    (hgunit :
      IsUnit
        ((g0.map (Ideal.Quotient.mk (Ideal.span ({π} : Set R)))).leadingCoeff))
    (hgdeg :
      (g0.map (Ideal.Quotient.mk (Ideal.span ({π} : Set R)))).natDegree = m)
    (hcorr :
      ∀ n : ℕ, (g0 * Q + h0 * p - fn).coeff n ∈
        Ideal.span ({π} : Set R))
    (hAdeg :
      ((fn - h0 * p).map
        (Ideal.Quotient.mk (Ideal.span ({π} : Set R)))).natDegree ≤ d) :
    (henselFactorization_lowPart (d - m) Q).natDegree ≤ d - m ∧
      ∀ n : ℕ,
        (g0 * henselFactorization_lowPart (d - m) Q + h0 * p - fn).coeff n ∈
          Ideal.span ({π} : Set R) := by
  exact henselFactorization_correction_after_lowPart_span_singleton
    (π := π) (N := d - m) hcorr
    (henselFactorization_high_coeff_mem_span_singleton_of_correction_degree
      (π := π) (g0 := g0) (h0 := h0) (fn := fn) (p := p)
      (Q := Q) (m := m) (d := d) hgunit hgdeg hcorr hAdeg)

/-- principal-ideal one-step correction after Bezout and
division.  This is the displayed-factor route: the displayed factor
`a*g0 + b*h0 - 1 = C π * e`, not an equality `m = (π)`, supplies the
correction congruence modulo `(π)`. -/
theorem henselFactorization_correction_after_division_degree_truncation_span_singleton
    {R : Type*} [CommRing R] [IsLocalRing R] {π : R}
    {a b g0 h0 fn q p e : R[X]} {m d : ℕ}
    (hπ : π ∈ IsLocalRing.maximalIdeal R)
    (hgunit : IsUnit g0.leadingCoeff)
    (hg0nat : g0.natDegree = m)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hdiv : b * fn = g0 * q + p)
    (hfn : fn.natDegree ≤ d)
    (hh0 : h0.natDegree ≤ d - m)
    (hp : p.natDegree ≤ m)
    (hmd : m ≤ d) :
    (henselFactorization_lowPart (d - m) (a * fn + h0 * q)).natDegree ≤ d - m ∧
      ∀ n : ℕ,
        (g0 * henselFactorization_lowPart (d - m) (a * fn + h0 * q) +
            h0 * p - fn).coeff n ∈ Ideal.span ({π} : Set R) := by
  rcases henselFactorization_span_singleton_quotient_unit_leadingCoeff_natDegree_eq
      (π := π) hπ hgunit hg0nat with
    ⟨hgunitQuot, hgdegQuot⟩
  have hcorr :
      ∀ n : ℕ, (g0 * (a * fn + h0 * q) + h0 * p - fn).coeff n ∈
        Ideal.span ({π} : Set R) :=
    henselFactorization_correction_congruence_span_singleton_after_division
      (π := π) hbezFactor hdiv
  have hAdeg :
      ((fn - h0 * p).map
        (Ideal.Quotient.mk (Ideal.span ({π} : Set R)))).natDegree ≤ d :=
    henselFactorization_span_singleton_quotient_sub_mul_natDegree_le_of_degree_bounds
      (π := π) (fn := fn) (h0 := h0) (P := p)
      (a := d - m) (b := m) (d := d) hfn hh0 hp (by
        rw [Nat.sub_add_cancel hmd])
  exact henselFactorization_correction_after_degree_truncation_span_singleton
    (π := π) (g0 := g0) (h0 := h0) (fn := fn) (p := p)
    (Q := a * fn + h0 * q) (m := m) (d := d)
    hgunitQuot hgdegQuot hcorr hAdeg

/-- principal-ideal version of replacement of the initial
lifted factors by the current inductive approximants.  If `g` and `h` are
still congruent to `g0` and `h0` modulo `(π)`, then a correction congruence
for `g0,h0` modulo `(π)` is also one for `g,h`. -/
theorem henselFactorization_correction_congruence_replace_initial_factors_span_singleton
    {R : Type*} [CommRing R] {π : R}
    {g0 h0 g h fn p q : R[X]}
    (hg : ∀ n : ℕ, (g - g0).coeff n ∈ Ideal.span ({π} : Set R))
    (hh : ∀ n : ℕ, (h - h0).coeff n ∈ Ideal.span ({π} : Set R))
    (hcorr :
      ∀ n : ℕ, (g0 * q + h0 * p - fn).coeff n ∈
        Ideal.span ({π} : Set R)) :
    ∀ n : ℕ, (g * q + h * p - fn).coeff n ∈
      Ideal.span ({π} : Set R) := by
  let φ : R →+* R ⧸ Ideal.span ({π} : Set R) :=
    Ideal.Quotient.mk (Ideal.span ({π} : Set R))
  have hgmap : g.map φ = g0.map φ := by
    simpa [φ] using
      (henselFactorization_map_quotient_eq_iff_sub_coeff_mem
        (Ideal.span ({π} : Set R)) g g0).2 hg
  have hhmap : h.map φ = h0.map φ := by
    simpa [φ] using
      (henselFactorization_map_quotient_eq_iff_sub_coeff_mem
        (Ideal.span ({π} : Set R)) h h0).2 hh
  have hcorrMap : (g0 * q + h0 * p - fn).map φ = 0 := by
    simpa [φ] using
      (henselFactorization_map_quotient_eq_zero_iff_coeff_mem
        (Ideal.span ({π} : Set R)) (g0 * q + h0 * p - fn)).2 hcorr
  have hmap : (g * q + h * p - fn).map φ = 0 := by
    calc
      (g * q + h * p - fn).map φ =
          g.map φ * q.map φ + h.map φ * p.map φ - fn.map φ := by
        exact henselFactorization_map_mul_add_mul_sub φ g h q p fn
      _ = g0.map φ * q.map φ + h0.map φ * p.map φ - fn.map φ := by
        rw [hgmap, hhmap]
      _ = (g0 * q + h0 * p - fn).map φ := by
        exact (henselFactorization_map_mul_add_mul_sub φ g0 h0 q p fn).symm
      _ = 0 := hcorrMap
  intro n
  exact
    (henselFactorization_map_quotient_eq_zero_iff_coeff_mem
      (Ideal.span ({π} : Set R)) (g * q + h * p - fn)).1
      (by simpa [φ] using hmap) n

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Henselian_Factorization_ErrorPowers
attribute [-instance] _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# the power step in Hensel's iteration

This file contains the `π^n`-to-`π^(n+1)` step in the coefficientwise proof of
Hensel's lemma.  The preceding files produce the correction congruence modulo
the maximal ideal; here it is converted into the actual improvement of the
factorization error after the update
`g ↦ g + π^n p`, `h ↦ h + π^n q`.
-/

noncomputable section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- coefficientwise divisibility gives a polynomial factor by
the corresponding `C a` polynomial. -/
theorem henselFactorization_exists_factor_of_coeff_mem_span_singleton
    {R : Type*} [CommRing R] {a : R} {P : R[X]}
    (hP : ∀ i : ℕ, P.coeff i ∈ Ideal.span ({a} : Set R)) :
    ∃ Q : R[X], P = Polynomial.C a * Q := by
  have hdvd : ∀ i : ℕ, a ∣ P.coeff i := by
    intro i
    simpa [Ideal.mem_span_singleton] using hP i
  exact (Polynomial.C_dvd_iff_dvd_coeff a P).2 hdvd

/-- the principal ideal generated by an element of an ideal is
contained in that ideal. -/
theorem henselFactorization_span_singleton_le_ideal_of_mem
    {R : Type*} [CommRing R] (I : Ideal R) {π : R} (hπ : π ∈ I) :
    Ideal.span ({π} : Set R) ≤ I := by
  rw [Ideal.span_le]
  intro x hx
  have hxπ : x = π := by simpa using hx
  simpa [hxπ] using hπ

/-- multiplying a coefficient congruent to zero modulo `π`
by `π^n` puts it in `(π^(n+1))`. -/
theorem henselFactorization_span_singleton_pow_mul_mem_succ
    {R : Type*} [CommRing R] {π x : R} (n : ℕ)
    (hx : x ∈ Ideal.span ({π} : Set R)) :
    π ^ n * x ∈ Ideal.span ({π ^ (n + 1)} : Set R) := by
  rcases (Ideal.mem_span_singleton'.mp hx) with ⟨c, hc⟩
  refine Ideal.mem_span_singleton'.mpr ⟨c, ?_⟩
  rw [← hc]
  rw [pow_succ]
  ring

/-- a positive power of `π` times any coefficient is
congruent to zero modulo `π`. -/
theorem henselFactorization_pow_mul_mem_span_singleton_of_pos
    {R : Type*} [CommRing R] {π x : R} {n : ℕ} (hn : 1 ≤ n) :
    π ^ n * x ∈ Ideal.span ({π} : Set R) := by
  refine Ideal.mem_span_singleton'.mpr ⟨π ^ (n - 1) * x, ?_⟩
  have hpow : π ^ (n - 1) * π = π ^ n := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  calc
    (π ^ (n - 1) * x) * π = (π ^ (n - 1) * π) * x := by ring
    _ = π ^ n * x := by rw [hpow]

/-- the quadratic term in the Hensel update is automatically
in `(π^(n+1))` once `n ≥ 1`. -/
theorem henselFactorization_span_singleton_pow_mul_pow_mem_succ_of_pos
    {R : Type*} [CommRing R] {π x : R} {n : ℕ} (hn : 1 ≤ n) :
    π ^ n * (π ^ n * x) ∈ Ideal.span ({π ^ (n + 1)} : Set R) :=
  henselFactorization_span_singleton_pow_mul_mem_succ
    (π := π) (x := π ^ n * x) n
    (henselFactorization_pow_mul_mem_span_singleton_of_pos
      (π := π) (x := x) hn)

/-- reversing the sign of a coefficientwise congruence modulo
the principal ideal `(π)`. -/
theorem henselFactorization_correction_congruence_symm_span_singleton
    {R : Type*} [CommRing R] {π : R} {A B : R[X]}
    (hcong : ∀ i : ℕ, (A - B).coeff i ∈ Ideal.span ({π} : Set R)) :
    ∀ i : ℕ, (B - A).coeff i ∈ Ideal.span ({π} : Set R) := by
  intro i
  have hneg :
      -((A - B).coeff i) ∈ Ideal.span ({π} : Set R) :=
    (Ideal.span ({π} : Set R)).neg_mem (hcong i)
  convert hneg using 1
  all_goals try with_reducible_and_instances rfl
  simp [Polynomial.coeff_sub]

/-- the algebraic power-improvement step: if
`f - g h = π^n f_n` and the chosen correction satisfies
`g q + h p ≡ f_n mod π`, then after the update
`g ↦ g + π^n p`, `h ↦ h + π^n q`, every coefficient of the new error lies in
`(π^(n+1))`. -/
theorem henselFactorization_power_update_error_coeff_mem_span_singleton
    {R : Type*} [CommRing R] {π : R} {n : ℕ} (hn : 1 ≤ n)
    {f g h fn p q : R[X]}
    (hfactor : f - g * h = Polynomial.C (π ^ n) * fn)
    (hcorr :
      ∀ i : ℕ, (g * q + h * p - fn).coeff i ∈
        Ideal.span ({π} : Set R)) :
    ∀ i : ℕ,
      (f - (g + Polynomial.C (π ^ n) * p) *
          (h + Polynomial.C (π ^ n) * q)).coeff i ∈
        Ideal.span ({π ^ (n + 1)} : Set R) := by
  intro i
  have hsymm :
      (fn - (g * q + h * p)).coeff i ∈ Ideal.span ({π} : Set R) :=
    henselFactorization_correction_congruence_symm_span_singleton
      (π := π) (A := g * q + h * p) (B := fn) hcorr i
  have hfirst :
      π ^ n * (fn - (g * q + h * p)).coeff i ∈
        Ideal.span ({π ^ (n + 1)} : Set R) :=
    henselFactorization_span_singleton_pow_mul_mem_succ (π := π) n hsymm
  have hsecond :
      π ^ n * (π ^ n * (p * q).coeff i) ∈
        Ideal.span ({π ^ (n + 1)} : Set R) :=
    henselFactorization_span_singleton_pow_mul_pow_mem_succ_of_pos
      (π := π) (x := (p * q).coeff i) hn
  have herr :
      f - (g + Polynomial.C (π ^ n) * p) *
          (h + Polynomial.C (π ^ n) * q) =
        Polynomial.C (π ^ n) * (fn - (g * q + h * p)) -
          Polynomial.C (π ^ n) * (Polynomial.C (π ^ n) * (p * q)) := by
    have hf : f = Polynomial.C (π ^ n) * fn + g * h := by
      calc
        f = (f - g * h) + g * h := by ring
        _ = Polynomial.C (π ^ n) * fn + g * h := by rw [hfactor]
    rw [hf]
    ring
  have hcoeff :
      (f - (g + Polynomial.C (π ^ n) * p) *
          (h + Polynomial.C (π ^ n) * q)).coeff i =
        π ^ n * (fn - (g * q + h * p)).coeff i -
          π ^ n * (π ^ n * (p * q).coeff i) := by
    rw [herr]
    simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  rw [hcoeff]
  exact (Ideal.span ({π ^ (n + 1)} : Set R)).sub_mem hfirst hsecond

/-- factor form of the power-improvement step. -/
theorem henselFactorization_power_update_error_factor_exists
    {R : Type*} [CommRing R] {π : R} {n : ℕ} (hn : 1 ≤ n)
    {f g h fn p q : R[X]}
    (hfactor : f - g * h = Polynomial.C (π ^ n) * fn)
    (hcorr :
      ∀ i : ℕ, (g * q + h * p - fn).coeff i ∈
        Ideal.span ({π} : Set R)) :
    ∃ fnNext : R[X],
      f - (g + Polynomial.C (π ^ n) * p) *
          (h + Polynomial.C (π ^ n) * q) =
        Polynomial.C (π ^ (n + 1)) * fnNext :=
  henselFactorization_exists_factor_of_coeff_mem_span_singleton
    (a := π ^ (n + 1))
    (P := f - (g + Polynomial.C (π ^ n) * p) *
      (h + Polynomial.C (π ^ n) * q))
    (henselFactorization_power_update_error_coeff_mem_span_singleton
      (π := π) hn hfactor hcorr)


end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Henselian_Factorization_CoefficientMinimum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# the finite minimum coefficient

The coefficientwise proof of Hensel's lemma chooses, among the finitely many
coefficients of `f - g₀h₀` and `ag₀ + bh₀ - 1`, one coefficient of minimum
valuation and calls it `π`.  In a valuation ring this is the same algebraic
input as choosing one coefficient that divides all coefficients in the finite
set.
-/

noncomputable section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- the finite set of coefficients of two polynomials from
which the construction chooses the minimum-value coefficient. -/
def henselFactorization_twoPolynomialCoeffFinset
    {R : Type*} [Semiring R] (P Q : R[X]) : Finset R := by
  classical
  exact P.support.image (fun n => P.coeff n) ∪
    Q.support.image (fun n => Q.coeff n)

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Henselian_Factorization_DegreeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# degree bounds for the error factors

This file supplies the degree estimates for the polynomials `f_n` appearing in
the coefficientwise Hensel iteration.
-/

noncomputable section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- if `deg f ≤ d`, `deg g ≤ m`, and `deg h ≤ d-m`, then
`deg(f-gh)≤d`. -/
theorem henselFactorization_error_natDegree_le
    {R : Type*} [CommRing R] {f g h : R[X]} {d m : ℕ}
    (hf : f.natDegree ≤ d) (hg : g.natDegree ≤ m)
    (hh : h.natDegree ≤ d - m) (hmd : m ≤ d) :
    (f - g * h).natDegree ≤ d := by
  have hmul : (g * h).natDegree ≤ d := by
    have hmul' : (g * h).natDegree ≤ m + (d - m) :=
      Polynomial.natDegree_mul_le_of_le hg hh
    have hsum : m + (d - m) = d := by
      rw [Nat.add_comm, Nat.sub_add_cancel hmd]
    simpa [hsum] using hmul'
  have hsub := Polynomial.natDegree_sub_le_of_le hf hmul
  simpa using hsub

/-- if `P=C(a)Q` with `a≠0`, then a degree bound on `P`
is a degree bound on `Q`. -/
theorem henselFactorization_factor_natDegree_le_of_constant_mul_eq
    {R : Type*} [CommRing R] [NoZeroDivisors R] {a : R} (ha : a ≠ 0)
    {P Q : R[X]} {d : ℕ}
    (hP : P.natDegree ≤ d) (hfactor : P = Polynomial.C a * Q) :
    Q.natDegree ≤ d := by
  have hCQ : (Polynomial.C a * Q).natDegree ≤ d := by
    simpa [hfactor] using hP
  simpa [Polynomial.natDegree_C_mul (p := Q) (a0 := ha)] using hCQ

/-- degree bound for the next error factor `f_n` from the
current factorization error. -/
theorem henselFactorization_error_factor_natDegree_le
    {R : Type*} [CommRing R] [NoZeroDivisors R] {π : R} {n : ℕ}
    (hπn : π ^ n ≠ 0)
    {f g h fn : R[X]} {d m : ℕ}
    (hf : f.natDegree ≤ d) (hg : g.natDegree ≤ m)
    (hh : h.natDegree ≤ d - m) (hmd : m ≤ d)
    (hfactor : f - g * h = Polynomial.C (π ^ n) * fn) :
    fn.natDegree ≤ d :=
  henselFactorization_factor_natDegree_le_of_constant_mul_eq
    (a := π ^ n) hπn
    (P := f - g * h) (Q := fn)
    (henselFactorization_error_natDegree_le hf hg hh hmd)
    hfactor

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Henselian_Factorization_Step
attribute [-instance] _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# one Hensel iteration step

This file packages the algebraic correction, degree truncation, and `π`-power
update into the single step used recursively in the proof of Hensel's
lemma.
-/

noncomputable section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- Algebraic splitting of an update by a `π^n`-multiple around the initial
lift. -/
theorem henselFactorization_update_sub_eq_initial_error_add
    {R : Type*} [CommRing R] {π : R} {n : ℕ} {g g0 p : R[X]} :
    g + Polynomial.C (π ^ n) * p - g0 =
      (g - g0) + Polynomial.C (π ^ n) * p := by
  ring

/-- adding a `π^n`-multiple preserves congruence modulo
`(π)` once `n ≥ 1`.  This is the inductive congruence needed for the
displayed-factor one-step update. -/
theorem henselFactorization_update_preserves_span_singleton
    {R : Type*} [CommRing R] {π : R} {n : ℕ} (hn : 1 ≤ n)
    {g g0 p : R[X]}
    (hg : ∀ i : ℕ, (g - g0).coeff i ∈ Ideal.span ({π} : Set R)) :
    ∀ i : ℕ,
      (g + Polynomial.C (π ^ n) * p - g0).coeff i ∈
        Ideal.span ({π} : Set R) := by
  intro i
  rw [henselFactorization_update_sub_eq_initial_error_add, Polynomial.coeff_add]
  refine (Ideal.span ({π} : Set R)).add_mem (hg i) ?_
  rw [Polynomial.coeff_C_mul]
  exact henselFactorization_pow_mul_mem_span_singleton_of_pos
    (π := π) (x := p.coeff i) hn

/-- displayed-factor one recursive Hensel step from the division
data.  The congruence modulo `(π)` is produced from the displayed Bezout-error
factor, and the update needs only `π ∈ m`, not `m ≤ (π)`. -/
theorem henselFactorization_one_step_update_from_division_data_of_mem_span
    {R : Type*} [CommRing R] [IsLocalRing R] {π : R} {n : ℕ} (hn : 1 ≤ n)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 g h fn a b qdiv p e : R[X]} {m d : ℕ}
    (hfactor : f - g * h = Polynomial.C (π ^ n) * fn)
    (hg : ∀ i : ℕ, (g - g0).coeff i ∈ Ideal.span ({π} : Set R))
    (hh : ∀ i : ℕ, (h - h0).coeff i ∈ Ideal.span ({π} : Set R))
    (hgunit : IsUnit g0.leadingCoeff)
    (hg0nat : g0.natDegree = m)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hdiv : b * fn = g0 * qdiv + p)
    (hfn : fn.natDegree ≤ d)
    (hh0 : h0.natDegree ≤ d - m)
    (hp : p.natDegree ≤ m)
    (hmd : m ≤ d) :
    (henselFactorization_lowPart (d - m) (a * fn + h0 * qdiv)).natDegree ≤ d - m ∧
      (∀ i : ℕ,
        (g + Polynomial.C (π ^ n) * p - g0).coeff i ∈
          Ideal.span ({π} : Set R)) ∧
        (∀ i : ℕ,
          (h + Polynomial.C (π ^ n) *
              henselFactorization_lowPart (d - m) (a * fn + h0 * qdiv) - h0).coeff i ∈
            Ideal.span ({π} : Set R)) ∧
          (∀ i : ℕ,
            (g + Polynomial.C (π ^ n) * p - g0).coeff i ∈
              IsLocalRing.maximalIdeal R) ∧
            (∀ i : ℕ,
              (h + Polynomial.C (π ^ n) *
                  henselFactorization_lowPart (d - m) (a * fn + h0 * qdiv) - h0).coeff i ∈
                IsLocalRing.maximalIdeal R) ∧
              ∃ fnNext : R[X],
                f - (g + Polynomial.C (π ^ n) * p) *
                    (h + Polynomial.C (π ^ n) *
                      henselFactorization_lowPart (d - m) (a * fn + h0 * qdiv)) =
                  Polynomial.C (π ^ (n + 1)) * fnNext := by
  rcases henselFactorization_correction_after_division_degree_truncation_span_singleton
      (π := π) hπmem hgunit hg0nat hbezFactor hdiv hfn hh0 hp hmd with
    ⟨hqdeg, hcorrInitial⟩
  have hcorrCurrent :
      ∀ i : ℕ,
        (g * henselFactorization_lowPart (d - m) (a * fn + h0 * qdiv) +
            h * p - fn).coeff i ∈ Ideal.span ({π} : Set R) :=
    henselFactorization_correction_congruence_replace_initial_factors_span_singleton
      (π := π) (g0 := g0) (h0 := h0) (g := g) (h := h)
      (fn := fn) (p := p)
      (q := henselFactorization_lowPart (d - m) (a * fn + h0 * qdiv))
      hg hh hcorrInitial
  have hgNext :
      ∀ i : ℕ,
        (g + Polynomial.C (π ^ n) * p - g0).coeff i ∈
          Ideal.span ({π} : Set R) :=
    henselFactorization_update_preserves_span_singleton (π := π) hn hg
  have hhNext :
      ∀ i : ℕ,
        (h + Polynomial.C (π ^ n) *
            henselFactorization_lowPart (d - m) (a * fn + h0 * qdiv) - h0).coeff i ∈
          Ideal.span ({π} : Set R) :=
    henselFactorization_update_preserves_span_singleton (π := π) hn hh
  have hspan_le :
      Ideal.span ({π} : Set R) ≤ IsLocalRing.maximalIdeal R :=
    henselFactorization_span_singleton_le_ideal_of_mem
      (IsLocalRing.maximalIdeal R) hπmem
  refine ⟨hqdeg, hgNext, hhNext, ?_, ?_, ?_⟩
  · intro i
    exact hspan_le (hgNext i)
  · intro i
    exact hspan_le (hhNext i)
  · exact henselFactorization_power_update_error_factor_exists
      (π := π) hn hfactor hcorrCurrent


end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Henselian_Factorization_Iteration
attribute [-instance] _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# recursive Hensel iterates

This file records the recursive polynomial iterates used in the proof
of Hensel's lemma and the coefficientwise adic estimates needed for the later
completion argument.
-/

noncomputable section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- the recursive polynomial sequence
`F_{n+1}=F_n+π^(n+1)c_{n+1}` used for either factor in Hensel's iteration. -/
def henselFactorization_henselIterate {R : Type*} [CommRing R]
    (π : R) (F0 : R[X]) (corr : ℕ → R[X]) : ℕ → R[X]
  | 0 => F0
  | n + 1 =>
      henselFactorization_henselIterate π F0 corr n +
        Polynomial.C (π ^ (n + 1)) * corr (n + 1)

@[simp]
theorem henselFactorization_henselIterate_zero
    {R : Type*} [CommRing R] (π : R) (F0 : R[X]) (corr : ℕ → R[X]) :
    henselFactorization_henselIterate π F0 corr 0 = F0 :=
  rfl

@[simp]
theorem henselFactorization_henselIterate_succ
    {R : Type*} [CommRing R] (π : R) (F0 : R[X]) (corr : ℕ → R[X])
    (n : ℕ) :
    henselFactorization_henselIterate π F0 corr (n + 1) =
      henselFactorization_henselIterate π F0 corr n +
        Polynomial.C (π ^ (n + 1)) * corr (n + 1) :=
  rfl

/-- every recursive iterate is congruent to its initial lift
modulo `(π)`.  This is built into the update formula and does not require
`(π)` to be the maximal ideal. -/
theorem henselFactorization_henselIterate_span_singleton
    {R : Type*} [CommRing R] {π : R}
    (F0 : R[X]) (corr : ℕ → R[X]) :
    ∀ n i : ℕ,
      (henselFactorization_henselIterate π F0 corr n - F0).coeff i ∈
        Ideal.span ({π} : Set R) := by
  intro n
  induction n with
  | zero =>
      intro i
      simp
  | succ n ih =>
      intro i
      simpa [henselFactorization_henselIterate_succ] using
        (henselFactorization_update_preserves_span_singleton
          (π := π) (n := n + 1)
          (g := henselFactorization_henselIterate π F0 corr n)
          (g0 := F0) (p := corr (n + 1))
          (Nat.succ_pos n) ih i)


end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Henselian_Factorization_InfiniteApproximation
attribute [-instance] _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# compatible Hensel prefixes

This file turns the finite Hensel-prefix construction into a recursive family
of compatible prefixes.  The completion/limit argument is kept for the next
layer.
-/

noncomputable section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- the data carried by a finite Hensel prefix at stage `N`.
The fields are exactly the invariants needed to extend the prefix one more
step and later pass to the complete limit. -/
structure HenselFactorizationFinitePrefixState
    {R : Type*} [CommRing R] [IsLocalRing R] (π : R)
    (f g0 h0 : R[X]) (m d N : ℕ) where
  /-- The polynomial corrections for the first factor at each stage. -/
  pCorr : ℕ → R[X]
  /-- The polynomial corrections for the second factor at each stage. -/
  qCorr : ℕ → R[X]
  /-- The residual error polynomial at the current stage. -/
  fErr : R[X]
  /-- Every prefix through the current stage factors the error by the corresponding power of `π`. -/
  prefixFactor :
    ∀ r : ℕ, r ≤ N →
      ∃ fr : R[X],
        f - henselFactorization_henselIterate π g0 pCorr r *
            henselFactorization_henselIterate π h0 qCorr r =
          Polynomial.C (π ^ (r + 1)) * fr
  /-- Each correction for the first factor has degree at most `m`. -/
  pCorrDeg : ∀ r : ℕ, (pCorr r).natDegree ≤ m
  /-- Each correction for the second factor has degree at most `d - m`. -/
  qCorrDeg : ∀ r : ℕ, (qCorr r).natDegree ≤ d - m
  /-- At stage `N`, the factorization error is `π ^ (N + 1)` times `fErr`. -/
  factor :
    f - henselFactorization_henselIterate π g0 pCorr N *
        henselFactorization_henselIterate π h0 qCorr N =
      Polynomial.C (π ^ (N + 1)) * fErr
  /-- The first approximate factor at stage `N` has degree at most `m`. -/
  gDeg : (henselFactorization_henselIterate π g0 pCorr N).natDegree ≤ m
  /-- The second approximate factor at stage `N` has degree at most `d - m`. -/
  hDeg : (henselFactorization_henselIterate π h0 qCorr N).natDegree ≤ d - m
  /-- The first approximate factor remains congruent to `g0` modulo the maximal ideal. -/
  gRed :
    ∀ i : ℕ,
      (henselFactorization_henselIterate π g0 pCorr N - g0).coeff i ∈
        IsLocalRing.maximalIdeal R
  /-- The second approximate factor remains congruent to `h0` modulo the maximal ideal. -/
  hRed :
    ∀ i : ℕ,
      (henselFactorization_henselIterate π h0 qCorr N - h0).coeff i ∈
        IsLocalRing.maximalIdeal R


end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_AbsoluteValue_PrincipalAdicCompleteness
attribute [-instance] _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Principal adic filtrations in complete nonarchimedean valuation rings

For a complete nonarchimedean absolute value, a nonzero element of the open
unit ball generates a separated and precomplete principal filtration on the
closed unit ball.  These facts are shared by the coefficientwise Hensel
construction and the irreducible-polynomial coefficient estimate.
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

/-- Membership in the `π`-adic principal power is exactly the corresponding
absolute-value bound on the closed unit ball of a nonarchimedean valued field. -/
theorem principal_pow_mem_iff_abs_le
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    {π x : absoluteValueValuationSubring v hnonarch}
    (hπne : π ≠ 0) (n : ℕ) :
    x ∈ (Ideal.span ({π} : Set
        (absoluteValueValuationSubring v hnonarch))) ^ n ↔
      v (x : K) ≤ v ((π : absoluteValueValuationSubring v hnonarch) : K) ^ n := by
  let V := absoluteValueValuationSubring v hnonarch
  have hπK_ne : ((π : V) : K) ≠ 0 := by
    intro hzero
    exact hπne (Subtype.ext hzero)
  constructor
  · intro hx
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
    rcases hx with ⟨c, hc⟩
    have hc_abs : v ((c : V) : K) ≤ 1 :=
      (mem_absoluteValueValuationSubring_iff
        v hnonarch ((c : V) : K)).1 c.property
    calc
      v (x : K) = v ((((π : V) : K) ^ n) * ((c : V) : K)) := by
        exact congrArg (fun y : V => v ((y : V) : K)) hc
      _ = v (((π : V) : K) ^ n) * v ((c : V) : K) := by rw [v.map_mul]
      _ = v ((π : V) : K) ^ n * v ((c : V) : K) := by rw [map_pow]
      _ ≤ v ((π : V) : K) ^ n * 1 :=
        mul_le_mul_of_nonneg_left hc_abs (pow_nonneg (v.nonneg _) n)
      _ = v ((π : V) : K) ^ n := by rw [mul_one]
  · intro hx
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    let cK : K := (x : K) / (((π : V) : K) ^ n)
    have hπpow_pos : 0 < v (((π : V) : K) ^ n) := by
      exact v.pos (pow_ne_zero n hπK_ne)
    have hcK_mem : cK ∈ V := by
      rw [mem_absoluteValueValuationSubring_iff]
      have hdiv :
          v cK = v (x : K) / v (((π : V) : K) ^ n) := by
        change v ((x : K) / (((π : V) : K) ^ n)) =
          v (x : K) / v (((π : V) : K) ^ n)
        rw [div_eq_mul_inv, v.map_mul, map_inv₀, div_eq_mul_inv]
      rw [hdiv]
      exact div_le_one_of_le₀ (by simpa [map_pow] using hx) (le_of_lt hπpow_pos)
    refine ⟨⟨cK, hcK_mem⟩, ?_⟩
    apply Subtype.ext
    change (x : K) = (((π : V) : K) ^ n) * cK
    change (x : K) =
      (((π : V) : K) ^ n) * ((x : K) / (((π : V) : K) ^ n))
    rw [mul_comm, div_mul_cancel₀]
    exact pow_ne_zero n hπK_ne

/-- Principal congruence modulo `(π)^n` is exactly an absolute-value bound for
the difference. -/
theorem principal_smodEq_iff_abs_sub_le
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    {π x y : absoluteValueValuationSubring v hnonarch}
    (hπne : π ≠ 0) {n : ℕ} :
    x ≡ y [SMOD
      ((Ideal.span ({π} : Set
        (absoluteValueValuationSubring v hnonarch))) ^ n •
          ⊤ : Submodule
            (absoluteValueValuationSubring v hnonarch)
            (absoluteValueValuationSubring v hnonarch))] ↔
    v ((x : K) - (y : K)) ≤
      v ((π : absoluteValueValuationSubring v hnonarch) : K) ^ n := by
  let V := absoluteValueValuationSubring v hnonarch
  constructor
  · intro hxy
    have hmem : (x - y : V) ∈ (Ideal.span ({π} : Set V)) ^ n := by
      have h := SModEq.sub_mem.mp hxy
      simpa [smul_eq_mul, Ideal.mul_top, V] using h
    simpa using
      (principal_pow_mem_iff_abs_le
        v hnonarch (π := π) (x := x - y) hπne n).1 hmem
  · intro hxy
    rw [SModEq.sub_mem]
    have hmem : (x - y : V) ∈ (Ideal.span ({π} : Set V)) ^ n := by
      rw [principal_pow_mem_iff_abs_le
        v hnonarch (π := π) (x := x - y) hπne n]
      simpa using hxy
    simpa [smul_eq_mul, Ideal.mul_top, V] using hmem

/-- Forward direction of
`principal_smodEq_iff_abs_sub_le`. -/
theorem abs_sub_le_of_principal_smodEq
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    {π x y : absoluteValueValuationSubring v hnonarch}
    (hπne : π ≠ 0) {n : ℕ}
    (hxy : x ≡ y [SMOD
      ((Ideal.span ({π} : Set
        (absoluteValueValuationSubring v hnonarch))) ^ n •
          ⊤ : Submodule
            (absoluteValueValuationSubring v hnonarch)
            (absoluteValueValuationSubring v hnonarch))]) :
    v ((x : K) - (y : K)) ≤
      v ((π : absoluteValueValuationSubring v hnonarch) : K) ^ n :=
  (principal_smodEq_iff_abs_sub_le
    v hnonarch (π := π) (x := x) (y := y) hπne).1 hxy

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Henselian_IrreduciblePolynomialBounds
attribute [-instance] _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# reduction input for the coefficient estimate

This file isolates the residue-polynomial input used in the
irreducible-polynomial coefficient estimate.  For the closed-unit-ball valuation ring attached to a nonarchimedean
absolute value, coefficients of value `< 1` reduce to zero and coefficients of
value `1` reduce to nonzero elements.  Hence the first coefficient of value
`1` gives the exact initial `X`-power dividing the reduced polynomial.
-/

noncomputable section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- reduction input: a coefficient of absolute value `< 1`
reduces to the zero coefficient of the residue polynomial. -/
theorem irreduciblePolynomial_reduction_coeff_eq_zero_of_abs_lt_one
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (F : (absoluteValueValuationSubring v hnonarch)[X])
    {i : ℕ} (hi : v (F.coeff i : K) < 1) :
    (F.map (IsLocalRing.residue
        (absoluteValueValuationSubring v hnonarch))).coeff i =
      0 := by
  rw [Polynomial.coeff_map]
  exact
    (absoluteValueUnitBallSubringAsValuationSubring_residue_eq_zero_iff_abs_lt_one
      v hnonarch (F.coeff i)).2 hi

/-- reduction input: a coefficient of absolute value `1`
reduces to a nonzero coefficient of the residue polynomial. -/
theorem irreduciblePolynomial_reduction_coeff_ne_zero_of_abs_eq_one
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (F : (absoluteValueValuationSubring v hnonarch)[X])
    {i : ℕ} (hi : v (F.coeff i : K) = 1) :
    (F.map (IsLocalRing.residue
        (absoluteValueValuationSubring v hnonarch))).coeff i ≠
      0 := by
  rw [Polynomial.coeff_map]
  exact
    (absoluteValueUnitBallSubringAsValuationSubring_residue_ne_zero_iff_abs_eq_one
      v hnonarch (F.coeff i)).2 hi

/-- reduction input: if all coefficients below `r` have
absolute value `< 1`, then `X^r` divides the reduced polynomial. -/
theorem irreduciblePolynomial_reduction_X_pow_dvd_of_initial_abs_lt_one
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (F : (absoluteValueValuationSubring v hnonarch)[X])
    {r : ℕ} (hinit : ∀ i : ℕ, i < r → v (F.coeff i : K) < 1) :
    Polynomial.X ^ r ∣
      F.map (IsLocalRing.residue
        (absoluteValueValuationSubring v hnonarch)) := by
  rw [Polynomial.X_pow_dvd_iff]
  intro i hi
  exact irreduciblePolynomial_reduction_coeff_eq_zero_of_abs_lt_one
    v hnonarch F (hinit i hi)

/-- reduction input: if `r` is the first coefficient with
absolute value `1`, then the reduced polynomial is divisible by exactly
`X^r` at the origin. -/
theorem irreduciblePolynomial_reduction_exact_X_pow_of_first_abs_eq_one
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (F : (absoluteValueValuationSubring v hnonarch)[X])
    {r : ℕ} (hinit : ∀ i : ℕ, i < r → v (F.coeff i : K) < 1)
    (hr : v (F.coeff r : K) = 1) :
    Polynomial.X ^ r ∣
        F.map (IsLocalRing.residue
          (absoluteValueValuationSubring v hnonarch)) ∧
      ¬ Polynomial.X ^ (r + 1) ∣
        F.map (IsLocalRing.residue
          (absoluteValueValuationSubring v hnonarch)) := by
  constructor
  · exact irreduciblePolynomial_reduction_X_pow_dvd_of_initial_abs_lt_one
      v hnonarch F hinit
  · intro hdiv
    have hcoeff_zero :
        (F.map (IsLocalRing.residue
          (absoluteValueValuationSubring v hnonarch))).coeff r =
          0 := by
      rw [Polynomial.X_pow_dvd_iff] at hdiv
      exact hdiv r (Nat.lt_succ_self r)
    exact (irreduciblePolynomial_reduction_coeff_ne_zero_of_abs_eq_one
      v hnonarch F hr) hcoeff_zero

/-- reduction input: from any coefficient of value `1`, choose
the first such coefficient.  Every earlier coefficient then has value `< 1`
because all coefficients already lie in the closed unit ball. -/
theorem irreduciblePolynomial_exists_first_abs_eq_one_coeff
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (F : (absoluteValueValuationSubring v hnonarch)[X])
    {n : ℕ} (hn : v (F.coeff n : K) = 1) :
    ∃ r : ℕ,
      v (F.coeff r : K) = 1 ∧
        ∀ i : ℕ, i < r → v (F.coeff i : K) < 1 := by
  classical
  let P : ℕ → Prop := fun i => v (F.coeff i : K) = 1
  have hex : ∃ i : ℕ, P i := ⟨n, hn⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  intro i hi
  have hne : v (F.coeff i : K) ≠ 1 :=
    Nat.find_min hex hi
  have hle : v (F.coeff i : K) ≤ 1 :=
    (mem_absoluteValueValuationSubring_iff
      v hnonarch (F.coeff i : K)).1 (F.coeff i).property
  exact lt_of_le_of_ne hle hne

/-- reduction input: if some coefficient has value `1`, then
the reduced polynomial has an exact initial `X^r` divisor for the first such
coefficient `r`. -/
theorem irreduciblePolynomial_exists_exact_X_pow_reduction_of_abs_eq_one_coeff
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (F : (absoluteValueValuationSubring v hnonarch)[X])
    {n : ℕ} (hn : v (F.coeff n : K) = 1) :
    ∃ r : ℕ,
      v (F.coeff r : K) = 1 ∧
        Polynomial.X ^ r ∣
            F.map (IsLocalRing.residue
              (absoluteValueValuationSubring v hnonarch)) ∧
          ¬ Polynomial.X ^ (r + 1) ∣
            F.map (IsLocalRing.residue
              (absoluteValueValuationSubring v hnonarch)) := by
  rcases irreduciblePolynomial_exists_first_abs_eq_one_coeff v hnonarch F hn with
    ⟨r, hr, hinit⟩
  exact ⟨r, hr,
    irreduciblePolynomial_reduction_exact_X_pow_of_first_abs_eq_one
      v hnonarch F hinit hr⟩

/-- reduction input: if the degree-zero coefficient has absolute
value `< 1`, then the first coefficient of value `1` has positive index. -/
theorem irreduciblePolynomial_first_abs_eq_one_index_pos_of_const_abs_lt_one
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (F : (absoluteValueValuationSubring v hnonarch)[X])
    {r : ℕ} (hconst : v (F.coeff 0 : K) < 1)
    (hr : v (F.coeff r : K) = 1) :
    0 < r := by
  refine Nat.pos_of_ne_zero ?_
  intro hr0
  have hcoeff0 : v (F.coeff 0 : K) = 1 := by
    simpa [hr0] using hr
  have hlt : (1 : ℝ) < 1 := by
    simp [hcoeff0] at hconst ⊢
  exact (lt_irrefl (1 : ℝ)) hlt

/-- A coefficient whose absolute value is `1` is nonzero.  This small
field-level fact is used repeatedly when passing from coefficient estimates to
degree bounds. -/
theorem irreduciblePolynomial_coeff_ne_zero_of_abs_eq_one
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (F : (absoluteValueValuationSubring v hnonarch)[X])
    {i : ℕ} (hi : v (F.coeff i : K) = 1) :
    F.coeff i ≠ 0 := by
  intro hzero
  simp [hzero] at hi

/-- reduction input: if the leading coefficient has absolute
value `< 1`, then a coefficient of value `1` occurs strictly before the
natural degree. -/
theorem irreduciblePolynomial_abs_eq_one_index_lt_natDegree_of_leading_abs_lt_one
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (F : (absoluteValueValuationSubring v hnonarch)[X])
    {r : ℕ} (hlead : v (F.leadingCoeff : K) < 1)
    (hr : v (F.coeff r : K) = 1) :
    r < F.natDegree := by
  have hle : r ≤ F.natDegree :=
    Polynomial.le_natDegree_of_ne_zero
      (irreduciblePolynomial_coeff_ne_zero_of_abs_eq_one v hnonarch F hr)
  have hne : r ≠ F.natDegree := by
    intro hrdeg
    have hlead_eq : v (F.leadingCoeff : K) = 1 := by
      simpa [Polynomial.leadingCoeff, hrdeg.symm] using hr
    have hlt : (1 : ℝ) < 1 := by
      simp [hlead_eq] at hlead ⊢
    exact (lt_irrefl (1 : ℝ)) hlt
  exact lt_of_le_of_ne hle hne

/-- reduction input: exact `X^r` divisibility rewrites the
reduced polynomial as `X^r` times its monic quotient. -/
theorem irreduciblePolynomial_reduction_eq_X_pow_mul_divByMonic_of_X_pow_dvd
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (F : (absoluteValueValuationSubring v hnonarch)[X])
    {r : ℕ}
    (hdiv : Polynomial.X ^ r ∣
      F.map (IsLocalRing.residue
        (absoluteValueValuationSubring v hnonarch))) :
    F.map (IsLocalRing.residue
        (absoluteValueValuationSubring v hnonarch)) =
      Polynomial.X ^ r *
        (F.map (IsLocalRing.residue
          (absoluteValueValuationSubring v hnonarch)) /ₘ
            Polynomial.X ^ r) := by
  let P :=
    F.map (IsLocalRing.residue
      (absoluteValueValuationSubring v hnonarch))
  have hmonic : (Polynomial.X ^ r :
      (IsLocalRing.ResidueField
        (absoluteValueValuationSubring v hnonarch))[X]).Monic :=
    Polynomial.monic_X_pow r
  have hmod : P %ₘ Polynomial.X ^ r = 0 :=
    (Polynomial.modByMonic_eq_zero_iff_dvd hmonic).2 hdiv
  have hdecomp := Polynomial.modByMonic_add_div P (Polynomial.X ^ r)
  rw [hmod, zero_add] at hdecomp
  simpa [P] using hdecomp.symm

/-- reduction input: exact nondivisibility by `X^(r+1)` says
that the monic quotient by `X^r` has nonzero degree-zero coefficient. -/
theorem irreduciblePolynomial_reduction_divByMonic_X_pow_coeff_zero_ne_zero
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (F : (absoluteValueValuationSubring v hnonarch)[X])
    {r : ℕ}
    (hdiv : Polynomial.X ^ r ∣
      F.map (IsLocalRing.residue
        (absoluteValueValuationSubring v hnonarch)))
    (hnotdiv : ¬ Polynomial.X ^ (r + 1) ∣
      F.map (IsLocalRing.residue
        (absoluteValueValuationSubring v hnonarch))) :
    ((F.map (IsLocalRing.residue
        (absoluteValueValuationSubring v hnonarch)) /ₘ
          Polynomial.X ^ r).coeff 0) ≠ 0 := by
  let P :=
    F.map (IsLocalRing.residue
      (absoluteValueValuationSubring v hnonarch))
  let Q := P /ₘ Polynomial.X ^ r
  have hfac : P = Polynomial.X ^ r * Q := by
    simpa [P, Q] using
      irreduciblePolynomial_reduction_eq_X_pow_mul_divByMonic_of_X_pow_dvd
        v hnonarch F hdiv
  intro hQ0
  have hXdvdQ : Polynomial.X ∣ Q := by
    rw [Polynomial.X_dvd_iff]
    exact hQ0
  rcases hXdvdQ with ⟨T, hT⟩
  apply hnotdiv
  refine ⟨T, ?_⟩
  calc
    P = Polynomial.X ^ r * Q := hfac
    _ = Polynomial.X ^ r * (Polynomial.X * T) := by rw [hT]
    _ = Polynomial.X ^ (r + 1) * T := by
      rw [pow_succ, mul_assoc]

/-- Hensel input: if the quotient after removing the exact
initial `X^r` factor has nonzero degree-zero coefficient, then it is coprime
to `X^r`. -/
theorem irreduciblePolynomial_reduction_X_pow_isCoprime_divByMonic_of_coeff_zero_ne_zero
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (F : (absoluteValueValuationSubring v hnonarch)[X])
    {r : ℕ}
    (hQ0 :
      ((F.map (IsLocalRing.residue
        (absoluteValueValuationSubring v hnonarch)) /ₘ
          Polynomial.X ^ r).coeff 0) ≠ 0) :
    IsCoprime (Polynomial.X ^ r)
      (F.map (IsLocalRing.residue
        (absoluteValueValuationSubring v hnonarch)) /ₘ
          Polynomial.X ^ r) := by
  let P :=
    F.map (IsLocalRing.residue
      (absoluteValueValuationSubring v hnonarch))
  let Q := P /ₘ Polynomial.X ^ r
  have hnotX :
      ¬ (Polynomial.X :
          (IsLocalRing.ResidueField
            (absoluteValueValuationSubring v hnonarch))[X]) ∣
        Q := by
    intro hX
    exact hQ0 (by
      simpa [P, Q] using (Polynomial.X_dvd_iff.mp hX))
  have hcopX :
      IsCoprime
        (Polynomial.X :
          (IsLocalRing.ResidueField
            (absoluteValueValuationSubring v hnonarch))[X])
        Q := by
    exact
      (Polynomial.prime_X
        (R := IsLocalRing.ResidueField
          (absoluteValueValuationSubring v hnonarch))).coprime_iff_not_dvd.2
        hnotX
  simpa [P, Q] using (hcopX.pow_left (m := r))

/-- Hensel input: exact `X^r` divisibility of the reduction
supplies the coprime factor pair `X^r` and the remaining quotient. -/
theorem irreduciblePolynomial_reduction_X_pow_isCoprime_divByMonic_of_exact
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (F : (absoluteValueValuationSubring v hnonarch)[X])
    {r : ℕ}
    (hdiv : Polynomial.X ^ r ∣
      F.map (IsLocalRing.residue
        (absoluteValueValuationSubring v hnonarch)))
    (hnotdiv : ¬ Polynomial.X ^ (r + 1) ∣
      F.map (IsLocalRing.residue
        (absoluteValueValuationSubring v hnonarch))) :
    IsCoprime (Polynomial.X ^ r)
      (F.map (IsLocalRing.residue
        (absoluteValueValuationSubring v hnonarch)) /ₘ
          Polynomial.X ^ r) := by
  exact
    irreduciblePolynomial_reduction_X_pow_isCoprime_divByMonic_of_coeff_zero_ne_zero
      v hnonarch F
      (irreduciblePolynomial_reduction_divByMonic_X_pow_coeff_zero_ne_zero
        v hnonarch F hdiv hnotdiv)

/-- reduction input: under the endpoint inequalities used in
the proof, the first coefficient of value `1` gives a nontrivial exact
initial `X^r` divisor with `0 < r < natDegree`. -/
theorem irreduciblePolynomial_exists_nontrivial_exact_X_pow_reduction
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (F : (absoluteValueValuationSubring v hnonarch)[X])
    (hconst : v (F.coeff 0 : K) < 1)
    (hlead : v (F.leadingCoeff : K) < 1)
    {n : ℕ} (hn : v (F.coeff n : K) = 1) :
    ∃ r : ℕ,
      0 < r ∧ r < F.natDegree ∧
        v (F.coeff r : K) = 1 ∧
          Polynomial.X ^ r ∣
              F.map (IsLocalRing.residue
                (absoluteValueValuationSubring v hnonarch)) ∧
            ¬ Polynomial.X ^ (r + 1) ∣
              F.map (IsLocalRing.residue
                (absoluteValueValuationSubring v hnonarch)) := by
  rcases irreduciblePolynomial_exists_exact_X_pow_reduction_of_abs_eq_one_coeff
      v hnonarch F hn with
    ⟨r, hr, hdiv, hnotdiv⟩
  exact ⟨r,
    irreduciblePolynomial_first_abs_eq_one_index_pos_of_const_abs_lt_one
      v hnonarch F hconst hr,
    irreduciblePolynomial_abs_eq_one_index_lt_natDegree_of_leading_abs_lt_one
      v hnonarch F hlead hr,
    hr, hdiv, hnotdiv⟩

/-- Hensel input: under the endpoint inequalities used in the
proof, the reduction has a nontrivial monic factor `X^r`, the remaining
quotient, and these two factors are coprime. -/
theorem irreduciblePolynomial_exists_hensel_reduction_factor_input
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (F : (absoluteValueValuationSubring v hnonarch)[X])
    (hconst : v (F.coeff 0 : K) < 1)
    (hlead : v (F.leadingCoeff : K) < 1)
    {n : ℕ} (hn : v (F.coeff n : K) = 1) :
    ∃ r : ℕ,
      0 < r ∧ r < F.natDegree ∧
        F.map (IsLocalRing.residue
            (absoluteValueValuationSubring v hnonarch)) =
          Polynomial.X ^ r *
            (F.map (IsLocalRing.residue
              (absoluteValueValuationSubring v hnonarch)) /ₘ
                Polynomial.X ^ r) ∧
          (Polynomial.X ^ r :
            (IsLocalRing.ResidueField
              (absoluteValueValuationSubring v hnonarch))[X]).natDegree =
            r ∧
            IsCoprime (Polynomial.X ^ r)
              (F.map (IsLocalRing.residue
                (absoluteValueValuationSubring v hnonarch)) /ₘ
                  Polynomial.X ^ r) ∧
              ((F.map (IsLocalRing.residue
                (absoluteValueValuationSubring v hnonarch)) /ₘ
                  Polynomial.X ^ r).coeff 0) ≠ 0 := by
  rcases irreduciblePolynomial_exists_nontrivial_exact_X_pow_reduction
      v hnonarch F hconst hlead hn with
    ⟨r, hrpos, hrlt, _hr, hdiv, hnotdiv⟩
  refine ⟨r, hrpos, hrlt, ?_, ?_, ?_, ?_⟩
  · exact irreduciblePolynomial_reduction_eq_X_pow_mul_divByMonic_of_X_pow_dvd
      v hnonarch F hdiv
  · exact Polynomial.natDegree_X_pow r
  · exact irreduciblePolynomial_reduction_X_pow_isCoprime_divByMonic_of_exact
      v hnonarch F hdiv hnotdiv
  · exact irreduciblePolynomial_reduction_divByMonic_X_pow_coeff_zero_ne_zero
      v hnonarch F hdiv hnotdiv

/-- field-polynomial input: once a field polynomial has been
normalized so that every coefficient lies in the closed unit ball and one
coefficient has value `1`, the endpoint inequalities produce the same Hensel
reduction factor data after choosing a degree-preserving valuation-ring lift. -/
theorem irreduciblePolynomial_exists_hensel_reduction_factor_input_of_field_coeffs
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (f : K[X])
    (hfcoeff : ∀ i : ℕ, v (f.coeff i) ≤ 1)
    (hconst : v (f.coeff 0) < 1)
    (hlead : v f.leadingCoeff < 1)
    {n : ℕ} (hn : v (f.coeff n) = 1) :
    ∃ F : (absoluteValueValuationSubring v hnonarch)[X],
      ∃ r : ℕ,
        F.map (algebraMap
            (absoluteValueValuationSubring v hnonarch) K) =
          f ∧
        F.natDegree = f.natDegree ∧
          0 < r ∧ r < F.natDegree ∧
            F.map (IsLocalRing.residue
                (absoluteValueValuationSubring v hnonarch)) =
              Polynomial.X ^ r *
                (F.map (IsLocalRing.residue
                  (absoluteValueValuationSubring v hnonarch)) /ₘ
                    Polynomial.X ^ r) ∧
              (Polynomial.X ^ r :
                (IsLocalRing.ResidueField
                  (absoluteValueValuationSubring v hnonarch))[X]).natDegree =
                r ∧
                IsCoprime (Polynomial.X ^ r)
                  (F.map (IsLocalRing.residue
                    (absoluteValueValuationSubring v hnonarch)) /ₘ
                      Polynomial.X ^ r) ∧
                  ((F.map (IsLocalRing.residue
                    (absoluteValueValuationSubring v hnonarch)) /ₘ
                      Polynomial.X ^ r).coeff 0) ≠ 0 := by
  rcases
      exists_polynomial_over_absoluteValueUnitBallSubringAsValuationSubring_of_coeff_abs_le_one
        v hnonarch f hfcoeff with
    ⟨F, hmap, hdegree, hcoeff_abs⟩
  have hconstF : v (F.coeff 0 : K) < 1 := by
    simpa [hcoeff_abs 0] using hconst
  have hleadF : v (F.leadingCoeff : K) < 1 := by
    have hlead_abs :
        v (F.leadingCoeff : K) = v f.leadingCoeff := by
      rw [Polynomial.leadingCoeff, Polynomial.leadingCoeff, ← hdegree]
      exact hcoeff_abs F.natDegree
    simpa [hlead_abs] using hlead
  have hnF : v (F.coeff n : K) = 1 := by
    simpa [hcoeff_abs n] using hn
  rcases irreduciblePolynomial_exists_hensel_reduction_factor_input
      v hnonarch F hconstF hleadF hnF with
    ⟨r, hrpos, hrlt, hfactor, hnatDegree, hcoprime, hQ0⟩
  exact
    ⟨F, r, hmap, hdegree, hrpos, hrlt, hfactor, hnatDegree, hcoprime, hQ0⟩

/-- normalization source: a nonzero polynomial has a positive
maximum among the absolute values of its coefficients, attained within the
finite coefficient range up to `natDegree`. -/
theorem irreduciblePolynomial_exists_coeff_abs_max_of_ne_zero
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    {f : K[X]} (hf : f ≠ 0) :
    ∃ m : ℝ, ∃ n : ℕ,
      0 < m ∧ n ≤ f.natDegree ∧ v (f.coeff n) = m ∧
        ∀ i : ℕ, v (f.coeff i) ≤ m := by
  classical
  let S : Finset ℕ := Finset.range (f.natDegree + 1)
  let T : Finset ℝ := S.image fun i => v (f.coeff i)
  have hdegmem : f.natDegree ∈ S := by
    simp [S]
  have hT : T.Nonempty := by
    exact ⟨v (f.coeff f.natDegree),
      Finset.mem_image.mpr ⟨f.natDegree, hdegmem, rfl⟩⟩
  let m : ℝ := T.max' hT
  have hlead_ne : f.leadingCoeff ≠ 0 :=
    (Polynomial.leadingCoeff_ne_zero).2 hf
  have hlead_pos : 0 < v f.leadingCoeff := by
    have hv_ne : v f.leadingCoeff ≠ 0 := by
      intro hzero
      exact hlead_ne ((v.eq_zero).1 hzero)
    exact lt_of_le_of_ne (v.nonneg f.leadingCoeff) hv_ne.symm
  have hlead_le_m : v f.leadingCoeff ≤ m := by
    have hmem : v (f.coeff f.natDegree) ∈ T :=
      Finset.mem_image.mpr ⟨f.natDegree, hdegmem, rfl⟩
    change v (f.coeff f.natDegree) ≤ m
    exact T.le_max' _ hmem
  have hmpos : 0 < m := hlead_pos.trans_le hlead_le_m
  have hmaxmem : m ∈ T := T.max'_mem hT
  rcases Finset.mem_image.mp hmaxmem with ⟨n, hnS, hnmax⟩
  have hnle : n ≤ f.natDegree := by
    exact Nat.lt_succ_iff.mp (by simpa [S] using hnS)
  refine ⟨m, n, hmpos, hnle, hnmax, ?_⟩
  intro i
  by_cases hi : i ≤ f.natDegree
  · have hiS : i ∈ S := by
      simp [S, Nat.lt_succ_of_le hi]
    have himem : v (f.coeff i) ∈ T :=
      Finset.mem_image.mpr ⟨i, hiS, rfl⟩
    exact T.le_max' _ himem
  · have hlt : f.natDegree < i := Nat.lt_of_not_ge hi
    have hzero : f.coeff i = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt hlt
    rw [hzero, map_zero]
    exact hmpos.le

/-- normalization source: dividing a nonzero polynomial by a
coefficient whose absolute value is the positive coefficient maximum preserves
degree, puts every coefficient in the closed unit ball, and makes that chosen
coefficient have value `1`. -/
theorem irreduciblePolynomial_scale_by_max_coeff_abs_data
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    {f : K[X]} {m : ℝ} {n : ℕ}
    (hmpos : 0 < m)
    (hnmax : v (f.coeff n) = m)
    (hbound : ∀ i : ℕ, v (f.coeff i) ≤ m) :
    let g : K[X] := Polynomial.C (f.coeff n)⁻¹ * f
    g.natDegree = f.natDegree ∧
      (∀ i : ℕ, v (g.coeff i) = m⁻¹ * v (f.coeff i)) ∧
        (∀ i : ℕ, v (g.coeff i) ≤ 1) ∧
          v (g.coeff n) = 1 := by
  let g : K[X] := Polynomial.C (f.coeff n)⁻¹ * f
  have hmne : m ≠ 0 := ne_of_gt hmpos
  have hn_ne : f.coeff n ≠ 0 := by
    intro hzero
    have h0m : (0 : ℝ) = m := by
      simpa [hzero] using hnmax
    exact hmne h0m.symm
  have hdegree : g.natDegree = f.natDegree := by
    dsimp [g]
    exact Polynomial.natDegree_C_mul (p := f) (a0 := inv_ne_zero hn_ne)
  have hcoeff_abs : ∀ i : ℕ, v (g.coeff i) = m⁻¹ * v (f.coeff i) := by
    intro i
    dsimp [g]
    calc
      v ((Polynomial.C (f.coeff n)⁻¹ * f).coeff i) =
          v ((f.coeff n)⁻¹ * f.coeff i) := by
            rw [Polynomial.coeff_C_mul]
      _ = v ((f.coeff n)⁻¹) * v (f.coeff i) := by
            rw [v.map_mul]
      _ = m⁻¹ * v (f.coeff i) := by
            rw [map_inv₀, hnmax]
  have hcoeff_le : ∀ i : ℕ, v (g.coeff i) ≤ 1 := by
    intro i
    rw [hcoeff_abs i]
    calc
      m⁻¹ * v (f.coeff i) ≤ m⁻¹ * m :=
        mul_le_mul_of_nonneg_left (hbound i) (inv_nonneg.mpr hmpos.le)
      _ = 1 := inv_mul_cancel₀ hmne
  have hn_one : v (g.coeff n) = 1 := by
    rw [hcoeff_abs n, hnmax, inv_mul_cancel₀ hmne]
  exact ⟨hdegree, hcoeff_abs, hcoeff_le, hn_one⟩

/-- normalization source: if the original constant and
leading coefficients are strictly smaller than the coefficient maximum, then
after scaling by a maximum coefficient they are strictly inside the open unit
ball. -/
theorem irreduciblePolynomial_normalized_scale_endpoint_abs_lt_one
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    {f g : K[X]} {m : ℝ}
    (hmpos : 0 < m)
    (hdegree : g.natDegree = f.natDegree)
    (hcoeff_abs : ∀ i : ℕ, v (g.coeff i) = m⁻¹ * v (f.coeff i))
    (hconst : v (f.coeff 0) < m)
    (hlead : v f.leadingCoeff < m) :
    v (g.coeff 0) < 1 ∧ v g.leadingCoeff < 1 := by
  have hmne : m ≠ 0 := ne_of_gt hmpos
  constructor
  · rw [hcoeff_abs 0]
    calc
      m⁻¹ * v (f.coeff 0) < m⁻¹ * m :=
        mul_lt_mul_of_pos_left hconst (inv_pos.mpr hmpos)
      _ = 1 := inv_mul_cancel₀ hmne
  · have hlead_abs :
        v g.leadingCoeff = m⁻¹ * v f.leadingCoeff := by
      rw [Polynomial.leadingCoeff, Polynomial.leadingCoeff, ← hdegree]
      exact hcoeff_abs g.natDegree
    rw [hlead_abs]
    calc
      m⁻¹ * v f.leadingCoeff < m⁻¹ * m :=
        mul_lt_mul_of_pos_left hlead (inv_pos.mpr hmpos)
      _ = 1 := inv_mul_cancel₀ hmne

/-- normalized Hensel input: after scaling by a coefficient
that attains the positive coefficient maximum, strict endpoint bounds below
that maximum give the exact Hensel reduction factor input for the scaled
polynomial. -/
theorem irreduciblePolynomial_normalized_scale_hensel_reduction_factor_input
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    {f : K[X]} {m : ℝ} {n : ℕ}
    (hmpos : 0 < m)
    (hnmax : v (f.coeff n) = m)
    (hbound : ∀ i : ℕ, v (f.coeff i) ≤ m)
    (hconst : v (f.coeff 0) < m)
    (hlead : v f.leadingCoeff < m) :
    let g : K[X] := Polynomial.C (f.coeff n)⁻¹ * f
    ∃ F : (absoluteValueValuationSubring v hnonarch)[X],
      ∃ r : ℕ,
        F.map (algebraMap
            (absoluteValueValuationSubring v hnonarch) K) =
          g ∧
        F.natDegree = g.natDegree ∧
          0 < r ∧ r < F.natDegree ∧
            F.map (IsLocalRing.residue
                (absoluteValueValuationSubring v hnonarch)) =
              Polynomial.X ^ r *
                (F.map (IsLocalRing.residue
                  (absoluteValueValuationSubring v hnonarch)) /ₘ
                    Polynomial.X ^ r) ∧
              (Polynomial.X ^ r :
                (IsLocalRing.ResidueField
                  (absoluteValueValuationSubring v hnonarch))[X]).natDegree =
                r ∧
                IsCoprime (Polynomial.X ^ r)
                  (F.map (IsLocalRing.residue
                    (absoluteValueValuationSubring v hnonarch)) /ₘ
                      Polynomial.X ^ r) ∧
                  ((F.map (IsLocalRing.residue
                    (absoluteValueValuationSubring v hnonarch)) /ₘ
                      Polynomial.X ^ r).coeff 0) ≠ 0 := by
  let g : K[X] := Polynomial.C (f.coeff n)⁻¹ * f
  rcases irreduciblePolynomial_scale_by_max_coeff_abs_data
      v hmpos hnmax hbound with
    ⟨hdegree, hcoeff_abs, hcoeff_le, hn_one⟩
  rcases irreduciblePolynomial_normalized_scale_endpoint_abs_lt_one
      v hmpos hdegree hcoeff_abs hconst hlead with
    ⟨hconstg, hleadg⟩
  exact
    irreduciblePolynomial_exists_hensel_reduction_factor_input_of_field_coeffs
      v hnonarch g hcoeff_le hconstg hleadg hn_one

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Henselian_IrreduciblePolynomialLifting
attribute [-instance] _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Hensel obstruction to irreducibility

This file applies the explicit Hensel lemma from the coefficientwise Hensel construction to the
normalized residue input constructed by the coefficient-bound lemmas.  The result here is the
core contradiction for irreducible-polynomial lifting: a nontrivial factorization of
the reduction gives a nontrivial factorization over the complete valuation
ring, hence the mapped field polynomial is not irreducible.
-/

noncomputable section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- algebraic obstruction: a field polynomial with a factor of
positive degree strictly smaller than its own degree is not irreducible. -/
theorem irreduciblePolynomial_not_irreducible_of_field_factor_natDegree_lt
    {K : Type*} [Field K] {f g h : K[X]}
    (hfactor : f = g * h)
    (hgpos : 0 < g.natDegree)
    (hglt : g.natDegree < f.natDegree) :
    ¬ Irreducible f := by
  intro hirr
  have hg_notunit : ¬ IsUnit g := by
    intro hgunit
    exact (Nat.ne_of_gt hgpos) (Polynomial.natDegree_eq_zero_of_isUnit hgunit)
  rcases hirr.isUnit_or_isUnit hfactor with hgunit | hhunit
  · exact hg_notunit hgunit
  · have hg_ne : g ≠ 0 := by
      intro hgzero
      simp [hgzero] at hgpos
    have hh_ne : h ≠ 0 := hhunit.ne_zero
    have hdeg : f.natDegree = g.natDegree := by
      simpa [hfactor, Polynomial.natDegree_eq_zero_of_isUnit hhunit] using
        (Polynomial.natDegree_mul hg_ne hh_ne)
    exact (Nat.ne_of_lt hglt) hdeg.symm

/-- transport obstruction: a nontrivial factorization over the
closed-unit-ball valuation ring maps to a nontrivial field factorization. -/
theorem irreduciblePolynomial_not_irreducible_of_valuation_factorization
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    {F G H : (absoluteValueValuationSubring v hnonarch)[X]}
    {f : K[X]} {r : ℕ}
    (hFmap : F.map (algebraMap
        (absoluteValueValuationSubring v hnonarch) K) = f)
    (hFdegree : F.natDegree = f.natDegree)
    (hfactor : F = G * H)
    (hGdegree : G.natDegree = r)
    (hrpos : 0 < r)
    (hrlt : r < F.natDegree) :
    ¬ Irreducible f := by
  let V := absoluteValueValuationSubring v hnonarch
  let φ : V →+* K := algebraMap V K
  have hφinj : Function.Injective φ := by
    intro x y hxy
    exact Subtype.ext (by simpa [φ] using hxy)
  let Gk : K[X] := G.map φ
  let Hk : K[X] := H.map φ
  have hfacK : f = Gk * Hk := by
    calc
      f = F.map φ := hFmap.symm
      _ = (G * H).map φ := by rw [hfactor]
      _ = G.map φ * H.map φ := by simp [Polynomial.map_mul]
      _ = Gk * Hk := rfl
  have hGkDegree : Gk.natDegree = r := by
    calc
      Gk.natDegree = G.natDegree := by
        simpa [Gk] using Polynomial.natDegree_map_eq_of_injective hφinj G
      _ = r := hGdegree
  have hGkpos : 0 < Gk.natDegree := by
    simpa [hGkDegree] using hrpos
  have hGklt : Gk.natDegree < f.natDegree := by
    simpa [hGkDegree, hFdegree] using hrlt
  exact irreduciblePolynomial_not_irreducible_of_field_factor_natDegree_lt
    hfacK hGkpos hGklt

/-- The common nonvanishing step in the three irreducible-polynomial lifting Hensel routes:
if a polynomial is `X ^ r` times a polynomial with nonzero constant
coefficient, then it is nonzero. -/
theorem irreduciblePolynomial_polynomial_ne_zero_of_eq_X_pow_mul_of_coeff_zero_ne_zero
    {k : Type*} [Field k] {P Q : k[X]} {r : ℕ}
    (hfactor : P = Polynomial.X ^ r * Q)
    (hQ0 : Q.coeff 0 ≠ 0) :
    P ≠ 0 := by
  have hQne : Q ≠ 0 := by
    intro hQzero
    exact hQ0 (by simp [hQzero])
  rw [hfactor]
  exact mul_ne_zero (pow_ne_zero r Polynomial.X_ne_zero) hQne

/-- scalar normalization preserves irreducibility: multiplying
by the inverse of a nonzero coefficient is multiplication by a unit. -/
theorem irreduciblePolynomial_irreducible_normalized_scale_of_irreducible
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    {f : K[X]} {m : ℝ} {n : ℕ}
    (hmpos : 0 < m)
    (hnmax : v (f.coeff n) = m)
    (hirr : Irreducible f) :
    Irreducible (Polynomial.C (f.coeff n)⁻¹ * f) := by
  have hmne : m ≠ 0 := ne_of_gt hmpos
  have hn_ne : f.coeff n ≠ 0 := by
    intro hzero
    have h0m : (0 : ℝ) = m := by
      simpa [hzero] using hnmax
    exact hmne h0m.symm
  have hunit :
      IsUnit (Polynomial.C (f.coeff n)⁻¹ : K[X]) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero hn_ne))
  exact (irreducible_isUnit_mul hunit).2 hirr

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Henselian_Core
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ValuationTheory

/-!
# Henselian discretely valued fields

The Henselian factorization condition and the residual linear-factor lemmas used in the
residual linear-factor criterion.
-/

noncomputable section

namespace DiscreteValuationField

universe u v

/-- The factorization form of Hensel's lemma used in the Henselian factorization condition.

Every primitive polynomial whose reduction is a product of coprime factors has
degree-controlled lifts with the prescribed reductions. -/
def HenselFactorizationProperty {K : Type u} [Field K]
    (V : ValuationSubring K) : Prop :=
  ∀ {f : Polynomial V}
      {gbar hbar : Polynomial (IsLocalRing.ResidueField V)},
    f.map (IsLocalRing.residue V) ≠ 0 →
      f.map (IsLocalRing.residue V) = gbar * hbar →
        IsCoprime gbar hbar →
          ∃ G H : Polynomial V,
            G.natDegree = gbar.natDegree ∧
              H.natDegree ≤ f.natDegree - gbar.natDegree ∧
                f = G * H ∧
                  G.map (IsLocalRing.residue V) = gbar ∧
                    H.map (IsLocalRing.residue V) = hbar

/-- The Henselian factorization condition: a valuation is Henselian when its valuation ring
satisfies Hensel's lemma in the factorization sense. -/
def HenselianValuationByFactorization {K : Type u} [Field K]
    {Γ : Type v} [LinearOrderedCommGroupWithZero Γ]
    (val : _root_.Valuation K Γ) : Prop :=
  HenselFactorizationProperty val.valuationSubring

end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_AbsoluteValue_AlgebraicExtension_NormFormulaCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# coefficient bound from primitive Hensel factorization

This file reuses the algebraic normalization and irreducibility obstruction
from the irreducible-polynomial coefficient bounds.  The factor lift is supplied directly by the
factorization form of Hensel's lemma in the primitive factorization definition, so no completeness or
separatedness hypothesis is needed.
-/

noncomputable section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- The normalized residual factor input from the irreducible-polynomial coefficient bounds contradicts
irreducibility as soon as the valuation ring satisfies the construction's
factorization form of Hensel's lemma. -/
theorem normFormula_hensel_reduction_factor_input_not_irreducible_of_henselFactorization
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
      (absoluteValueValuationSubring v hnonarch))
    (F : (absoluteValueValuationSubring v hnonarch)[X])
    {r : ℕ}
    (hrpos : 0 < r) (hrlt : r < F.natDegree)
    (hfactor :
      F.map (IsLocalRing.residue
          (absoluteValueValuationSubring v hnonarch)) =
        Polynomial.X ^ r *
          (F.map (IsLocalRing.residue
            (absoluteValueValuationSubring v hnonarch)) /ₘ
              Polynomial.X ^ r))
    (hnatDegree : (Polynomial.X ^ r :
        (IsLocalRing.ResidueField
          (absoluteValueValuationSubring v hnonarch))[X]).natDegree =
        r)
    (hcoprime : IsCoprime (Polynomial.X ^ r)
      (F.map (IsLocalRing.residue
        (absoluteValueValuationSubring v hnonarch)) /ₘ
          Polynomial.X ^ r))
    (hQ0 : ((F.map (IsLocalRing.residue
        (absoluteValueValuationSubring v hnonarch)) /ₘ
          Polynomial.X ^ r).coeff 0) ≠ 0)
    {f : K[X]}
    (hFmap : F.map (algebraMap
        (absoluteValueValuationSubring v hnonarch) K) = f)
    (hFdegree : F.natDegree = f.natDegree) :
    ¬ Irreducible f := by
  let V := absoluteValueValuationSubring v hnonarch
  let k := IsLocalRing.ResidueField V
  let fbar : k[X] := F.map (IsLocalRing.residue V)
  let qbar : k[X] := fbar /ₘ Polynomial.X ^ r
  have hprim : F.map (IsLocalRing.residue V) ≠ 0 := by
    exact
      irreduciblePolynomial_polynomial_ne_zero_of_eq_X_pow_mul_of_coeff_zero_ne_zero
        hfactor hQ0
  rcases hv hprim (by simpa [V, k, fbar, qbar] using hfactor) hcoprime with
    ⟨G, H, hGdegree_res, _hHle, hGH, _hGmap, _hHmap⟩
  have hGdegree : G.natDegree = r := hGdegree_res.trans hnatDegree
  exact irreduciblePolynomial_not_irreducible_of_valuation_factorization
    v hnonarch hFmap hFdegree hGH hGdegree hrpos hrlt

/-- Scaling by a coefficient of positive maximum value and applying the construction
Hensel factorization contradicts irreducibility when both endpoint values are
strictly below that maximum. -/
theorem normFormula_normalized_scale_not_irreducible_of_henselFactorization
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
      (absoluteValueValuationSubring v hnonarch))
    {f : K[X]} {m : ℝ} {n : ℕ}
    (hmpos : 0 < m)
    (hnmax : v (f.coeff n) = m)
    (hbound : ∀ i : ℕ, v (f.coeff i) ≤ m)
    (hconst : v (f.coeff 0) < m)
    (hlead : v f.leadingCoeff < m) :
    let g : K[X] := Polynomial.C (f.coeff n)⁻¹ * f
    ¬ Irreducible g := by
  let g : K[X] := Polynomial.C (f.coeff n)⁻¹ * f
  rcases irreduciblePolynomial_normalized_scale_hensel_reduction_factor_input
      v hnonarch hmpos hnmax hbound hconst hlead with
    ⟨F, r, hFmap, hFdegree, hrpos, hrlt, hfactor, hnatDegree, hcoprime, hQ0⟩
  exact
    normFormula_hensel_reduction_factor_input_not_irreducible_of_henselFactorization
      v hnonarch hv F hrpos hrlt hfactor hnatDegree hcoprime hQ0
      hFmap hFdegree

/-- Under primitive Hensel factorization, a positive coefficient maximum of an
irreducible polynomial is bounded by the larger endpoint value. -/
theorem normFormula_coeff_max_le_endpoint_max_of_irreducible_of_henselFactorization
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
      (absoluteValueValuationSubring v hnonarch))
    {f : K[X]} {m : ℝ} {n : ℕ}
    (hirr : Irreducible f)
    (hmpos : 0 < m)
    (hnmax : v (f.coeff n) = m)
    (hbound : ∀ i : ℕ, v (f.coeff i) ≤ m) :
    m ≤ max (v (f.coeff 0)) (v f.leadingCoeff) := by
  by_contra hnot
  have hmaxlt : max (v (f.coeff 0)) (v f.leadingCoeff) < m :=
    lt_of_not_ge hnot
  have hconst : v (f.coeff 0) < m :=
    (le_max_left (v (f.coeff 0)) (v f.leadingCoeff)).trans_lt hmaxlt
  have hlead : v f.leadingCoeff < m :=
    (le_max_right (v (f.coeff 0)) (v f.leadingCoeff)).trans_lt hmaxlt
  have hscaled_irreducible :
      Irreducible (Polynomial.C (f.coeff n)⁻¹ * f) :=
    irreduciblePolynomial_irreducible_normalized_scale_of_irreducible
      v hmpos hnmax hirr
  have hscaled_not_irreducible :
      ¬ Irreducible (Polynomial.C (f.coeff n)⁻¹ * f) :=
    normFormula_normalized_scale_not_irreducible_of_henselFactorization
      v hnonarch hv hmpos hnmax hbound hconst hlead
  exact hscaled_not_irreducible hscaled_irreducible

/-- the finite norm-formula theorem coefficient source: primitive Hensel factorization alone bounds
every coefficient of an irreducible polynomial by its two endpoint values. -/
theorem normFormula_coeff_abs_le_endpoint_max_of_irreducible_of_henselFactorization
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
      (absoluteValueValuationSubring v hnonarch))
    {f : K[X]} (hirr : Irreducible f) :
    ∀ i : ℕ, v (f.coeff i) ≤ max (v (f.coeff 0)) (v f.leadingCoeff) := by
  rcases irreduciblePolynomial_exists_coeff_abs_max_of_ne_zero v hirr.ne_zero with
    ⟨m, n, hmpos, _hnle, hnmax, hbound⟩
  have hmle : m ≤ max (v (f.coeff 0)) (v f.leadingCoeff) :=
    normFormula_coeff_max_le_endpoint_max_of_irreducible_of_henselFactorization
      v hnonarch hv hirr hmpos hnmax hbound
  intro i
  exact (hbound i).trans hmle

/-- the finite norm-formula theorem monic specialization: if the constant coefficient of an
irreducible monic polynomial lies in the closed unit ball, then every
coefficient lies there. -/
theorem normFormula_monic_coeff_abs_le_one_of_const_abs_le_one_of_henselFactorization
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
      (absoluteValueValuationSubring v hnonarch))
    {f : K[X]} (hirr : Irreducible f)
    (hmonic : f.Monic)
    (hconst : v (f.coeff 0) ≤ 1) :
    ∀ i : ℕ, v (f.coeff i) ≤ 1 := by
  have hlead : v f.leadingCoeff = 1 := by
    rw [hmonic.leadingCoeff]
    simp
  have hendpoint :
      max (v (f.coeff 0)) (v f.leadingCoeff) ≤ 1 := by
    rw [hlead]
    exact max_le hconst le_rfl
  intro i
  exact
    (normFormula_coeff_abs_le_endpoint_max_of_irreducible_of_henselFactorization
      v hnonarch hv hirr i).trans hendpoint

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_AbsoluteValue_AlgebraicExtension_NormFormulaIntegralClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# the actual integral closure is a valuation ring

The factorization form of Hensel's lemma forces the endpoint coefficient
estimate for every irreducible polynomial.  Applied to the norm-formula value,
this says that every algebraic element or its inverse is integral over the
base valuation ring.  Thus the actual integral closure, rather than an
assumed target ring, satisfies the valuation-ring dichotomy.
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

open scoped Polynomial

/-- A closed unit for the finite norm-formula value is integral over the base
valuation ring, using only the primitive factorization definition's primitive factorization property. -/
theorem normFormula_finiteExtensionNormFormulaValue_isIntegral_of_le_one_of_henselFactorization
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
      (absoluteValueValuationSubring v hnonarch))
    {x : L} (hx : finiteExtensionNormFormulaValue v x ≤ 1) :
    IsIntegral
      (absoluteValueValuationSubring v hnonarch) x := by
  let V := absoluteValueValuationSubring v hnonarch
  let : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  let : Algebra.IsIntegral K L := Algebra.IsAlgebraic.isIntegral
  have hxint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hconst : v ((minpoly K x).coeff 0) ≤ 1 :=
    (normFormula_finiteExtensionNormFormulaValue_le_one_iff_minpoly_coeff_zero_le_one
      v x).1 hx
  have hcoeff : ∀ i : ℕ, v ((minpoly K x).coeff i) ≤ 1 :=
    normFormula_monic_coeff_abs_le_one_of_const_abs_le_one_of_henselFactorization
      v hnonarch hv (minpoly.irreducible hxint) (minpoly.monic hxint) hconst
  rcases
      exists_polynomial_over_absoluteValueUnitBallSubringAsValuationSubring_of_coeff_abs_le_one
        v hnonarch (minpoly K x) hcoeff with
    ⟨F, hFmap, hFdegree, _hcoeff⟩
  have hφinj : Function.Injective (algebraMap V K) := by
    intro a b hab
    exact Subtype.ext hab
  have hFmonic : F.Monic := by
    apply Polynomial.monic_of_injective hφinj
    rw [hFmap]
    exact minpoly.monic hxint
  have hFdegree_ne : F.natDegree ≠ 0 := by
    rw [hFdegree]
    exact Nat.ne_of_gt (minpoly.natDegree_pos hxint)
  have hroot : (Polynomial.aeval x) F = 0 := by
    have hmaproot :
        (Polynomial.aeval x) (F.map (algebraMap V K)) = 0 := by
      rw [hFmap]
      exact minpoly.aeval K x
    rwa [Polynomial.aeval_map_algebraMap K x F] at hmaproot
  exact IsIntegral.of_aeval_monic hFmonic hFdegree_ne (by
    rw [hroot]
    exact isIntegral_zero)

/-- In a finite extension, every element or its inverse belongs to the actual
integral closure of the base valuation ring. -/
theorem normFormula_finite_integralClosure_mem_or_inv_of_henselFactorization
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
      (absoluteValueValuationSubring v hnonarch))
    (x : L) :
    x ∈ (integralClosure
        (absoluteValueValuationSubring v hnonarch) L).toSubring ∨
      x⁻¹ ∈ (integralClosure
        (absoluteValueValuationSubring v hnonarch) L).toSubring := by
  by_cases hx : finiteExtensionNormFormulaValue v x ≤ 1
  · left
    exact
      normFormula_finiteExtensionNormFormulaValue_isIntegral_of_le_one_of_henselFactorization
        v hnonarch hv hx
  · right
    have hx_gt : 1 < finiteExtensionNormFormulaValue v x :=
      lt_of_not_ge hx
    have hx_pos : 0 < finiteExtensionNormFormulaValue v x :=
      zero_lt_one.trans hx_gt
    have hinv : finiteExtensionNormFormulaValue v x⁻¹ ≤ 1 := by
      rw [normFormula_finiteExtensionNormFormulaValue_inv]
      exact (inv_le_one₀ hx_pos).2 hx_gt.le
    exact
      normFormula_finiteExtensionNormFormulaValue_isIntegral_of_le_one_of_henselFactorization
        v hnonarch hv hinv

/-- the finite norm-formula theorem, source-producing algebraic endpoint: for an arbitrary
algebraic extension, the actual integral closure of the Henselian valuation
ring satisfies the valuation-ring dichotomy.  Each element is handled inside
the finite simple subextension that it generates. -/
theorem normFormula_algebraic_integralClosure_mem_or_inv_of_henselFactorization
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
      (absoluteValueValuationSubring v hnonarch))
    (x : L) :
    x ∈ (integralClosure
        (absoluteValueValuationSubring v hnonarch) L).toSubring ∨
      x⁻¹ ∈ (integralClosure
        (absoluteValueValuationSubring v hnonarch) L).toSubring := by
  let V := absoluteValueValuationSubring v hnonarch
  let E := IntermediateField.adjoin K ({x} : Set L)
  let xE : E :=
    ⟨x, IntermediateField.subset_adjoin K ({x} : Set L)
      (Set.mem_singleton x)⟩
  have hxint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  let : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional hxint
  have hfinite :=
    normFormula_finite_integralClosure_mem_or_inv_of_henselFactorization
      (K := K) (L := E) v hnonarch hv xE
  rcases hfinite with hxE | hxEinv
  · left
    have hxEint : IsIntegral V xE := hxE
    have hmap := hxEint.map
      ((IntermediateField.val E).restrictScalars V)
    have hxintV : IsIntegral V x := by
      simpa [E, xE] using hmap
    exact (mem_integralClosure_iff (R := V) (A := L)).2 hxintV
  · right
    have hxEinvint : IsIntegral V xE⁻¹ := hxEinv
    have hmap := hxEinvint.map
      ((IntermediateField.val E).restrictScalars V)
    have hxinvintV : IsIntegral V x⁻¹ := by
      simpa [E, xE] using hmap
    exact (mem_integralClosure_iff (R := V) (A := L)).2 hxinvintV

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_AbsoluteValue_AlgebraicExtension_UniqueValuationSubring
attribute [-instance] _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing
attribute [-simp] _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# uniqueness from the integral-closure valuation ring

Once the actual integral closure of a valuation subring satisfies the
valuative dichotomy, it is contained in every extension valuation ring.  Its
integrality over the base then forces the center of every such overring to be
the unique maximal ideal, so the overring is the integral closure itself.
-/

noncomputable section

universe u v w

namespace DiscreteValuationField

open ValuationTheory.DiscreteValuationField.Valuation

namespace Valuation

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-- the finite norm-formula theorem, uniqueness source after the actual integral closure has been
shown to be a valuation ring.

No finiteness, separability, discreteness, or completeness assumption is used:
every valuation of `L` extending the canonical valuation of `V` has valuation
subring equal to the valuation subring built from the actual integral closure
of `V` in `L`. -/
theorem normFormula_extension_valuationSubring_eq_integralClosure_of_mem_or_inv
    (V : ValuationSubring K)
    (hval :
      ∀ z : L,
        z ∈
            (integralClosure V.valuation.valuationSubring L).toSubring ∨
          z⁻¹ ∈
            (integralClosure V.valuation.valuationSubring L).toSubring)
    {Γ : Type w} [LinearOrderedCommGroupWithZero Γ]
    (wL : _root_.Valuation L Γ) [V.valuation.HasExtension wL] :
    wL.valuationSubring =
      integralClosureValuationSubringOfMemOrInv
        (L := L) V.valuation hval := by
  let B : ValuationSubring L :=
    integralClosureValuationSubringOfMemOrInv
      (L := L) V.valuation hval
  change wL.valuationSubring = B
  let : V.valuation.HasExtension B.valuation :=
    integralClosureValuationSubringOfMemOrInv_hasExtension
      (L := L) V.valuation hval
  have hBW : B ≤ wL.valuationSubring :=
    integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
      (L := L) V.valuation wL hval
  let i : V.valuation.valuationSubring →+* B :=
    { toFun := fun a =>
        ⟨algebraMap K L (a : K),
          (integralClosureValuationSubringOfMemOrInv_pullback
            (L := L) V.valuation hval (a : K)).2 a.2⟩
      map_zero' := by ext; simp
      map_one' := by ext; simp
      map_add' := by intro a b; ext; simp
      map_mul' := by intro a b; ext; simp }
  let : Algebra V.valuation.valuationSubring B := i.toAlgebra
  let : IsScalarTower V.valuation.valuationSubring B L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let P : Ideal B :=
    ValuationSubring.idealOfLE B wL.valuationSubring hBW
  have hPcomap :
      P.comap i =
        IsLocalRing.maximalIdeal V.valuation.valuationSubring := by
    apply Ideal.ext
    intro a
    rw [Ideal.mem_comap]
    change
      B.inclusion wL.valuationSubring hBW (i a) ∈
          IsLocalRing.maximalIdeal wL.valuationSubring ↔
        a ∈ IsLocalRing.maximalIdeal V.valuation.valuationSubring
    rw [Valuation.mem_maximalIdeal_iff (v := wL)]
    rw [Valuation.mem_maximalIdeal_iff (v := V.valuation)]
    have hcoe :
        ((B.inclusion wL.valuationSubring hBW (i a) :
          wL.valuationSubring) : L) = algebraMap K L (a : K) := by
      rfl
    rw [hcoe]
    exact
      _root_.Valuation.HasExtension.val_map_lt_one_iff
        V.valuation wL (a : K)
  have hBClosure :
      IsIntegralClosure B V.valuation.valuationSubring L := by
    simpa [B] using
      (integralClosureValuationSubringOfMemOrInv_isIntegralClosure
        (L := L) V.valuation hval)
  let : IsIntegralClosure B V.valuation.valuationSubring L := hBClosure
  have hBIntegral :
      Algebra.IsIntegral V.valuation.valuationSubring B :=
    IsIntegralClosure.isIntegral_algebra V.valuation.valuationSubring L
  let : Algebra.IsIntegral V.valuation.valuationSubring B := hBIntegral
  have hPmax : P.IsMaximal := by
    have hcomapMax :
        (P.comap (algebraMap V.valuation.valuationSubring B)).IsMaximal := by
      change (P.comap i).IsMaximal
      rw [hPcomap]
      exact
        IsLocalRing.maximalIdeal.isMaximal
          V.valuation.valuationSubring
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' i
      (fun x => Algebra.IsIntegral.isIntegral x) P hcomapMax
  have hP :
      ValuationSubring.idealOfLE B wL.valuationSubring hBW =
        IsLocalRing.maximalIdeal B :=
    IsLocalRing.eq_maximalIdeal hPmax
  exact
    valuationSubring_eq_of_le_of_idealOfLE_eq_maximalIdeal
      B wL.valuationSubring hBW hP

end Valuation
end DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_AbsoluteValue_AlgebraicExtension_NormFormulaExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# algebraic extension and integral closure

This file packages the explicit algebraic-extension statement.  A
valuation is represented by its valuation subring, so uniqueness is literal
equality of valuation subrings (equivalently, equivalence of valuations).
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

/-- the primitive factorization definition for the valuation subring attached to a nonarchimedean
absolute value, reduced to the exact factorization property used below. -/
theorem henselianValuation_iff_henselFactorization
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v) :
    ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
        (absoluteValueValuationSubring
          v hnonarch).valuation ↔
      ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
        (absoluteValueValuationSubring v hnonarch) := by
  simp only [ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization,
    ValuationSubring.valuationSubring_valuation]

/-- the finite norm-formula theorem: a Henselian nonarchimedean valuation has exactly one
extension to every algebraic extension, and the valuation ring of that
extension is the actual integral closure of the base valuation ring.

The extension is expressed by its valuation subring.  The first conjunct says
that its canonical valuation extends the base valuation; the second is the
integral-closure identification. -/
theorem normFormula_algebraic_extension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (absoluteValueValuationSubring
        v hnonarch).valuation) :
    let V := absoluteValueValuationSubring v hnonarch
    ∃! W : ValuationSubring L,
      V.valuation.HasExtension W.valuation ∧
        W.toSubring = (integralClosure V L).toSubring := by
  let V := absoluteValueValuationSubring v hnonarch
  have hv : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty V :=
    (henselianValuation_iff_henselFactorization v hnonarch).1 hhens
  have hvalV :
      ∀ z : L,
        z ∈ (integralClosure V L).toSubring ∨
          z⁻¹ ∈ (integralClosure V L).toSubring :=
    normFormula_algebraic_integralClosure_mem_or_inv_of_henselFactorization
      v hnonarch hv
  have hval :
      ∀ z : L,
        z ∈ (integralClosure V.valuation.valuationSubring L).toSubring ∨
          z⁻¹ ∈
            (integralClosure V.valuation.valuationSubring L).toSubring := by
    rw [ValuationSubring.valuationSubring_valuation]
    exact hvalV
  let B : ValuationSubring L :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
      (L := L) V.valuation hval
  have hBext : V.valuation.HasExtension B.valuation :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_hasExtension
      (L := L) V.valuation hval
  have hBclosure : B.toSubring = (integralClosure V L).toSubring := by
    change
      (integralClosure V.valuation.valuationSubring L).toSubring =
        (integralClosure V L).toSubring
    rw [ValuationSubring.valuationSubring_valuation]
  refine ⟨B, ⟨hBext, hBclosure⟩, ?_⟩
  intro W hW
  let : V.valuation.HasExtension W.valuation := hW.1
  simpa only [ValuationSubring.valuationSubring_valuation] using
    DiscreteValuationField.Valuation.normFormula_extension_valuationSubring_eq_integralClosure_of_mem_or_inv
      (K := K) (L := L) V hval W.valuation

/-- Exact extension of nonarchimedean absolute values supplies extension of
the canonical valuations of their closed unit balls. -/
theorem absoluteValueValuation_hasExtension_of_extends
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ)
    (hv : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hw : LubinTate.Valuations.NonarchimedeanAbsoluteValue w)
    (hext : ∀ a : K, w (algebraMap K L a) = v a) :
    let V := absoluteValueValuationSubring v hv
    let W := absoluteValueValuationSubring w hw
    V.valuation.HasExtension W.valuation := by
  let V := absoluteValueValuationSubring v hv
  let W := absoluteValueValuationSubring w hw
  apply _root_.Valuation.HasExtension.ofComapInteger
  rw [ValuationSubring.integer_valuation, ValuationSubring.integer_valuation]
  have hcomap :=
    comap_absoluteValueUnitBallSubring_eq_of_extends
      v w hv hw hext
  ext x
  change algebraMap K L x ∈ absoluteValueUnitBallSubring w hw ↔
    x ∈ absoluteValueUnitBallSubring v hv
  constructor
  · intro hx
    have hx' : x ∈ Subring.comap (algebraMap K L)
        (absoluteValueUnitBallSubring w hw) := hx
    rw [hcomap] at hx'
    exact hx'
  · intro hx
    have hx' : x ∈ Subring.comap (algebraMap K L)
        (absoluteValueUnitBallSubring w hw) := by
      rw [hcomap]
      exact hx
    exact hx'

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Henselian_UniqueAlgebraicExtensions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# unique extension criterion

Valuations are regarded valuations up to equivalence.  Accordingly, uniqueness on
an algebraic extension is stated as literal uniqueness of its valuation
subring.  This is the same endpoint used in the finite norm-formula theorem.
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

universe u

/-- A valuation subring has a unique extension valuation ring to `L`. -/
def HasUniqueValuationSubringExtension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (V : ValuationSubring K) : Prop :=
  ∃! W : ValuationSubring L, V.valuation.HasExtension W.valuation

/-- the unique-extension criterion, forward direction.  the primitive factorization definition, in its exact
factorization form, gives a unique extension valuation ring on every
algebraic extension. -/
theorem henselianUniqueExtension_unique_algebraic_valuationSubring_extension_of_henselian
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (absoluteValueValuationSubring
        v hnonarch).valuation) :
    HasUniqueValuationSubringExtension
      (L := L) (absoluteValueValuationSubring v hnonarch) := by
  let V := absoluteValueValuationSubring v hnonarch
  obtain ⟨B, hB, hBuniq⟩ :=
    normFormula_algebraic_extension (K := K) (L := L)
      v hnonarch hhens
  refine ⟨B, hB.1, ?_⟩
  intro W hW
  apply hBuniq W
  refine ⟨hW, ?_⟩
  have hv : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty V :=
    (henselianValuation_iff_henselFactorization v hnonarch).1 hhens
  have hvalV :
      ∀ z : L,
        z ∈ (integralClosure V L).toSubring ∨
          z⁻¹ ∈ (integralClosure V L).toSubring :=
    normFormula_algebraic_integralClosure_mem_or_inv_of_henselFactorization
      v hnonarch hv
  have hval :
      ∀ z : L,
        z ∈ (integralClosure V.valuation.valuationSubring L).toSubring ∨
          z⁻¹ ∈
            (integralClosure V.valuation.valuationSubring L).toSubring := by
    rw [ValuationSubring.valuationSubring_valuation]
    exact hvalV
  let : V.valuation.HasExtension W.valuation := hW
  have hWic :
      W =
        ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
          (L := L) V.valuation hval := by
    simpa only [ValuationSubring.valuationSubring_valuation] using
      DiscreteValuationField.Valuation.normFormula_extension_valuationSubring_eq_integralClosure_of_mem_or_inv
        (K := K) (L := L) V hval W.valuation
  change W.toSubring = (integralClosure V L).toSubring
  rw [hWic]
  ext z
  change z ∈
      ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
        (L := L) V.valuation hval ↔ z ∈ (integralClosure V L).toSubring
  rw [ValuationTheory.DiscreteValuationField.Valuation.mem_integralClosureValuationSubringOfMemOrInv
      V.valuation hval z]
  rw [ValuationSubring.valuationSubring_valuation]

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_AbsoluteValue_AlgebraicExtension_RamificationInvariants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# the fundamental inequality and identity

The first part follows the proof on pp. 149--150: residue-basis lifts are
multiplied by representatives of distinct value-group cosets, and the
resulting family is linearly independent over the base field.  The second
part uses the actual valuation rings.  For a discrete Henselian base and a
finite separable extension, the finite norm-formula theorem identifies the target valuation ring
with the integral closure, so the local Dedekind ramification identity applies
without completeness.
-/

noncomputable section

open scoped BigOperators

namespace AlgebraicNumberTheory
namespace Valuations

open Module

def ramificationAddValuation {K : Type*} [Field K]
    (v : LubinTate.Valuations.ExponentialValuation K) : AddValuation K (WithTop ℝ) :=
  AddValuation.of v
    ((v.eq_top_iff 0).mpr rfl)
    (LubinTate.Valuations.exponentialValuation_one v)
    v.add_le_min v.map_mul

@[simp]
theorem ramificationAddValuation_apply {K : Type*} [Field K]
    (v : LubinTate.Valuations.ExponentialValuation K) (x : K) :
    ramificationAddValuation v x = v x :=
  rfl

/-- The map of valuation rings induced by an exact extension of exponential
exponential valuations. -/
def exponentialValuationRingMap
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a) :
    LubinTate.Valuations.exponentialValuationSubring v →+*
      LubinTate.Valuations.exponentialValuationSubring w :=
  (algebraMap K L).restrict _ _ fun a ha ↦ by
    change (0 : WithTop ℝ) ≤ w (algebraMap K L a)
    rw [hExt]
    exact ha

@[simp]
theorem exponentialValuationRingMap_apply
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (a : LubinTate.Valuations.exponentialValuationSubring v) :
    ((exponentialValuationRingMap v w hExt a :
      LubinTate.Valuations.exponentialValuationSubring w) : L) =
        algebraMap K L (a : K) :=
  rfl

/-- The canonical multiplicative presentation `exp (-v(x))` of an exponential
exponential valuation. -/
noncomputable def exponentialAssociatedAbsoluteValue
    {K : Type*} [Field K] (v : LubinTate.Valuations.ExponentialValuation K) :
    AbsoluteValue K ℝ := by
  classical
  refine
    { toFun := fun x ↦ if x = 0 then 0 else Real.exp (-(v x).untop₀)
      map_mul' := ?_
      nonneg' := ?_
      eq_zero' := ?_
      add_le' := ?_ }
  · intro x y
    by_cases hx : x = 0
    · subst x
      simp
    by_cases hy : y = 0
    · subst y
      simp
    have hxy : x * y ≠ 0 := mul_ne_zero hx hy
    have hreal : (v (x * y)).untop₀ =
        (v x).untop₀ + (v y).untop₀ := by
      apply WithTop.coe_eq_coe.mp
      rw [WithTop.coe_add,
        WithTop.coe_untop₀_of_ne_top
          (LubinTate.Valuations.exponentialValuation_ne_top_of_ne_zero v hxy),
        WithTop.coe_untop₀_of_ne_top
          (LubinTate.Valuations.exponentialValuation_ne_top_of_ne_zero v hx),
        WithTop.coe_untop₀_of_ne_top
          (LubinTate.Valuations.exponentialValuation_ne_top_of_ne_zero v hy)]
      exact v.map_mul x y
    simp only [hx, hy, hxy, ite_false, if_false]
    rw [hreal, neg_add, Real.exp_add]
  · intro x
    by_cases hx : x = 0
    · simp [hx]
    · simp [hx, Real.exp_nonneg]
  · intro x
    by_cases hx : x = 0
    · simp [hx]
    · simp [hx, Real.exp_ne_zero]
  · intro x y
    by_cases hx : x = 0
    · subst x
      simp
    by_cases hy : y = 0
    · subst y
      simp
    by_cases hxy : x + y = 0
    · simp only [hx, hy, hxy, ite_false, if_false, ite_true, if_true]
      positivity
    let r := (v x).untop₀
    let s := (v y).untop₀
    let t := (v (x + y)).untop₀
    have hvr : v x = (r : WithTop ℝ) :=
      (WithTop.coe_untop₀_of_ne_top
        (LubinTate.Valuations.exponentialValuation_ne_top_of_ne_zero v hx)).symm
    have hvs : v y = (s : WithTop ℝ) :=
      (WithTop.coe_untop₀_of_ne_top
        (LubinTate.Valuations.exponentialValuation_ne_top_of_ne_zero v hy)).symm
    have hvt : v (x + y) = (t : WithTop ℝ) :=
      (WithTop.coe_untop₀_of_ne_top
        (LubinTate.Valuations.exponentialValuation_ne_top_of_ne_zero v hxy)).symm
    have hmin : min r s ≤ t := by
      have h := v.add_le_min x y
      rw [hvr, hvs, hvt] at h
      exact WithTop.coe_le_coe.mp (by simpa only [WithTop.coe_min] using h)
    have hmain : Real.exp (-t) ≤ Real.exp (-r) + Real.exp (-s) := by
      refine (Real.exp_le_exp.mpr (neg_le_neg hmin)).trans ?_
      by_cases hrs : r ≤ s
      · rw [min_eq_left hrs]
        exact le_add_of_nonneg_right (Real.exp_nonneg _)
      · rw [min_eq_right (le_of_not_ge hrs)]
        exact le_add_of_nonneg_left (Real.exp_nonneg _)
    simpa only [hx, hy, hxy, ite_false, if_false, r, s, t] using hmain

/-- The canonical multiplicative presentation is associated to `v`, with
the fixed base `e = exp 1`. -/
theorem exponentialAssociatedAbsoluteValue_associated
    {K : Type*} [Field K] (v : LubinTate.Valuations.ExponentialValuation K) :
    LubinTate.Valuations.AssociatedAbsoluteValue v (Real.exp 1)
      (exponentialAssociatedAbsoluteValue v) := by
  refine ⟨Real.one_lt_exp_iff.mpr zero_lt_one, ?_⟩
  intro x hx
  refine ⟨(v x).untop₀, ?_, ?_⟩
  · exact (WithTop.coe_untop₀_of_ne_top
      (LubinTate.Valuations.exponentialValuation_ne_top_of_ne_zero v hx)).symm
  · simp [exponentialAssociatedAbsoluteValue, hx, Real.exp_one_rpow]

/-- An absolute value associated to a exponential valuation is
nonarchimedean; the strong triangle inequality is the exponential
ultrametric inequality transported through the decreasing map
`r ↦ q ^ (-r)`. -/
theorem associatedAbsoluteValue_nonarchimedean
    {K : Type*} [Field K]
    (v : LubinTate.Valuations.ExponentialValuation K) (q : ℝ)
    (abv : AbsoluteValue K ℝ)
    (hassoc : LubinTate.Valuations.AssociatedAbsoluteValue v q abv) :
    LubinTate.Valuations.NonarchimedeanAbsoluteValue abv := by
  apply LubinTate.Valuations.nonarchimedean_of_strong_triangle
  intro x y
  by_cases hx : x = 0
  · subst x
    simp
  by_cases hy : y = 0
  · subst y
    simp
  by_cases hxy : x + y = 0
  · simp [hxy]
  obtain ⟨r, hvr, habvr⟩ := hassoc.2 x hx
  obtain ⟨s, hvs, habvs⟩ := hassoc.2 y hy
  obtain ⟨t, hvt, habvt⟩ := hassoc.2 (x + y) hxy
  have hmin : min r s ≤ t := by
    have h := v.add_le_min x y
    rw [hvr, hvs, hvt] at h
    exact WithTop.coe_le_coe.mp (by simpa only [WithTop.coe_min] using h)
  rw [habvr, habvs, habvt]
  have hpow : q ^ (-t) ≤ q ^ (-(min r s)) :=
    Real.rpow_le_rpow_of_exponent_le (le_of_lt hassoc.1)
      (neg_le_neg hmin)
  refine hpow.trans ?_
  by_cases hrs : r ≤ s
  · rw [min_eq_left hrs]
    exact le_max_left _ _
  · have hsr : s ≤ r := le_of_not_ge hrs
    rw [min_eq_right hsr]
    exact le_max_right _ _

/-- Associated additive and multiplicative presentations have the same
valuation subring. -/
theorem associatedAbsoluteValue_valuationSubring_eq
    {K : Type*} [Field K]
    (v : LubinTate.Valuations.ExponentialValuation K) (q : ℝ)
    (abv : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue abv)
    (hassoc : LubinTate.Valuations.AssociatedAbsoluteValue v q abv) :
    LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v =
      absoluteValueValuationSubring abv hnonarch := by
  ext x
  rw [LubinTate.Valuations.mem_exponentialValuationSubringAsValuationSubring_iff,
    mem_absoluteValueValuationSubring_iff]
  by_cases hx : x = 0
  · subst x
    simp [(v.eq_top_iff 0).mpr rfl]
  · exact (LubinTate.Valuations.associatedAbsoluteValue_le_one_iff hassoc hx).symm

/-- Exact extension of associated exponential valuations gives exact
extension of the associated absolute values. -/
theorem associatedAbsoluteValue_extends
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (q : ℝ) (av : AbsoluteValue K ℝ) (aw : AbsoluteValue L ℝ)
    (hav : LubinTate.Valuations.AssociatedAbsoluteValue v q av)
    (haw : LubinTate.Valuations.AssociatedAbsoluteValue w q aw) :
    ∀ a : K, aw (algebraMap K L a) = av a := by
  intro a
  by_cases ha : a = 0
  · subst a
    simp
  · have hma : algebraMap K L a ≠ 0 :=
      (map_ne_zero (algebraMap K L)).mpr ha
    obtain ⟨r, hvr, havr⟩ := hav.2 a ha
    obtain ⟨s, hws, haws⟩ := haw.2 (algebraMap K L a) hma
    have hrs : r = s := by
      rw [hExt, hvr] at hws
      exact WithTop.coe_eq_coe.mp hws
    rw [havr, haws, hrs]

/-- the finite norm-formula theorem applied directly to the exponential presentation: a chosen
extension of a Henselian valuation has valuation ring equal to the actual
integral closure. The required multiplicative presentations are constructed
internally. -/
theorem exponentialValuationSubring_eq_integralClosure_of_henselian
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation) :
    (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring w).toSubring =
      (integralClosure
        (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v) L).toSubring := by
  let av := exponentialAssociatedAbsoluteValue v
  let aw := exponentialAssociatedAbsoluteValue w
  have hav : LubinTate.Valuations.AssociatedAbsoluteValue v (Real.exp 1) av :=
    exponentialAssociatedAbsoluteValue_associated v
  have haw : LubinTate.Valuations.AssociatedAbsoluteValue w (Real.exp 1) aw :=
    exponentialAssociatedAbsoluteValue_associated w
  have havNonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue av :=
    associatedAbsoluteValue_nonarchimedean v (Real.exp 1) av hav
  have hawNonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue aw :=
    associatedAbsoluteValue_nonarchimedean w (Real.exp 1) aw haw
  let Vv := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v
  let Wv := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring w
  let Va := absoluteValueValuationSubring av havNonarch
  let Wa := absoluteValueValuationSubring aw hawNonarch
  have hV : Vv = Va :=
    associatedAbsoluteValue_valuationSubring_eq
      v (Real.exp 1) av havNonarch hav
  have hW : Wv = Wa :=
    associatedAbsoluteValue_valuationSubring_eq
      w (Real.exp 1) aw hawNonarch haw
  have hhensA : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization Va.valuation := by
    rw [← hV]
    exact hhens
  have habsExt : ∀ a : K, aw (algebraMap K L a) = av a :=
    associatedAbsoluteValue_extends
      v w hExt (Real.exp 1) av aw hav haw
  have hWaExt : Va.valuation.HasExtension Wa.valuation :=
    absoluteValueValuation_hasExtension_of_extends
      av aw havNonarch hawNonarch habsExt
  let : Va.valuation.HasExtension Wa.valuation := hWaExt
  obtain ⟨B, hB, _hBuniq⟩ :=
    normFormula_algebraic_extension (K := K) (L := L)
      av havNonarch hhensA
  obtain ⟨C, hC, hCuniq⟩ :=
    henselianUniqueExtension_unique_algebraic_valuationSubring_extension_of_henselian
      (K := K) (L := L) av havNonarch hhensA
  have hWaC : Wa = C := hCuniq Wa hWaExt
  have hBC : B = C := hCuniq B hB.1
  have hWaB : Wa = B := hWaC.trans hBC.symm
  calc
    Wv.toSubring = Wa.toSubring := congrArg ValuationSubring.toSubring hW
    _ = B.toSubring := congrArg ValuationSubring.toSubring hWaB
    _ = (integralClosure Va L).toSubring := hB.2
    _ = (integralClosure Vv L).toSubring := by rw [hV]

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Unramified_Definitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite and algebraic unramified valued extensions

Finite unramified valued extensions are expressed directly by the
degree equality and residue separability condition.
-/

noncomputable section

universe u v w x

open ValuationTheory.DiscreteValuationField

namespace AlgebraicNumberTheory
namespace Valuations

section UnramifiedExtensions

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]

/-- Restriction of an exponential valuation to an intermediate field.
This is the valuation carried by each finite subextension in the union clause
of the finite unramified-extension definition. -/
def exponentialValuationRestrict
    (w : LubinTate.Valuations.ExponentialValuation L) (E : IntermediateField K L) :
    LubinTate.Valuations.ExponentialValuation E where
  toFun x := w (x : L)
  eq_top_iff x := by
    rw [w.eq_top_iff]
    simp
  map_mul x y := by
    exact w.map_mul (x : L) (y : L)
  add_le_min x y := by
    exact w.add_le_min (x : L) (y : L)

@[simp]
theorem exponentialValuationRestrict_apply
    (w : LubinTate.Valuations.ExponentialValuation L) (E : IntermediateField K L) (x : E) :
    exponentialValuationRestrict w E x = w (x : L) :=
  rfl

/-- The valuation-ring map associated with an exact extension of exponential
exponential valuations.  the fundamental inequality uses the same map internally; it is
exposed here because the finite unramified-extension definition also asks for separability of the actual
residue-field extension. -/
def unramifiedValuationRingValuationRingMap
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a) :
    LubinTate.Valuations.exponentialValuationSubring v →+*
      LubinTate.Valuations.exponentialValuationSubring w :=
  (algebraMap K L).restrict _ _ fun a ha ↦ by
    change (0 : WithTop ℝ) ≤ w (algebraMap K L a)
    rw [hExt]
    exact ha

@[simp]
theorem unramifiedValuationRingValuationRingMap_apply
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (a : LubinTate.Valuations.exponentialValuationSubring v) :
    ((unramifiedValuationRingValuationRingMap v w hExt a :
      LubinTate.Valuations.exponentialValuationSubring w) : L) =
        algebraMap K L (a : K) :=
  rfl

end UnramifiedExtensions

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_AbsoluteValue_ExponentialValuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Canonical exponential valuation attached to an absolute value

The localization arguments of the ramification-localization construction are naturally multiplicative, whereas the
unramified predicates of the unramified-extension construction use additive exponential valuations.  This file
supplies the canonical conversion `v(x) = -log |x|`.
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

variable {K : Type*} [Field K]

/-- The additive exponential valuation `- log |x|`, with value `∞` at zero. -/
def absoluteValueExponentialValuation
    (abv : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue abv) :
    LubinTate.Valuations.ExponentialValuation K := by
  classical
  refine
    { toFun := fun x ↦
        if x = 0 then ⊤ else ((-Real.log (abv x) : ℝ) : WithTop ℝ)
      eq_top_iff := ?_
      map_mul := ?_
      add_le_min := ?_ }
  · intro x
    by_cases hx : x = 0
    · simp [hx]
    · simp [hx]
  · intro x y
    by_cases hx : x = 0
    · subst x
      simp
    by_cases hy : y = 0
    · subst y
      simp
    have hxy : x * y ≠ 0 := mul_ne_zero hx hy
    simp only [hx, hy, hxy, ite_false, if_false, map_mul]
    rw [Real.log_mul (abv.ne_zero hx) (abv.ne_zero hy)]
    simp only [neg_add, WithTop.coe_add]
  · intro x y
    by_cases hx : x = 0
    · subst x
      simp
    by_cases hy : y = 0
    · subst y
      simp
    by_cases hxy : x + y = 0
    · simp [hxy]
    simp only [hx, hy, hxy, ite_false, if_false]
    apply WithTop.coe_le_coe.mpr
    by_cases hle : abv x ≤ abv y
    · have hlogxy : Real.log (abv x) ≤ Real.log (abv y) :=
        Real.strictMonoOn_log.monotoneOn (abv.pos hx) (abv.pos hy) hle
      rw [min_eq_right (neg_le_neg hlogxy)]
      apply neg_le_neg
      exact Real.strictMonoOn_log.monotoneOn (abv.pos hxy) (abv.pos hy)
        (((LubinTate.Valuations.strong_triangle_of_nonarchimedean abv hnonarch)
          x y).trans (max_eq_right hle).le)
    · have hyx : abv y ≤ abv x := le_of_not_ge hle
      have hlogyx : Real.log (abv y) ≤ Real.log (abv x) :=
        Real.strictMonoOn_log.monotoneOn (abv.pos hy) (abv.pos hx) hyx
      rw [min_eq_left (neg_le_neg hlogyx)]
      apply neg_le_neg
      exact Real.strictMonoOn_log.monotoneOn (abv.pos hxy) (abv.pos hx)
        (((LubinTate.Valuations.strong_triangle_of_nonarchimedean abv hnonarch)
          x y).trans (max_eq_left hyx).le)

@[simp] theorem absoluteValueExponentialValuation_apply_ne_zero
    (abv : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue abv)
    {x : K} (hx : x ≠ 0) :
    absoluteValueExponentialValuation abv hnonarch x =
      ((-Real.log (abv x) : ℝ) : WithTop ℝ) := by
  simp [absoluteValueExponentialValuation, hx]

/-- The original absolute value is associated to its canonical exponential
valuation, with base `e`. -/
theorem absoluteValueExponentialValuation_associated
    (abv : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue abv) :
    LubinTate.Valuations.AssociatedAbsoluteValue
      (absoluteValueExponentialValuation abv hnonarch)
      (Real.exp 1) abv := by
  refine ⟨Real.one_lt_exp_iff.mpr zero_lt_one, ?_⟩
  intro x hx
  refine ⟨-Real.log (abv x), ?_, ?_⟩
  · simp [absoluteValueExponentialValuation, hx]
  · simp only [neg_neg]
    exact (Real.exp_log (abv.pos hx)).symm.trans
      (Real.exp_one_rpow (Real.log (abv x))).symm

/-- Exact extension of nonarchimedean absolute values gives exact extension
of their canonical exponential valuations. -/
theorem absoluteValueExponentialValuation_extends
    {L : Type*} [Field L] [Algebra K L]
    (av : AbsoluteValue K ℝ) (aw : AbsoluteValue L ℝ)
    (hav : LubinTate.Valuations.NonarchimedeanAbsoluteValue av)
    (haw : LubinTate.Valuations.NonarchimedeanAbsoluteValue aw)
    (hExt : ∀ x : K, aw (algebraMap K L x) = av x) :
    ∀ x : K,
      absoluteValueExponentialValuation aw haw (algebraMap K L x) =
        absoluteValueExponentialValuation av hav x := by
  intro x
  by_cases hx : x = 0
  · subst x
    simp [absoluteValueExponentialValuation]
  · have hmx : algebraMap K L x ≠ 0 := (map_ne_zero _).mpr hx
    simp [absoluteValueExponentialValuation, hx, hmx, hExt]

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_HilbertRamification_AbsoluteValueConjugacy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Valuation conjugacy

For a possibly infinite Galois extension `L/K`, the Galois group acts
transitively on the extensions to `L` of a nontrivial absolute value of `K`.
-/

noncomputable section

universe u v

namespace AlgebraicNumberTheory
namespace Valuations

/-- Pull an absolute value back by a field automorphism.  This is the canonical
right action `w ↦ w ∘ σ`. -/
def absoluteValueConjugate
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (w : AbsoluteValue L ℝ) (σ : L ≃ₐ[K] L) : AbsoluteValue L ℝ :=
  w.comp (f := σ.toRingEquiv.toRingHom) σ.injective

@[simp] theorem absoluteValueConjugate_apply
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (w : AbsoluteValue L ℝ) (σ : L ≃ₐ[K] L) (x : L) :
    absoluteValueConjugate w σ x = w (σ x) :=
  rfl

end Valuations
end AlgebraicNumberTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_HilbertRamification_DecompositionGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Decomposition-group restriction law

This file gives the three tower-intersection formulas in their common ambient
Galois group.  The decomposition-group statement is formulated for arbitrary
absolute values, including the archimedean case.  The inertia and ramification
statements use valuation subrings and therefore cover the nonarchimedean case
in which those groups are defined.
-/

noncomputable section

universe u v w

namespace HilbertRamification

open AlgebraicNumberTheory.Valuations

variable (K : Type u) {L : Type w} [Field K] [Field L] [Algebra K L]

/-- The decomposition group of an absolute-value class.  Membership says that pullback by the
automorphism preserves the strict unit ball, equivalently the valuation
class, rather than requiring equality of chosen absolute-value representatives.
-/
def absoluteValueDecompositionGroup (w : AbsoluteValue L ℝ) :
    Subgroup (L ≃ₐ[K] L) where
  carrier := { σ | ∀ x : L, w (σ x) < 1 ↔ w x < 1 }
  one_mem' := by
    intro x
    rfl
  mul_mem' := by
    intro σ τ hσ hτ x
    exact (hσ (τ x)).trans (hτ x)
  inv_mem' := by
    intro σ hσ x
    have h := hσ (σ⁻¹ x)
    simpa using h.symm

@[simp] theorem mem_absoluteValueDecompositionGroup_iff
    (w : AbsoluteValue L ℝ) (σ : L ≃ₐ[K] L) :
    σ ∈ absoluteValueDecompositionGroup K w ↔
      ∀ x : L, w (σ x) < 1 ↔ w x < 1 :=
  Iff.rfl

/-- Membership really is preservation of the absolute-value class: the
pullback absolute value is equivalent to the chosen representative. -/
theorem mem_absoluteValueDecompositionGroup_iff_equivalent
    (w : AbsoluteValue L ℝ) (σ : L ≃ₐ[K] L) :
    σ ∈ absoluteValueDecompositionGroup K w ↔
      LubinTate.Valuations.EquivalentAbsoluteValues
        (w.comp (f := σ.toRingEquiv.toRingHom) σ.injective) w := by
  rw [LubinTate.Valuations.equivalentAbsoluteValues_iff_isEquiv,
    AbsoluteValue.isEquiv_iff_lt_one_iff]
  rfl

end HilbertRamification
end
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_HilbertRamification_DecompositionField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Decomposition field

The decomposition field is the fixed field of the decomposition group.  This
formulation uses absolute values and therefore includes the archimedean case.
-/

noncomputable section

universe u v

namespace HilbertRamification

open scoped Pointwise Topology

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]

/-- The decomposition-field definition: the decomposition field `Z_w` of a
absolute value `w` over `K`. -/
abbrev absoluteValueDecompositionField (w : AbsoluteValue L ℝ) :
    IntermediateField K L :=
  IntermediateField.fixedField (absoluteValueDecompositionGroup K w)

@[simp] theorem mem_absoluteValueDecompositionField_iff
    (w : AbsoluteValue L ℝ) (x : L) :
    x ∈ absoluteValueDecompositionField K w ↔
      ∀ σ ∈ absoluteValueDecompositionGroup K w, σ x = x :=
  IntermediateField.mem_fixedField_iff (H := absoluteValueDecompositionGroup K w) x

end HilbertRamification
end
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_HilbertRamification_DecompositionFieldExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Decomposition-field extension comparison

This file starts with clause (i): the restriction of `w` to its decomposition
field has a unique extension back to `L`.  The proof works for finite or
infinite Galois extensions and for archimedean or nonarchimedean valuations.
-/

noncomputable section

universe u v

namespace AlgebraicNumberTheory
namespace Valuations

/-- Restriction of an absolute value on `L` to an intermediate field. -/
def absoluteValueRestrictIntermediateField
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (w : AbsoluteValue L ℝ) (E : IntermediateField K L) : AbsoluteValue E ℝ :=
  w.comp (f := algebraMap E L) (algebraMap E L).injective

@[simp] theorem absoluteValueRestrictIntermediateField_apply
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (w : AbsoluteValue L ℝ) (E : IntermediateField K L) (x : E) :
    absoluteValueRestrictIntermediateField w E x = w (x : L) :=
  rfl

end Valuations
end AlgebraicNumberTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Completion_BaseChangeAdjoinRoot
attribute [-instance] _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# A primitive extension after scalar extension

If `L/K` has power basis generated by `α`, then the scalar extension
`A ⊗[K] L` is canonically `A[X]/(minpoly_K(α))`.  The equivalence below is
the canonical algebra equivalence used in scalar-extension decompositions.
-/

noncomputable section

namespace ValuationTheory
namespace Completion

universe u v w

open scoped TensorProduct Polynomial

/-- Scalar extension of a power basis. -/
noncomputable def powerBasisBaseChange
    {K A L : Type*} [Field K] [Field A] [Field L]
    [Algebra K A] [Algebra K L]
    (pb : PowerBasis K L) : PowerBasis A (A ⊗[K] L) where
  gen := 1 ⊗ₜ[K] pb.gen
  dim := pb.dim
  basis := Algebra.TensorProduct.basis A pb.basis
  basis_eq_pow i := by
    rw [Algebra.TensorProduct.basis_apply, pb.basis_eq_pow]
    simp [Algebra.TensorProduct.tmul_pow]

/-- The generator of a base-changed power basis is the tensor of one with the old generator. -/
@[simp]
theorem powerBasisBaseChange_gen
    {K A L : Type*} [Field K] [Field A] [Field L]
    [Algebra K A] [Algebra K L]
    (pb : PowerBasis K L) :
    (powerBasisBaseChange (A := A) pb).gen = 1 ⊗ₜ[K] pb.gen :=
  rfl

/-- The mapped primitive polynomial vanishes at `1 ⊗ α`. -/
theorem minpoly_map_aeval_one_tmul
    {K A L : Type*} [Field K] [Field A] [Field L]
    [Algebra K A] [Algebra K L]
    (pb : PowerBasis K L) :
    Polynomial.aeval (1 ⊗ₜ[K] pb.gen : A ⊗[K] L)
      ((minpoly K pb.gen).map (algebraMap K A)) = 0 := by
  rw [Polynomial.aeval_map_algebraMap]
  show Polynomial.aeval
      ((Algebra.TensorProduct.includeRight : L →ₐ[K] A ⊗[K] L) pb.gen)
        (minpoly K pb.gen) = 0
  rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]

/-- The canonical algebra map from the mapped primitive quotient to the
scalar extension. -/
noncomputable def adjoinRootToBaseChange
    {K A L : Type*} [Field K] [Field A] [Field L]
    [Algebra K A] [Algebra K L]
    (pb : PowerBasis K L) :
    AdjoinRoot ((minpoly K pb.gen).map (algebraMap K A)) →ₐ[A]
      A ⊗[K] L :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId A (A ⊗[K] L))
    (1 ⊗ₜ[K] pb.gen) (by
      change Polynomial.aeval (1 ⊗ₜ[K] pb.gen : A ⊗[K] L)
        ((minpoly K pb.gen).map (algebraMap K A)) = 0
      exact minpoly_map_aeval_one_tmul (A := A) pb)

/-- The map from an adjoined-root algebra to its base change sends root to root. -/
@[simp]
theorem adjoinRootToBaseChange_root
    {K A L : Type*} [Field K] [Field A] [Field L]
    [Algebra K A] [Algebra K L]
    (pb : PowerBasis K L) :
    adjoinRootToBaseChange (A := A) pb
        (AdjoinRoot.root ((minpoly K pb.gen).map (algebraMap K A))) =
      1 ⊗ₜ[K] pb.gen := by
  simp [adjoinRootToBaseChange]

/-- The canonical map from the adjoined-root algebra onto its base change is surjective. -/
theorem adjoinRootToBaseChange_surjective
    {K A L : Type*} [Field K] [Field A] [Field L]
    [Algebra K A] [Algebra K L]
    (pb : PowerBasis K L) :
    Function.Surjective (adjoinRootToBaseChange (A := A) pb) := by
  let q := (minpoly K pb.gen).map (algebraMap K A)
  let e := adjoinRootToBaseChange (A := A) pb
  let b := (powerBasisBaseChange (A := A) pb).basis
  change Function.Surjective e.toLinearMap
  rw [← e.toLinearMap.range_eq_top]
  apply top_unique
  rw [← b.span_eq]
  apply Submodule.span_le.2
  rintro _ ⟨i, rfl⟩
  refine ⟨AdjoinRoot.root q ^ (i : ℕ), ?_⟩
  change e (AdjoinRoot.root q ^ (i : ℕ)) = b i
  rw [map_pow, (powerBasisBaseChange (A := A) pb).basis_eq_pow,
    adjoinRootToBaseChange_root]
  rw [powerBasisBaseChange_gen, Algebra.TensorProduct.tmul_pow, one_pow]

/-- The mapped primitive quotient and scalar extension have equal dimension. -/
theorem adjoinRoot_baseChange_finrank_eq
    {K A L : Type*} [Field K] [Field A] [Field L]
    [Algebra K A] [Algebra K L]
    (pb : PowerBasis K L) :
    Module.finrank A
        (AdjoinRoot ((minpoly K pb.gen).map (algebraMap K A))) =
      Module.finrank A (A ⊗[K] L) := by
  let q := (minpoly K pb.gen).map (algebraMap K A)
  let hq : q.Monic :=
    (minpoly.monic pb.isIntegral_gen).map (algebraMap K A)
  let qpb : PowerBasis A (AdjoinRoot q) := AdjoinRoot.powerBasis' hq
  calc
    Module.finrank A (AdjoinRoot q) = q.natDegree := qpb.finrank
    _ = (minpoly K pb.gen).natDegree :=
      (minpoly.monic pb.isIntegral_gen).natDegree_map (algebraMap K A)
    _ = pb.dim := pb.natDegree_minpoly
    _ = Module.finrank A (A ⊗[K] L) :=
      (powerBasisBaseChange (A := A) pb).finrank.symm

/-- Canonical scalar-extension presentation, in the quotient-to-tensor
direction. -/
noncomputable def adjoinRootEquivBaseChange
    {K A L : Type*} [Field K] [Field A] [Field L]
    [Algebra K A] [Algebra K L]
    (pb : PowerBasis K L) :
    AdjoinRoot ((minpoly K pb.gen).map (algebraMap K A)) ≃ₐ[A]
      A ⊗[K] L := by
  let q := (minpoly K pb.gen).map (algebraMap K A)
  let hq : q.Monic :=
    (minpoly.monic pb.isIntegral_gen).map (algebraMap K A)
  letI : Module.Finite A (AdjoinRoot q) := hq.finite_adjoinRoot
  letI : Module.Finite A (A ⊗[K] L) :=
    (powerBasisBaseChange (A := A) pb).finite
  exact AlgEquiv.ofBijective (adjoinRootToBaseChange (A := A) pb)
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (adjoinRoot_baseChange_finrank_eq (A := A) pb)
        (f := (adjoinRootToBaseChange (A := A) pb).toLinearMap)).2
      (adjoinRootToBaseChange_surjective (A := A) pb),
      adjoinRootToBaseChange_surjective (A := A) pb⟩

/-- The adjoined-root/base-change equivalence preserves the distinguished root. -/
@[simp]
theorem adjoinRootEquivBaseChange_root
    {K A L : Type*} [Field K] [Field A] [Field L]
    [Algebra K A] [Algebra K L]
    (pb : PowerBasis K L) :
    adjoinRootEquivBaseChange (A := A) pb
        (AdjoinRoot.root ((minpoly K pb.gen).map (algebraMap K A))) =
      1 ⊗ₜ[K] pb.gen := by
  change adjoinRootToBaseChange (A := A) pb
      (AdjoinRoot.root ((minpoly K pb.gen).map (algebraMap K A))) = _
  exact adjoinRootToBaseChange_root (A := A) pb

/-- Canonical scalar-extension presentation of a primitive field extension. -/
noncomputable def baseChangeEquivAdjoinRoot
    {K A L : Type*} [Field K] [Field A] [Field L]
    [Algebra K A] [Algebra K L]
    (pb : PowerBasis K L) :
    A ⊗[K] L ≃ₐ[A]
      AdjoinRoot ((minpoly K pb.gen).map (algebraMap K A)) :=
  (adjoinRootEquivBaseChange (A := A) pb).symm

/-- The inverse base-change equivalence sends `1 ⊗ gen` to the adjoined root. -/
@[simp]
theorem baseChangeEquivAdjoinRoot_one_tmul_gen
    {K A L : Type*} [Field K] [Field A] [Field L]
    [Algebra K A] [Algebra K L]
    (pb : PowerBasis K L) :
    baseChangeEquivAdjoinRoot (A := A) pb (1 ⊗ₜ[K] pb.gen) =
      AdjoinRoot.root ((minpoly K pb.gen).map (algebraMap K A)) := by
  change (adjoinRootEquivBaseChange (A := A) pb).symm
      (1 ⊗ₜ[K] pb.gen) = _
  rw [← adjoinRootEquivBaseChange_root]
  exact (adjoinRootEquivBaseChange (A := A) pb).symm_apply_apply _

end Completion
end ValuationTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Completion_ExtensionFactorClassification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Classification of extensions of a completed absolute value

For a simple finite extension `L = K(α)`, the extensions of a nontrivial
absolute value of `K` correspond to the distinct irreducible factors, over
the completion, of an irreducible polynomial having `α` as a root.  The final
theorem below also records the explicit pullback valuation and the extension
of the chosen embedding to the completed field.
-/

noncomputable section

open Polynomial
open scoped Topology
open ValuationTheory.Completion

namespace AlgebraicNumberTheory
namespace Valuations

universe u v

/-- A root of the chosen irreducible polynomial is integral over the base
field.  This is derived from `hf` and `hroot`; it is not an extra hypothesis
of the extension-factor correspondence. -/
theorem completionExtensionFactor_root_isIntegral
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {α : L} {f : K[X]} (hf : Irreducible f)
    (hroot : Polynomial.aeval α f = 0) : IsIntegral K α :=
  (show IsAlgebraic K α from ⟨f, hf.ne_zero, hroot⟩).isIntegral

/-- An irreducible polynomial having `α` as a root is associated to the
minimal polynomial of `α`. -/
theorem completionExtensionFactor_definingPolynomial_associated_minpoly
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {α : L} {f : K[X]} (hf : Irreducible f)
    (hroot : Polynomial.aeval α f = 0) :
    Associated f (minpoly K α) := by
  have hlead : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf.ne_zero
  have hunit : IsUnit (C f.leadingCoeff⁻¹ : K[X]) :=
    isUnit_C.mpr (IsUnit.mk0 f.leadingCoeff⁻¹ (inv_ne_zero hlead))
  exact (associated_mul_unit_right f (C f.leadingCoeff⁻¹) hunit).trans
    (Associated.of_eq (minpoly.eq_of_irreducible hf hroot))

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Completion_PolynomialCRT
attribute [-instance] _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Polynomial Chinese remainder equivalence

This is the algebraic core of tensor-product decompositions.  A squarefree factorization
of the base-changed primitive polynomial gives the canonical product of its
simple factor algebras.
-/

noncomputable section

namespace ValuationTheory
namespace Completion

universe u v

open scoped Polynomial
open Function

/-- The Chinese remainder ring equivalence is an algebra equivalence over
any coefficient ring acting on the ambient commutative ring. -/
noncomputable def quotientInfAlgEquivPiQuotient
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {ι : Type*} [Finite ι]
    (I : ι → Ideal A) (hI : Pairwise (IsCoprime on I)) :
    (A ⧸ ⨅ i, I i) ≃ₐ[R] ∀ i, A ⧸ I i where
  __ := Ideal.quotientInfRingEquivPiQuotient I hI
  commutes' r := by
    ext i
    rfl

/-- Chinese remainder equivalence for a finite family of pairwise coprime
polynomials.  It is canonical: every polynomial class is sent to the family
of the same class modulo each factor. -/
noncomputable def adjoinRootProdEquivPi
    {F : Type u} [Field F] {ι : Type v} [Fintype ι]
    (f : ι → F[X])
    (hf : ∀ i j, i ≠ j → IsCoprime (f i) (f j)) :
    AdjoinRoot (∏ i, f i) ≃ₐ[F] ∀ i, AdjoinRoot (f i) := by
  let I : ι → Ideal F[X] := fun i => Ideal.span ({f i} : Set F[X])
  have hI : Pairwise (IsCoprime on I) := by
    intro i j hij
    exact (Ideal.isCoprime_span_singleton_iff (f i) (f j)).2
      (hf i j hij)
  have hInf : Ideal.span ({∏ i, f i} : Set F[X]) = ⨅ i, I i := by
    symm
    exact Ideal.iInf_span_singleton hf
  exact
    (Ideal.quotientEquivAlgOfEq F hInf).trans
      (quotientInfAlgEquivPiQuotient I hI)

/-- The product decomposition of an adjoined-root algebra evaluates
representatives coordinatewise. -/
@[simp]
theorem adjoinRootProdEquivPi_mk
    {F : Type u} [Field F] {ι : Type v} [Fintype ι]
    (f : ι → F[X])
    (hf : ∀ i j, i ≠ j → IsCoprime (f i) (f j))
    (g : F[X]) (i : ι) :
    adjoinRootProdEquivPi f hf (AdjoinRoot.mk (∏ i, f i) g) i =
      AdjoinRoot.mk (f i) g := by
  change Ideal.Quotient.mk (Ideal.span ({f i} : Set F[X])) g =
    Ideal.Quotient.mk (Ideal.span ({f i} : Set F[X])) g
  rfl

end Completion
end ValuationTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Completion_TensorProductDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Tensor-product decomposition over a completion

For a finite separable extension `L / K`, the canonical map
`L ⊗_K K_v → ∏_{w|v} L_w` is an isomorphism.  The proof follows the
construction: choose a primitive element, factor its mapped minimal polynomial,
apply the Chinese remainder theorem, and identify every simple factor with
the corresponding completion using the extension-factor correspondence.
-/

noncomputable section

open Polynomial
open scoped BigOperators TensorProduct
open ValuationTheory.Completion

namespace AlgebraicNumberTheory
namespace Valuations

universe u v

/-- The primitive power basis used in the separable proof of the completion
tensor-product decomposition. -/
noncomputable def completionTensorDecomposition_powerBasis
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] : PowerBasis K L :=
  Field.powerBasisOfFiniteOfSeparable K L

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Completion_FiniteProductNormTrace
attribute [-instance] _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Norms and traces on finite dependent products

These algebraic lemmas are the finite-product linear algebra used in
tensor-product norm and trace formulas.  Mathlib has the binary trace formula and the
determinant of a binary product map; the dependent finite-product versions
are recorded here so that the local factors are allowed to have different
field degrees.
-/

noncomputable section

namespace ValuationTheory
namespace Completion

universe u v w

open Module

/-- A component of a module-valued product is finite whenever the whole
product is finite.  Evaluation is a surjective linear map. -/
theorem moduleFiniteOfPi
    {R : Type u} [Semiring R]
    {ι : Type v} (M : ι → Type w)
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [Module.Finite R (∀ i, M i)] (i : ι) :
    Module.Finite R (M i) := by
  classical
  apply Module.Finite.of_surjective (LinearMap.proj i)
  intro x
  exact ⟨Pi.single i x, by simp⟩

end Completion
end ValuationTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Completion_ExtensionInvariants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Local degree, ramification, and residue invariants

For a finite separable extension `L / K` and a discrete nonarchimedean
absolute value `v` on `K`, this file proves the exact degree formula
`∑_{w ∣ v} e_w f_w = [L : K]`.

The proof makes explicit the two facts used implicitly in the construction: metric
completion preserves the value group and residue field, and every completed
local extension `L_w / K_v` is finite separable.  The fundamental inequality then gives
`[L_w : K_v] = e_w f_w`; summing and applying the local degree, norm, and trace formulas gives the result.
-/

noncomputable section

open scoped BigOperators

namespace AlgebraicNumberTheory.Valuations

universe u v

theorem mem_absoluteValueExponentialSubring_iff
    {K : Type u} [Field K] (a : AbsoluteValue K ℝ)
    (ha : LubinTate.Valuations.NonarchimedeanAbsoluteValue a) (x : K) :
    x ∈ LubinTate.Valuations.exponentialValuationSubring
        (absoluteValueExponentialValuation a ha) ↔ a x ≤ 1 := by
  rw [LubinTate.Valuations.mem_exponentialValuationSubring_iff]
  by_cases hx : x = 0
  · subst x
    simp [absoluteValueExponentialValuation]
  · rw [absoluteValueExponentialValuation_apply_ne_zero a ha hx]
    rw [WithTop.coe_nonneg]
    constructor
    · intro h
      by_contra hnot
      have hone : 1 < a x := lt_of_not_ge hnot
      linarith [Real.log_pos hone]
    · intro h
      exact neg_nonneg.mpr (Real.log_nonpos (a.nonneg x) h)

theorem mem_absoluteValueExponentialSubring_maximalIdeal_iff
    {K : Type u} [Field K] (a : AbsoluteValue K ℝ)
    (ha : LubinTate.Valuations.NonarchimedeanAbsoluteValue a)
    (x : LubinTate.Valuations.exponentialValuationSubring
      (absoluteValueExponentialValuation a ha)) :
    x ∈ IsLocalRing.maximalIdeal
        (LubinTate.Valuations.exponentialValuationSubring
          (absoluteValueExponentialValuation a ha)) ↔
      a (x : K) < 1 := by
  rw [← LubinTate.Valuations.exponentialMaxIdeal_eq_maximalIdeal]
  change (0 : WithTop ℝ) <
      absoluteValueExponentialValuation a ha (x : K) ↔ _
  by_cases hx : (x : K) = 0
  · simp [hx, absoluteValueExponentialValuation]
  · exact (LubinTate.Valuations.associatedAbsoluteValue_lt_one_iff
      (absoluteValueExponentialValuation_associated a ha) hx).symm


end AlgebraicNumberTheory.Valuations
end
end


