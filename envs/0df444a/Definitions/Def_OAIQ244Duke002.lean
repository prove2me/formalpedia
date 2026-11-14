-- Prove2me | Definitions.Def_OAIQ244Duke002
-- name    : OAIQ244Duke002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:11:29.111735+00:00
-- url     : https://prove2.me/theorems/3d47cc36-7f3d-4c70-92f0-9ffbd9ad96cf
-- title:
--   Definitions bundle OAIQ244Duke002 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 266 declarations of OpenAI's Lean: 122 definitions, 1 inductive type or structure, 12 instances, 130 theorems and 1 other declaration. The definitions and types are `AlgebraicNumberTheory.Valuations.henselFactorization_polyOfLimitCoeffs`, `AlgebraicNumberTheory.Valuations.padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt`, `AlgebraicNumberTheory.Valuations.withAbsNontriviallyNormedField`, `AlgebraicNumberTheory.numberFieldInRationalSeparableClosure`, `AlgebraicNumberTheory.numberFieldSeparableClosureEmbedding`, `AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure`, `ChosenFinitePlaceBaseCompletion`, `ClassFormation.continuousQuotientMk`, `CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandH0`, `CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandH0.equiv`, `CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandH0.lift`, `CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandH0.mk`, `CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandHMinusOne`, `CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandHMinusOne.equiv`, `CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandHMinusOne.mk`, `CyclicCohomology.ProfiniteCohomology.Herbrand.augmentationSubgroup`, `CyclicCohomology.ProfiniteCohomology.Herbrand.fixedSubgroup`, `CyclicCohomology.ProfiniteCohomology.Herbrand.normKernelSubgroup`, `CyclicCohomology.ProfiniteCohomology.Herbrand.sigmaMinusOne`, `CyclicCohomology.ProfiniteCohomology.Herbrand.sigmaMinusOneHom`, `CyclicCohomology.ProfiniteCohomology.Herbrand.tateNorm`, `CyclicCohomology.ProfiniteCohomology.Herbrand.tateNormHom`, `CyclicCohomology.ProfiniteCohomology.Herbrand.tateNormSubgroup`, `CyclicCohomology.baseIntegerScalarMulLinearMap`, `CyclicCohomology.baseIntegerScalarMulSubmodule`, `CyclicCohomology.chosenBaseUniformizerPowSubmodule`, `CyclicCohomology.chosenNormalBasisIntegerLattice`, `CyclicCohomology.chosenNormalBasisLatticeSuccQuot`, `CyclicCohomology.chosenNormalBasisLatticeSuccQuotConcreteLinearEquiv`, `CyclicCohomology.chosenNormalBasisLatticeSuccQuotLift`, `CyclicCohomology.chosenNormalBasisLatticeSuccQuotLinearLift`, `CyclicCohomology.chosenNormalBasisLatticeSuccQuotMk`, `CyclicCohomology.chosenNormalBasisLatticeSuccSubmodule`, `CyclicCohomology.chosenNormalBasisPrincipalUnitSet`, `CyclicCohomology.cyclicCosetEquiv`, `CyclicCohomology.inducedCoordinateProduct`, `CyclicCohomology.inducedCoordinates`, `CyclicCohomology.inducedFirstCoordinateHom`, `CyclicCohomology.inducedFixedEquiv`, `CyclicCohomology.inducedMulDistribMulAction` and 83 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AbstractClassFieldTheory_Degree_FrobeniusFixedField`, `AlgebraicNumberTheory_Adele_IntegralTensorSupport_AbsoluteValue`, `AlgebraicNumberTheory_Adele_IntegralTensorSupport_FinitePlaceCompletion`, `AlgebraicNumberTheory_Completion_ChosenLocalization`, `AlgebraicNumberTheory_FiniteAbelianCompositum`, `AlgebraicNumberTheory_Idele_Basic`, `AlgebraicNumberTheory_Idele_ClassGroup_Tower`, `AlgebraicNumberTheory_Idele_Extension_BaseChange`, `AlgebraicNumberTheory_Idele_Extension_ClassGroup`, `AlgebraicNumberTheory_Idele_Extension_GaloisNorm`, `AlgebraicNumberTheory_Idele_Extension_LocalComponent`, `AlgebraicNumberTheory_Idele_PrincipalCore`, `AlgebraicNumberTheory_Idele_Relative_Support`, `AlgebraicNumberTheory_SeparableClosureEmbedding`, `Cyclic_Herbrand_HerbrandLowDegree_Basic`, `Cyclic_Herbrand_HerbrandLowDegree_Product`, `Cyclic_Herbrand_Induced`, `Cyclic_Herbrand_NormalBasisLattice`, `InducedFunctions`, `LocalClassFieldTheory_ClassFormation_LocalBlocks_Tensor`, `LocalClassFieldTheory_ClassFormation_NormalBasisGaloisAction`, `LocalClassFieldTheory_ClassFormation_Valuation`, `LocalField_NonarchimedeanLocalField_FiniteUnramified`, `LocalField_NonarchimedeanLocalField_GaloisIntegerRing`, `LocalField_NonarchimedeanLocalField_IdealQuotients`, `LocalField_NonarchimedeanLocalField_ResidueExtension`, `LocalField_NonarchimedeanLocalField_ResidueGalois`, `LocalField_Padic_Cyclotomic_TotallyRamified_EisensteinPolynomial`, `Valuation_AbsoluteValue_Completeness`, `Valuation_Henselian_Factorization_AdicLimits`, `Valuation_Henselian_Factorization_Assembly`, `Valuation_Henselian_Factorization_Basic`, `Valuation_Henselian_Factorization_CoefficientMinimum`, `Valuation_Henselian_Factorization_DegreeBounds`, `Valuation_Henselian_Factorization_DivisionBounds`, `Valuation_Henselian_Factorization_ErrorPowers`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke014`, `OAIQ244Duke015`, `OAIQ244Duke016`, `OAIQ244Duke017`, `OAIQ244Duke018`, `OAIQ244Duke019`, `OAIQ244Duke020`, `OAIQ244Duke021` and `OAIQ244Duke024`.
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
import Mathlib.FieldTheory.Galois.GaloisClosure
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
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.NumberTheory.Cyclotomic.Discriminant
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.Ostrowski
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Padics.RingHoms
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
import Mathlib.RingTheory.IsAdjoinRoot
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
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.WellKnown
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

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Degree_FrobeniusFixedField
set_option synthInstance.maxHeartbeats 400000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace ClassFormation

/-!
# normalized degree and Frobenius theory: the fixed field of a Frobenius lift

This file gives the group-dual form of the Frobenius fixed-field theorem.  If `σ` is a
Frobenius lift in `G(\widetilde L | K)`, the subgroup `Γ` fixing the
field `Σ` is the closed subgroup topologically generated by `σ`.
-/

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]
/-- The quotient projection with its quotient topology, used locally below. -/
def continuousQuotientMk
    {A : Type*} [Group A] [TopologicalSpace A]
    (N : Subgroup A) [N.Normal] : A →ₜ* A ⧸ N where
  toMonoidHom := QuotientGroup.mk' N
  continuous_toFun := continuous_quotient_mk'

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Ideles of a number field

This file defines the ideles of a number field.

The finite ideles are defined as the restricted product of the multiplicative
groups of the finite completions with respect to the unit groups of their
valuation rings.  This is deliberately not the topology induced from the
finite adele ring: the latter is not the idele topology.  The infinite factor
is the unit group of the finite product of the archimedean completions.
-/

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section


variable (K : Type*) [Field K] [NumberField K]

/-- The finite idele group attached to a Dedekind domain and its fraction
field.  The number-field definition below specializes this to the ring of
integers. -/
abbrev FiniteIdeleGroupOf
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F] :=
  Πʳ v : HeightOneSpectrum R,
    [(v.adicCompletion F)ˣ, (v.adicCompletionIntegers F).units]

/-- The group of finite ideles of a number field. -/
abbrev FiniteIdeleGroup :=
  FiniteIdeleGroupOf (𝓞 K) K

/-- The product of the multiplicative groups of the archimedean completions. -/
abbrev InfiniteIdeleGroup :=
  (NumberField.InfiniteAdeleRing K)ˣ

/-- The idele group `I_K`. -/
abbrev IdeleGroup :=
  InfiniteIdeleGroup K × FiniteIdeleGroup K

namespace FiniteIdeleGroup

variable {K}

/-- Evaluation of a finite idele at a finite place. -/
def component (v : HeightOneSpectrum (𝓞 K)) :
    FiniteIdeleGroup K →* (v.adicCompletion K)ˣ where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem component_apply (a : FiniteIdeleGroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    component v a = a v :=
  rfl

end FiniteIdeleGroup

namespace InfiniteIdeleGroup

variable {K}

/-- The component of an infinite idele at an archimedean place. -/
def component (v : InfinitePlace K) :
    InfiniteIdeleGroup K →* v.Completionˣ :=
  (Pi.evalMonoidHom (fun w : InfinitePlace K ↦ w.Completionˣ) v).comp
    ContinuousMulEquiv.piUnits.toMonoidHom

omit [NumberField K] in
@[simp]
theorem component_apply (a : InfiniteIdeleGroup K) (v : InfinitePlace K) :
    component v a = ContinuousMulEquiv.piUnits a v :=
  rfl

end InfiniteIdeleGroup

namespace IdeleGroup

variable {K}

/-- Algebraically, the finite ideles over a Dedekind domain are the units of
its finite adele ring. -/
def finiteEquivFiniteAdeleUnitsOf
  (R : Type*) [CommRing R] [IsDedekindDomain R]
    (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F] :
    FiniteIdeleGroupOf R F ≃*
    (IsDedekindDomain.FiniteAdeleRing R F)ˣ :=
  (RestrictedProduct.unitsEquiv
    (ι := HeightOneSpectrum R)
    (S := fun v : HeightOneSpectrum R ↦ ValuationSubring (v.adicCompletion F))
    (B := fun v : HeightOneSpectrum R ↦ v.adicCompletionIntegers F)
    (𝓕 := Filter.cofinite)
    (fun v : HeightOneSpectrum R ↦ v.adicCompletion F)).symm

/-- The component of an idele at an archimedean place. -/
def infiniteComponent (v : InfinitePlace K) :
    IdeleGroup K →* v.Completionˣ :=
  (InfiniteIdeleGroup.component v).comp (MonoidHom.fst _ _)

/-- The component of an idele at a finite place. -/
def finiteComponent (v : HeightOneSpectrum (𝓞 K)) :
    IdeleGroup K →* (v.adicCompletion K)ˣ :=
  (FiniteIdeleGroup.component v).comp (MonoidHom.snd _ _)

@[simp]
theorem infiniteComponent_apply (a : IdeleGroup K) (v : InfinitePlace K) :
    infiniteComponent v a = ContinuousMulEquiv.piUnits a.1 v :=
  rfl

@[simp]
theorem finiteComponent_apply (a : IdeleGroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    finiteComponent v a = a.2 v :=
  rfl

/-- Algebraically, the finite ideles are the units of the finite adele ring.
The topology on the left is the restricted-product topology and is not
transported through this equivalence. -/
def finiteEquivFiniteAdeleUnits :
    FiniteIdeleGroup K ≃*
      (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ :=
  finiteEquivFiniteAdeleUnitsOf (𝓞 K) K

/-- Algebraically, the idele group is the unit group of the adele ring.

This is only a multiplicative equivalence.  It is intentionally not stated as
a homeomorphism because the idele topology is finer than the topology induced
from the adele ring. -/
def equivAdeleRingUnits :
    IdeleGroup K ≃* (NumberField.AdeleRing (𝓞 K) K)ˣ :=
  ((MulEquiv.refl (InfiniteIdeleGroup K)).prodCongr
      (finiteEquivFiniteAdeleUnits (K := K))).trans
    MulEquiv.prodUnits.symm

@[simp]
theorem equivAdeleRingUnits_fst (a : IdeleGroup K) :
    (MulEquiv.prodUnits (equivAdeleRingUnits a)).1 = a.1 := by
  rfl

@[simp]
theorem equivAdeleRingUnits_snd (a : IdeleGroup K) :
    (MulEquiv.prodUnits (equivAdeleRingUnits a)).2 =
      finiteEquivFiniteAdeleUnits (K := K) a.2 := by
  rfl

end IdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_PrincipalCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Principal ideles and the idele class group

This file formalizes the diagonal
embedding of `Kˣ` into the idele group and the resulting idele class group.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section


variable (K : Type*) [Field K] [NumberField K]

namespace IdeleGroup

/-- The diagonal embedding of `Kˣ` into the idele group. -/
def principalIdele : Kˣ →* IdeleGroup K :=
  (equivAdeleRingUnits (K := K)).symm.toMonoidHom.comp
    (Units.map (algebraMap K (NumberField.AdeleRing (𝓞 K) K)))

variable {K}

/-- The finite component of a principal idele is the image of the
underlying field element in the corresponding completion. -/
@[simp]
theorem finiteComponent_principalIdele
    (x : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ((finiteComponent v (principalIdele K x) :
      (v.adicCompletion K)ˣ) : v.adicCompletion K) = (x : K) :=
  rfl

/-- The infinite component of a principal idele is the image of the
underlying field element in the corresponding completion. -/
@[simp]
theorem infiniteComponent_principalIdele
    (x : Kˣ) (w : InfinitePlace K) :
    ((infiniteComponent w (principalIdele K x) :
      w.Completionˣ) : w.Completion) = (x : K) :=
  rfl

variable (K)

/-- The subgroup of principal ideles. -/
def principalSubgroup : Subgroup (IdeleGroup K) :=
  (principalIdele K).range

end IdeleGroup

/-- The idele class group `C_K = I_K / Kˣ`. -/
abbrev IdeleClassGroup :=
  IdeleGroup K ⧸ IdeleGroup.principalSubgroup K
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Extension_BaseChange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Ideles in finite extensions: the tensor-product model

This file uses the canonical presentation
`𝔸_L = 𝔸_K ⊗_K L`.  This makes extension, Galois conjugation, and the
idele norm formal linear-algebra operations.
-/

open scoped NumberField TensorProduct
open NumberField

noncomputable section


variable
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- The adele algebra of `L`, written in base-change form
`𝔸_K ⊗_K L`. -/
abbrev RelativeAdeleRing :=
  NumberField.AdeleRing (𝓞 K) K ⊗[K] L

/-- The idele group of the base-changed adele algebra. -/
abbrev RelativeIdeleGroup :=
  (RelativeAdeleRing K L)ˣ

namespace RelativeIdeleGroup

instance baseAdeleRingNontrivial :
    Nontrivial (NumberField.AdeleRing (𝓞 K) K) :=
  Function.Injective.nontrivial
    (NumberField.AdeleRing.algebraMap_injective
      (R := 𝓞 K) (K := K))

/-- The base-adele algebra map into its scalar extension. -/
def adeleInclusion :
    NumberField.AdeleRing (𝓞 K) K →+*
      RelativeAdeleRing K L :=
  (Algebra.TensorProduct.includeLeft
    (R := K) (S := K)
    (A := NumberField.AdeleRing (𝓞 K) K) (B := L)).toRingHom

/-- The extension field embedded in the scalar-extended adele algebra. -/
def fieldInclusion :
    L →+* RelativeAdeleRing K L :=
  (Algebra.TensorProduct.includeRight
    (R := K) (A := NumberField.AdeleRing (𝓞 K) K)
    (B := L)).toRingHom

/-- The canonical inclusion `I_K → I_L` in the tensor-product model. -/
def inclusion :
    IdeleGroup K →* RelativeIdeleGroup K L :=
  (Units.map (adeleInclusion K L)).comp
    (IdeleGroup.equivAdeleRingUnits (K := K)).toMonoidHom

/-- The diagonal copy of `Lˣ` inside the relative idele group. -/
def principalIdele :
    Lˣ →* RelativeIdeleGroup K L :=
  Units.map (fieldInclusion K L)

omit [NumberField L] [FiniteDimensional K L] in
@[simp]
theorem inclusion_principalIdele
    (x : Kˣ) :
    inclusion K L (IdeleGroup.principalIdele K x) =
      principalIdele K L
        (Units.map (algebraMap K L) x) := by
  apply Units.ext
  change
    (Algebra.TensorProduct.includeLeft
      (R := K) (S := K)
      (A := NumberField.AdeleRing (𝓞 K) K) (B := L))
        (algebraMap K
          (NumberField.AdeleRing (𝓞 K) K) (x : K)) =
      (Algebra.TensorProduct.includeRight
        (R := K) (A := NumberField.AdeleRing (𝓞 K) K)
        (B := L))
        (algebraMap K L (x : K))
  simp

/-- The norm of relative ideles, obtained as the determinant over
the base adele ring. -/
def norm :
    RelativeIdeleGroup K L →* IdeleGroup K :=
  (IdeleGroup.equivAdeleRingUnits (K := K)).symm.toMonoidHom.comp
    (Units.map
      (Algebra.norm
        (NumberField.AdeleRing (𝓞 K) K)))

omit [NumberField L] in
@[simp]
theorem norm_inclusion (a : IdeleGroup K) :
    norm K L (inclusion K L a) =
      a ^ Module.finrank K L := by
  apply (IdeleGroup.equivAdeleRingUnits (K := K)).injective
  simp only [norm, inclusion, MonoidHom.comp_apply]
  apply Units.ext
  change
    Algebra.norm (NumberField.AdeleRing (𝓞 K) K)
        (algebraMap
          (NumberField.AdeleRing (𝓞 K) K)
          (RelativeAdeleRing K L)
          ((IdeleGroup.equivAdeleRingUnits (K := K) a :
            (NumberField.AdeleRing (𝓞 K) K)ˣ) :
            NumberField.AdeleRing (𝓞 K) K)) =
      (((IdeleGroup.equivAdeleRingUnits (K := K) a) ^
          Module.finrank K L :
        (NumberField.AdeleRing (𝓞 K) K)ˣ) :
        NumberField.AdeleRing (𝓞 K) K)
  rw [Algebra.norm_algebraMap,
    Module.finrank_baseChange]
  rfl

omit [NumberField L] in
/-- Norm commutes with scalar extension from `K` to the base adele ring. -/
theorem norm_fieldInclusion (x : L) :
    Algebra.norm (NumberField.AdeleRing (𝓞 K) K)
        (fieldInclusion K L x) =
      algebraMap K (NumberField.AdeleRing (𝓞 K) K)
        (Algebra.norm K x) := by
  classical
  let b := Module.Free.chooseBasis K L
  let bA := b.baseChange
    (NumberField.AdeleRing (𝓞 K) K)
  rw [Algebra.norm_eq_matrix_det bA,
    Algebra.norm_eq_matrix_det b,
    (algebraMap K
      (NumberField.AdeleRing (𝓞 K) K)).map_det]
  congr 1
  ext i j
  simp [bA, b, fieldInclusion,
    Algebra.smul_def,
    Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.TensorProduct.tmul_mul_tmul]

omit [NumberField L] in
/-- The relative idele norm carries a principal idele to the
principal idele of the field norm. -/
@[simp]
theorem norm_principalIdele (x : Lˣ) :
    norm K L (principalIdele K L x) =
      IdeleGroup.principalIdele K
        (Units.map (Algebra.norm K) x) := by
  apply (IdeleGroup.equivAdeleRingUnits (K := K)).injective
  apply Units.ext
  change
    Algebra.norm (NumberField.AdeleRing (𝓞 K) K)
        (fieldInclusion K L (x : L)) =
      algebraMap K (NumberField.AdeleRing (𝓞 K) K)
        (Algebra.norm K (x : L))
  exact norm_fieldInclusion K L (x : L)

/-- Galois conjugation on the scalar-extended adele algebra. -/
def conjugation
    (σ : L ≃ₐ[K] L) :
    RelativeAdeleRing K L ≃ₐ[
      NumberField.AdeleRing (𝓞 K) K]
      RelativeAdeleRing K L :=
  Algebra.TensorProduct.congr AlgEquiv.refl σ

omit [NumberField L] [FiniteDimensional K L] in
@[simp]
theorem conjugation_tmul
    (σ : L ≃ₐ[K] L)
    (a : NumberField.AdeleRing (𝓞 K) K) (x : L) :
    conjugation K L σ (a ⊗ₜ[K] x) =
      a ⊗ₜ[K] σ x := by
  rfl

/-- Galois conjugation on relative ideles. -/
def conjugationIdele
    (σ : L ≃ₐ[K] L) :
    RelativeIdeleGroup K L ≃*
      RelativeIdeleGroup K L :=
  Units.mapEquiv (conjugation K L σ).toMulEquiv

omit [NumberField L] [FiniteDimensional K L] in
@[simp]
theorem conjugationIdele_coe
    (σ : L ≃ₐ[K] L) (a : RelativeIdeleGroup K L) :
    ((conjugationIdele K L σ a :
      RelativeIdeleGroup K L) : RelativeAdeleRing K L) =
      conjugation K L σ (a : RelativeAdeleRing K L) :=
  rfl

omit [NumberField L] [FiniteDimensional K L] in
theorem conjugation_one
    (a : RelativeAdeleRing K L) :
    conjugation K L (1 : L ≃ₐ[K] L) a = a := by
  change
    Algebra.TensorProduct.congr
        (AlgEquiv.refl :
          NumberField.AdeleRing (𝓞 K) K ≃ₐ[
            NumberField.AdeleRing (𝓞 K) K]
            NumberField.AdeleRing (𝓞 K) K)
        (AlgEquiv.refl : L ≃ₐ[K] L) a =
      a
  rw [Algebra.TensorProduct.congr_refl]
  rfl

omit [NumberField L] [FiniteDimensional K L] in
theorem conjugation_mul
    (σ τ : L ≃ₐ[K] L)
    (a : RelativeAdeleRing K L) :
    conjugation K L (σ * τ) a =
      conjugation K L σ (conjugation K L τ a) := by
  let e :
      NumberField.AdeleRing (𝓞 K) K ≃ₐ[
        NumberField.AdeleRing (𝓞 K) K]
        NumberField.AdeleRing (𝓞 K) K :=
    AlgEquiv.refl
  have he : e.trans e = e := by
    ext
    rfl
  have h :=
    Algebra.TensorProduct.congr_trans e e τ σ
  rw [he] at h
  change
    Algebra.TensorProduct.congr e (τ.trans σ) a =
      Algebra.TensorProduct.congr e σ
        (Algebra.TensorProduct.congr e τ a)
  exact congrArg
    (fun f :
      RelativeAdeleRing K L ≃ₐ[
        NumberField.AdeleRing (𝓞 K) K]
        RelativeAdeleRing K L ↦ f a) h

/-- The natural Galois action on relative ideles. -/
instance relativeIdeleMulAction :
    MulAction (L ≃ₐ[K] L) (RelativeIdeleGroup K L) where
  smul σ a := conjugationIdele K L σ a
  one_smul a := by
    apply Units.ext
    exact conjugation_one K L (a : RelativeAdeleRing K L)
  mul_smul σ τ a := by
    apply Units.ext
    change conjugation K L (σ * τ)
        (a : RelativeAdeleRing K L) =
      conjugation K L σ
        (conjugation K L τ (a : RelativeAdeleRing K L))
    exact conjugation_mul K L σ τ _

/-- The natural Galois action on relative ideles, viewed as an action by
group automorphisms. -/
@[reducible]
noncomputable def relativeIdeleMulDistribMulAction :
    MulDistribMulAction (L ≃ₐ[K] L) (RelativeIdeleGroup K L) where
  __ := relativeIdeleMulAction K L
  smul_one σ := map_one (conjugationIdele K L σ)
  smul_mul σ a b := map_mul (conjugationIdele K L σ) a b

omit [NumberField L] [FiniteDimensional K L] in
@[simp]
theorem smul_def
    (σ : L ≃ₐ[K] L) (a : RelativeIdeleGroup K L) :
    σ • a = conjugationIdele K L σ a :=
  rfl

omit [NumberField L] [FiniteDimensional K L] in
@[simp]
theorem smul_inclusion
    (σ : L ≃ₐ[K] L) (a : IdeleGroup K) :
    σ • inclusion K L a = inclusion K L a := by
  apply Units.ext
  change conjugation K L σ
      (algebraMap
        (NumberField.AdeleRing (𝓞 K) K)
        (RelativeAdeleRing K L)
        ((IdeleGroup.equivAdeleRingUnits (K := K) a :
          (NumberField.AdeleRing (𝓞 K) K)ˣ) :
          NumberField.AdeleRing (𝓞 K) K)) =
    algebraMap
      (NumberField.AdeleRing (𝓞 K) K)
      (RelativeAdeleRing K L)
      ((IdeleGroup.equivAdeleRingUnits (K := K) a :
        (NumberField.AdeleRing (𝓞 K) K)ˣ) :
        NumberField.AdeleRing (𝓞 K) K)
  exact (conjugation K L σ).commutes _

omit [NumberField L] [FiniteDimensional K L] in
@[simp]
theorem smul_principalIdele
    (σ : L ≃ₐ[K] L) (x : Lˣ) :
    σ • principalIdele K L x =
      principalIdele K L (Units.map σ.toRingEquiv.toMonoidHom x) := by
  apply Units.ext
  change conjugation K L σ
      (Algebra.TensorProduct.includeRight (x : L)) =
    Algebra.TensorProduct.includeRight (σ (x : L))
  change conjugation K L σ (1 ⊗ₜ[K] (x : L)) =
    1 ⊗ₜ[K] σ (x : L)
  rw [conjugation_tmul]

end RelativeIdeleGroup
end
end

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

/-- The determinant norm as a homogeneous polynomial in the coordinates
of a basis.  Keeping this polynomial over the ground field is what makes
the Galois product formula stable under arbitrary scalar extension. -/
def normPolynomial
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) : MvPolynomial ι K :=
  (-1 : MvPolynomial ι K) ^ Module.finrank K L *
    ((Algebra.lmul K L).toLinearMap.polyCharpoly b).coeff 0

@[simp]
theorem eval_normPolynomial
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (x : L) :
    MvPolynomial.eval (b.repr x) (normPolynomial b) =
      Algebra.norm K x := by
  rw [normPolynomial, map_mul, map_pow, map_neg, map_one,
    LinearMap.polyCharpoly_coeff_eval]
  exact ((Algebra.norm_apply K x).trans
    (LinearMap.det_eq_sign_charpoly_coeff
      ((Algebra.lmul K L) x))).symm

/-- Galois conjugation after scalar extension to an arbitrary commutative
`K`-algebra. -/
def scalarConjugation
    (A : Type*) [CommRing A] [Algebra K A]
    (σ : L ≃ₐ[K] L) :
    A ⊗[K] L →ₐ[A] A ⊗[K] L :=
  Algebra.TensorProduct.map (AlgHom.id A A) σ.toAlgHom

omit [FiniteDimensional K L] in
@[simp]
theorem scalarConjugation_tmul
    (A : Type*) [CommRing A] [Algebra K A]
    (σ : L ≃ₐ[K] L) (a : A) (x : L) :
    scalarConjugation (K := K) (L := L) A σ (a ⊗ₜ[K] x) =
      a ⊗ₜ[K] σ x :=
  rfl

omit [FiniteDimensional K L] in
@[simp]
theorem scalarConjugation_baseAdele_apply
    [NumberField K]
    (σ : L ≃ₐ[K] L) (z : RelativeAdeleRing K L) :
    scalarConjugation
        (NumberField.AdeleRing (𝓞 K) K) σ z =
      conjugation K L σ z :=
  rfl

end RelativeIdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Extension_LocalComponent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Local components of relative adeles and ideles

For a finite place `v` of `K`, evaluation on the finite-adele coordinate is
a `K`-algebra homomorphism `𝔸_K → K_v`.  Scalar extension along `L/K`
therefore gives the actual local component map

`𝔸_K ⊗[K] L → K_v ⊗[K] L`.

This is the map needed to apply the local tensor decomposition and the local
norm calculation to a genuine relative idele.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section


universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- Evaluation of an adele at an infinite place, as a `K`-algebra
homomorphism. -/
def infiniteAdeleComponentAlgHom
    (v : InfinitePlace K) :
    NumberField.AdeleRing (𝓞 K) K →ₐ[K]
      v.Completion :=
  (Pi.evalAlgHom K
      (fun w : InfinitePlace K => w.Completion) v).comp
    (AlgHom.fst K
      (NumberField.InfiniteAdeleRing K)
      (FiniteAdeleRing (𝓞 K) K))

@[simp]
theorem infiniteAdeleComponentAlgHom_apply
    (v : InfinitePlace K)
    (a : NumberField.AdeleRing (𝓞 K) K) :
    infiniteAdeleComponentAlgHom v a = a.1 v :=
  rfl

@[simp]
theorem infiniteAdeleComponentAlgHom_algebraMap
    (v : InfinitePlace K) (x : K) :
    infiniteAdeleComponentAlgHom v
        (algebraMap K
          (NumberField.AdeleRing (𝓞 K) K) x) =
      algebraMap K v.Completion x :=
  rfl

/-- The relative-adele component at an infinite place:
`𝔸_K ⊗[K] L → K_v ⊗[K] L`. -/
def relativeAdeleInfiniteComponent
    (v : InfinitePlace K) :
    RelativeAdeleRing K L →ₐ[K]
      v.Completion ⊗[K] L :=
  Algebra.TensorProduct.map
    (infiniteAdeleComponentAlgHom v)
    (AlgHom.id K L)

omit [NumberField L] [FiniteDimensional K L] in
@[simp]
theorem relativeAdeleInfiniteComponent_tmul
    (v : InfinitePlace K)
    (a : NumberField.AdeleRing (𝓞 K) K) (x : L) :
    relativeAdeleInfiniteComponent
        (K := K) (L := L) v (a ⊗ₜ[K] x) =
      a.1 v ⊗ₜ[K] x := by
  simp [relativeAdeleInfiniteComponent]

/-- Evaluation of an adele at a finite place, as a `K`-algebra
homomorphism. -/
def finiteAdeleComponentAlgHom
    (v : HeightOneSpectrum (𝓞 K)) :
    NumberField.AdeleRing (𝓞 K) K →ₐ[K]
      v.adicCompletion K :=
  { __ :=
      (RestrictedProduct.evalRingHom
        (fun w : HeightOneSpectrum (𝓞 K) =>
          w.adicCompletion K) v).comp
        (RingHom.snd
          (NumberField.InfiniteAdeleRing K)
          (FiniteAdeleRing (𝓞 K) K))
    commutes' := by
      intro x
      rfl }

@[simp]
theorem finiteAdeleComponentAlgHom_apply
    (v : HeightOneSpectrum (𝓞 K))
    (a : NumberField.AdeleRing (𝓞 K) K) :
    finiteAdeleComponentAlgHom v a = a.2 v :=
  rfl

@[simp]
theorem finiteAdeleComponentAlgHom_algebraMap
    (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    finiteAdeleComponentAlgHom v
        (algebraMap K
          (NumberField.AdeleRing (𝓞 K) K) x) =
      algebraMap K (v.adicCompletion K) x :=
  rfl

omit [NumberField L] [FiniteDimensional K L] in
/-- The relative-adele component at a finite place:
`𝔸_K ⊗[K] L → K_v ⊗[K] L`. -/
def relativeAdeleFiniteComponent
    (v : HeightOneSpectrum (𝓞 K)) :
    RelativeAdeleRing K L →ₐ[K]
      v.adicCompletion K ⊗[K] L :=
  Algebra.TensorProduct.map
    (finiteAdeleComponentAlgHom v)
    (AlgHom.id K L)

omit [NumberField L] [FiniteDimensional K L] in
@[simp]
theorem relativeAdeleFiniteComponent_tmul
    (v : HeightOneSpectrum (𝓞 K))
    (a : NumberField.AdeleRing (𝓞 K) K) (x : L) :
    relativeAdeleFiniteComponent (K := K) (L := L) v
        (a ⊗ₜ[K] x) =
      a.2 v ⊗ₜ[K] x := by
  simp [relativeAdeleFiniteComponent]

/-- The unit-valued infinite component of a relative idele. -/
def RelativeIdeleGroup.infiniteComponent
    (v : InfinitePlace K) :
    RelativeIdeleGroup K L →*
      (v.Completion ⊗[K] L)ˣ :=
  Units.map
    (relativeAdeleInfiniteComponent
      (K := K) (L := L) v).toRingHom

omit [NumberField L] [FiniteDimensional K L] in
@[simp]
theorem RelativeIdeleGroup.infiniteComponent_coe
    (v : InfinitePlace K)
    (a : RelativeIdeleGroup K L) :
    ((RelativeIdeleGroup.infiniteComponent
        (K := K) (L := L) v a :
        (v.Completion ⊗[K] L)ˣ) :
        v.Completion ⊗[K] L) =
      relativeAdeleInfiniteComponent
        (K := K) (L := L) v
        (a : RelativeAdeleRing K L) :=
  rfl

/-- The unit-valued local component of a relative idele. -/
def RelativeIdeleGroup.finiteComponent
    (v : HeightOneSpectrum (𝓞 K)) :
    RelativeIdeleGroup K L →*
      (v.adicCompletion K ⊗[K] L)ˣ :=
  Units.map
    (relativeAdeleFiniteComponent
      (K := K) (L := L) v).toRingHom

omit [NumberField L] [FiniteDimensional K L] in
@[simp]
theorem RelativeIdeleGroup.finiteComponent_coe
    (v : HeightOneSpectrum (𝓞 K))
    (a : RelativeIdeleGroup K L) :
    ((RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) v a :
        (v.adicCompletion K ⊗[K] L)ˣ) :
        v.adicCompletion K ⊗[K] L) =
      relativeAdeleFiniteComponent
        (K := K) (L := L) v
        (a : RelativeAdeleRing K L) :=
  rfl

/-- The determinant norm on the local tensor algebra. -/
def localTensorNorm
    (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K ⊗[K] L)ˣ →*
      (v.adicCompletion K)ˣ :=
  Units.map (Algebra.norm (v.adicCompletion K))

/-- Scalar extension of an archimedean base-field unit into its local
tensor algebra. -/
def infiniteLocalIdeleInclusion
    (v : InfinitePlace K) :
    v.Completionˣ →*
      (v.Completion ⊗[K] L)ˣ :=
  Units.map
    (Algebra.TensorProduct.includeLeft
      (R := K) (S := K)
      (A := v.Completion) (B := L)).toRingHom

/-- Scalar extension of an extension-field unit into an archimedean
local tensor algebra. -/
def infiniteLocalFieldIdeleInclusion
    (v : InfinitePlace K) :
    Lˣ →* (v.Completion ⊗[K] L)ˣ :=
  Units.map
    (Algebra.TensorProduct.includeRight
      (R := K) (A := v.Completion)
      (B := L)).toRingHom

/-- Scalar extension of a local base-field unit into the local tensor
algebra. -/
def localIdeleInclusion
    (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →*
      (v.adicCompletion K ⊗[K] L)ˣ :=
  Units.map
    (Algebra.TensorProduct.includeLeft
      (R := K) (S := K)
      (A := v.adicCompletion K) (B := L)).toRingHom

/-- Scalar extension of an extension-field unit into the local tensor
algebra. -/
def localFieldIdeleInclusion
    (v : HeightOneSpectrum (𝓞 K)) :
    Lˣ →* (v.adicCompletion K ⊗[K] L)ˣ :=
  Units.map
    (Algebra.TensorProduct.includeRight
      (R := K) (A := v.adicCompletion K)
      (B := L)).toRingHom
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Extension_ClassGroup
attribute [-simp] _root_.RelativeIdeleGroup.finiteComponent_coe _root_.RelativeIdeleGroup.infiniteComponent_coe _root_.RelativeIdeleGroup.scalarConjugation_baseAdele_apply _root_.relativeAdeleFiniteComponent_tmul _root_.relativeAdeleInfiniteComponent_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Idele classes in finite extensions

The tensor-product model makes the key intersection calculation

`I_K ∩ Lˣ = Kˣ`

an elementary linear-algebra statement.  A linear retraction of
`K → 𝔸_K` shows that an equality `a ⊗ 1 = 1 ⊗ x` forces both factors to
come from the same scalar in `K`.  We then descend the idele inclusion to
quotients and prove it injective.
-/

open scoped NumberField TensorProduct
open NumberField

noncomputable section


variable
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

namespace RelativeIdeleGroup

omit [NumberField L] [FiniteDimensional K L] in
/-- If a base adele and an extension-field element define the same
element of `𝔸_K ⊗_K L`, then they arise from one scalar of `K`. -/
theorem exists_scalar_of_adeleInclusion_eq_fieldInclusion
    (a : NumberField.AdeleRing (𝓞 K) K) (x : L)
    (h : adeleInclusion K L a = fieldInclusion K L x) :
    ∃ k : K,
      a = algebraMap K (NumberField.AdeleRing (𝓞 K) K) k ∧
      x = algebraMap K L k := by
  let η :=
    Algebra.linearMap K
      (NumberField.AdeleRing (𝓞 K) K)
  have hη : LinearMap.ker η = ⊥ :=
    LinearMap.ker_eq_bot.mpr
      (NumberField.AdeleRing.algebraMap_injective
        (R := 𝓞 K) (K := K))
  let ε :
      NumberField.AdeleRing (𝓞 K) K →ₗ[K] K :=
    η.leftInverse
  have hε :
      ε (1 : NumberField.AdeleRing (𝓞 K) K) = 1 := by
    change ε (algebraMap K
      (NumberField.AdeleRing (𝓞 K) K) 1) = 1
    exact LinearMap.leftInverse_apply_of_inj hη 1
  let q :
      RelativeAdeleRing K L →ₗ[K] L :=
    (TensorProduct.lid K L).toLinearMap.comp
      (TensorProduct.map ε LinearMap.id)
  have hq := congrArg q h
  have hx : x = algebraMap K L (ε a) := by
    simpa [q, adeleInclusion, fieldInclusion, hε,
      Algebra.smul_def] using hq.symm
  refine ⟨ε a, ?_, hx⟩
  apply
    (Algebra.TensorProduct.includeLeft_injective
      (R := K) (S := K)
      (A := NumberField.AdeleRing (𝓞 K) K) (B := L)
      (FaithfulSMul.algebraMap_injective K L))
  change adeleInclusion K L a =
    adeleInclusion K L
      (algebraMap K
        (NumberField.AdeleRing (𝓞 K) K) (ε a))
  rw [h, hx]
  exact (Algebra.TensorProduct.tmul_one_eq_one_tmul
    (A := NumberField.AdeleRing (𝓞 K) K)
    (B := L) (ε a)).symm

/-- The subgroup of principal relative ideles. -/
def principalSubgroup :
    Subgroup (RelativeIdeleGroup K L) :=
  (principalIdele K L).range

/-- The relative idele class group in the canonical presentation
`𝔸_L = 𝔸_K ⊗_K L`. -/
abbrev ClassGroup :=
  RelativeIdeleGroup K L ⧸ principalSubgroup K L

omit [NumberField L] [FiniteDimensional K L] in
/-- The preimage of the principal relative ideles under `I_K → I_L` is
exactly the subgroup of principal ideles of `K`. -/
theorem comap_principalSubgroup :
    Subgroup.comap (inclusion K L)
        (principalSubgroup K L) =
      IdeleGroup.principalSubgroup K := by
  ext a
  constructor
  · rintro ⟨x, hx⟩
    have htensor :
        adeleInclusion K L
            ((IdeleGroup.equivAdeleRingUnits (K := K) a :
              (NumberField.AdeleRing (𝓞 K) K)ˣ) :
              NumberField.AdeleRing (𝓞 K) K) =
          fieldInclusion K L (x : L) := by
      exact congrArg Units.val hx.symm
    obtain ⟨k, hkA, hkL⟩ :=
      exists_scalar_of_adeleInclusion_eq_fieldInclusion
        K L _ _ htensor
    have hk : k ≠ 0 := by
      intro hk0
      have : (x : L) = 0 := by
        rw [hkL, hk0, map_zero]
      exact x.ne_zero this
    let y : Kˣ := Units.mk0 k hk
    refine ⟨y, ?_⟩
    apply (IdeleGroup.equivAdeleRingUnits (K := K)).injective
    apply Units.ext
    change
      algebraMap K
          (NumberField.AdeleRing (𝓞 K) K) k =
        ((IdeleGroup.equivAdeleRingUnits (K := K) a :
          (NumberField.AdeleRing (𝓞 K) K)ˣ) :
          NumberField.AdeleRing (𝓞 K) K)
    exact hkA.symm
  · rintro ⟨y, rfl⟩
    refine ⟨Units.map (algebraMap K L) y, ?_⟩
    exact (inclusion_principalIdele K L y).symm

/-- Inclusion of ideles descends to inclusion of idele classes. -/
def classInclusion :
    IdeleClassGroup K →* ClassGroup K L :=
  QuotientGroup.map
    (IdeleGroup.principalSubgroup K)
    (principalSubgroup K L)
    (inclusion K L)
    (by
      rw [← comap_principalSubgroup K L])

omit [NumberField L] [FiniteDimensional K L] in
@[simp]
theorem classInclusion_mk (a : IdeleGroup K) :
    classInclusion K L
        (QuotientGroup.mk' (IdeleGroup.principalSubgroup K) a) =
      QuotientGroup.mk' (principalSubgroup K L)
        (inclusion K L a) :=
  rfl

/-- The determinant norm on relative ideles, descended to their
relative idele-class presentation. -/
noncomputable def classNorm :
    ClassGroup K L →* IdeleClassGroup K :=
  QuotientGroup.map
    (principalSubgroup K L)
    (IdeleGroup.principalSubgroup K)
    (RelativeIdeleGroup.norm K L)
    (by
      rintro _ ⟨x, rfl⟩
      refine
        ⟨Units.map (Algebra.norm K) x, ?_⟩
      exact
        (RelativeIdeleGroup.norm_principalIdele
          K L x).symm)

omit [NumberField L] in
@[simp]
theorem classNorm_mk
    (a : RelativeIdeleGroup K L) :
    classNorm K L
        (QuotientGroup.mk' (principalSubgroup K L) a) =
      QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K)
        (RelativeIdeleGroup.norm K L a) :=
  rfl

/-- The norm quotient in the relative idele-class presentation. -/
abbrev ClassNormQuotient :=
  IdeleClassGroup K ⧸ (classNorm K L).range

end RelativeIdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_ClassGroup_Tower
attribute [-simp] _root_.RelativeIdeleGroup.finiteComponent_coe _root_.RelativeIdeleGroup.infiniteComponent_coe _root_.RelativeIdeleGroup.scalarConjugation_baseAdele_apply _root_.relativeAdeleFiniteComponent_tmul _root_.relativeAdeleInfiniteComponent_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Idele-class norms in a field tower

For a tower `K ⊂ M ⊂ L`, keep the bottom field `K` fixed and write

`𝔸_M = 𝔸_K ⊗[K] M`,
`𝔸_L = (𝔸_K ⊗[K] M) ⊗[M] L`.

This gives an actual norm `C_L → C_M` whose composite with
`C_M → C_K` is the tower norm.  The resulting three concrete norm
quotients form a natural right-exact sequence.
-/

open scoped NumberField TensorProduct
open NumberField

noncomputable section

universe u

variable
    (K M L : Type u)
    [Field K] [NumberField K]
    [Field M] [NumberField M]
    [Field L] [NumberField L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L]

/-- The canonical right-factor `M`-algebra structure on
`𝔸_K ⊗[K] M`. -/
noncomputable instance (priority := 100)
    relativeAdeleRingIntermediateAlgebra :
    Algebra M (RelativeAdeleRing K M) :=
  Algebra.TensorProduct.rightAlgebra

/-- The relative adele algebra of `L`, presented over the intermediate
field while retaining the fixed bottom-field model of `𝔸_M`. -/
abbrev TowerRelativeAdeleRing :=
  RelativeAdeleRing K M ⊗[M] L

/-- The intermediate field acts on the one-step bottom-field model
`𝔸_K ⊗[K] L` through its embedding in `L`. -/
noncomputable instance (priority := 100)
    relativeAdeleRingTopIntermediateAlgebra :
    Algebra M (RelativeAdeleRing K L) :=
  ((Algebra.TensorProduct.includeRight
      (R := K)
      (A := NumberField.AdeleRing (𝓞 K) K)
      (B := L)).toRingHom.comp
        (algebraMap M L)).toAlgebra

/-- Extend the intermediate relative adele algebra along `M → L`. -/
def intermediateAdeleInclusion :
    RelativeAdeleRing K M →ₐ[M]
      RelativeAdeleRing K L where
  __ :=
    (Algebra.TensorProduct.map
      (AlgHom.id
        (NumberField.AdeleRing (𝓞 K) K)
        (NumberField.AdeleRing (𝓞 K) K))
      (IsScalarTower.toAlgHom K M L)).toRingHom
  commutes' m := by
    change
      1 ⊗ₜ[K] algebraMap M L m =
        1 ⊗ₜ[K] algebraMap M L m
    rfl

omit [NumberField M] [NumberField L]
    [FiniteDimensional K M] [FiniteDimensional M L] in
@[simp]
theorem intermediateAdeleInclusion_tmul
    (a : NumberField.AdeleRing (𝓞 K) K)
    (m : M) :
    intermediateAdeleInclusion K M L (a ⊗ₜ[K] m) =
      a ⊗ₜ[K] algebraMap M L m :=
  rfl

/-- The copy of `L` in the one-step relative adele algebra, regarded
as an `M`-algebra map. -/
def topFieldToOneStep :
    L →ₐ[M] RelativeAdeleRing K L where
  __ :=
    (Algebra.TensorProduct.includeRight
      (R := K)
      (A := NumberField.AdeleRing (𝓞 K) K)
      (B := L)).toRingHom
  commutes' _ := rfl

omit [NumberField M] [NumberField L] [Algebra K M]
    [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L] in
@[simp]
theorem topFieldToOneStep_apply
    (x : L) :
    topFieldToOneStep K M L x =
      (1 : NumberField.AdeleRing (𝓞 K) K) ⊗ₜ[K] x :=
  rfl

/-- Canonical ring equivalence
`(𝔸_K ⊗[K] M) ⊗[M] L ≃+* 𝔸_K ⊗[K] L`.

This is the standard tensor-product cancellation isomorphism: commute
the two outer factors, commute the inner scalar extension, cancel the
base change, and commute the remaining factors back. -/
def towerRelativeAdeleRingEquiv :
    TowerRelativeAdeleRing K M L ≃+*
      RelativeAdeleRing K L := by
  letI : Algebra L (TowerRelativeAdeleRing K M L) :=
    Algebra.TensorProduct.rightAlgebra
  let e₁ :=
    (Algebra.TensorProduct.commRight
      M L (RelativeAdeleRing K M)).symm
  let e₂ :=
    Algebra.TensorProduct.congr
      (AlgEquiv.refl : L ≃ₐ[M] L)
      (Algebra.TensorProduct.commRight K M
        (NumberField.AdeleRing (𝓞 K) K)).symm
  let e₃ :=
    Algebra.TensorProduct.cancelBaseChange
      K M L L (NumberField.AdeleRing (𝓞 K) K)
  let e₄ :=
    Algebra.TensorProduct.commRight
      K L (NumberField.AdeleRing (𝓞 K) K)
  exact
    e₁.toRingEquiv.trans
      (e₂.toRingEquiv.trans
        (e₃.toRingEquiv.trans e₄.toRingEquiv))

/-- Flatten the iterated scalar extension
`(𝔸_K ⊗[K] M) ⊗[M] L` to `𝔸_K ⊗[K] L`. -/
def towerRelativeAdeleFlatten :
    TowerRelativeAdeleRing K M L →ₐ[M]
      RelativeAdeleRing K L :=
  { (towerRelativeAdeleRingEquiv K M L).toRingHom with
    commutes' := by
      intro m
      change _ =
        (1 : NumberField.AdeleRing (𝓞 K) K) ⊗ₜ[K]
          algebraMap M L m
      simp [towerRelativeAdeleRingEquiv,
        Algebra.TensorProduct.right_algebraMap_apply,
        Algebra.smul_def] }

local instance instIsMulCommutativeClassGroup_r9ff11f_1 : IsMulCommutative (RelativeIdeleGroup.ClassGroup K L) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩
local instance instIsMulCommutativeIdeleClassGroup : IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩
end
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_HerbrandLowDegree_Basic
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace CyclicCohomology

/-!
# Low-degree Herbrand quotients

This reusable implementation supplies the low-degree cyclic cohomology used
by the class-formation and local class field theory layers.
-/

noncomputable section

open scoped BigOperators

namespace ProfiniteCohomology
namespace Herbrand

universe uG uA uB uC

/-- Herbrand-quotient theory: the finite-group norm `N_G a = ∏ g, g • a`
for a multiplicative `G`-module. -/
def tateNorm (G : Type uG) (A : Type uA) [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A] (a : A) : A :=
  ∏ g : G, g • a

/-- Herbrand-quotient theory: the multiplicative coboundary `a^(σ-1)`. -/
def sigmaMinusOne (G : Type uG) (A : Type uA) [Group G] [CommGroup A]
    [MulDistribMulAction G A] (σ : G) (a : A) : A :=
  σ • a * a⁻¹

/-- Herbrand-quotient theory: the fixed subgroup `A^G`. -/
def fixedSubgroup (G : Type uG) (A : Type uA) [Group G] [CommGroup A]
    [MulDistribMulAction G A] : Subgroup A where
  carrier := {a | ∀ g : G, g • a = a}
  one_mem' := by
    intro g
    exact MulDistribMulAction.smul_one g
  mul_mem' := by
    intro a b ha hb g
    rw [MulDistribMulAction.smul_mul, ha g, hb g]
  inv_mem' := by
    intro a ha g
    calc
      g • a⁻¹ = (g • a)⁻¹ := smul_inv' g a
      _ = a⁻¹ := by rw [ha g]

variable {G : Type uG} {A : Type uA} {B : Type uB} {C : Type uC}
variable [Group G] [Fintype G] [CommGroup A] [CommGroup B] [CommGroup C]
variable [MulDistribMulAction G A] [MulDistribMulAction G B] [MulDistribMulAction G C]

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- The finite-group norm is multiplicative. -/
theorem tateNorm_mul (a b : A) :
    tateNorm G A (a * b) = tateNorm G A a * tateNorm G A b := by
  calc
    tateNorm G A (a * b) = ∏ g : G, (g • a) * (g • b) := by
      unfold tateNorm
      apply Finset.prod_congr rfl
      intro g _hg
      exact MulDistribMulAction.smul_mul g a b
    _ = tateNorm G A a * tateNorm G A b := by
      simp only [tateNorm, Finset.prod_mul_distrib]

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- The Tate norm of the identity is the identity. -/
@[simp]
theorem tateNorm_one : tateNorm G A 1 = 1 := by
  unfold tateNorm
  exact Finset.prod_eq_one (fun g _hg => MulDistribMulAction.smul_one g)

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- The finite-group norm as a multiplicative homomorphism. -/
def tateNormHom : A →* A where
  toFun := tateNorm G A
  map_one' := tateNorm_one (G := G) (A := A)
  map_mul' := tateNorm_mul (G := G) (A := A)

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- The Tate norm homomorphism evaluates to the Tate norm. -/
@[simp]
theorem tateNormHom_apply (a : A) :
    tateNormHom (G := G) (A := A) a = tateNorm G A a :=
  rfl

omit [Fintype G] [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- The multiplicative coboundary `a ↦ a^(σ-1)` is multiplicative. -/
theorem sigmaMinusOne_mul (σ : G) (a b : A) :
    sigmaMinusOne G A σ (a * b) = sigmaMinusOne G A σ a * sigmaMinusOne G A σ b := by
  simp [sigmaMinusOne, mul_comm, mul_left_comm, mul_assoc]

omit [Fintype G] [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- The multiplicative coboundary `a ↦ a^(σ-1)` as a homomorphism. -/
def sigmaMinusOneHom (σ : G) : A →* A where
  toFun := sigmaMinusOne G A σ
  map_one' := by simp [sigmaMinusOne, MulDistribMulAction.smul_one]
  map_mul' := sigmaMinusOne_mul (G := G) (A := A) σ

omit [Fintype G] [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- The sigma-minus-one homomorphism evaluates to the sigma-minus-one operator. -/
@[simp]
theorem sigmaMinusOneHom_apply (σ : G) (a : A) :
    sigmaMinusOneHom (G := G) (A := A) σ a = sigmaMinusOne G A σ a :=
  rfl

/-- Herbrand-quotient theory: the norm image `N_G A`. -/
def tateNormSubgroup (G : Type uG) (A : Type uA) [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A] : Subgroup A :=
  MonoidHom.range (tateNormHom (G := G) (A := A))

/-- Herbrand-quotient theory: the norm kernel `{a | N_G a = 1}`. -/
def normKernelSubgroup (G : Type uG) (A : Type uA) [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A] : Subgroup A :=
  MonoidHom.ker (tateNormHom (G := G) (A := A))

/-- Herbrand-quotient theory: the augmentation image `I_G A` for a chosen `σ`. -/
def augmentationSubgroup (G : Type uG) (A : Type uA) [Group G] [CommGroup A]
    [MulDistribMulAction G A] (σ : G) : Subgroup A :=
  MonoidHom.range (sigmaMinusOneHom (G := G) (A := A) σ)

/-- Herbrand-quotient theory: multiplicative model of `H⁰(G,A)=A^G/N_G A`. -/
def HerbrandH0 (G : Type uG) (A : Type uA) [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A] : Type uA :=
  fixedSubgroup G A ⧸ (tateNormSubgroup G A).subgroupOf (fixedSubgroup G A)

/-- Herbrand-quotient theory: multiplicative model of
`H^{-1}(G,A) = ker(N_G)/I_G A` for a chosen generator `σ`. -/
def HerbrandHMinusOne (G : Type uG) (A : Type uA) [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A] (σ : G) : Type uA :=
  normKernelSubgroup G A ⧸ (augmentationSubgroup G A σ).subgroupOf (normKernelSubgroup G A)

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- Degree-zero Herbrand cohomology is a commutative group. -/
instance herbrandH0CommGroup : CommGroup (HerbrandH0 G A) := by
  unfold HerbrandH0
  infer_instance

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- Degree-minus-one Herbrand cohomology is a commutative group. -/
instance herbrandHMinusOneCommGroup (σ : G) :
    CommGroup (HerbrandHMinusOne G A σ) := by
  unfold HerbrandHMinusOne
  infer_instance

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- The sole public equivalence to the concrete quotient implementing
`H⁰(G,A)`. -/
def HerbrandH0.equiv :
    HerbrandH0 G A ≃*
      fixedSubgroup G A ⧸
        (tateNormSubgroup G A).subgroupOf (fixedSubgroup G A) := by
  change
    (fixedSubgroup G A ⧸
        (tateNormSubgroup G A).subgroupOf (fixedSubgroup G A)) ≃*
      fixedSubgroup G A ⧸
        (tateNormSubgroup G A).subgroupOf (fixedSubgroup G A)
  exact MulEquiv.refl _

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- The sole public equivalence to the concrete quotient implementing
`H⁻¹(G,A)`. -/
def HerbrandHMinusOne.equiv (σ : G) :
    HerbrandHMinusOne G A σ ≃*
      normKernelSubgroup G A ⧸
        (augmentationSubgroup G A σ).subgroupOf (normKernelSubgroup G A) := by
  change
    (normKernelSubgroup G A ⧸
        (augmentationSubgroup G A σ).subgroupOf (normKernelSubgroup G A)) ≃*
      normKernelSubgroup G A ⧸
        (augmentationSubgroup G A σ).subgroupOf (normKernelSubgroup G A)
  exact MulEquiv.refl _

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- Canonical projection from fixed points to `H⁰(G,A)`. -/
def HerbrandH0.mk : fixedSubgroup G A →* HerbrandH0 G A := by
  unfold HerbrandH0
  exact QuotientGroup.mk'
    ((tateNormSubgroup G A).subgroupOf (fixedSubgroup G A))

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- Canonical projection from the norm kernel to `H⁻¹(G,A)`. -/
def HerbrandHMinusOne.mk (σ : G) :
    normKernelSubgroup G A →* HerbrandHMinusOne G A σ := by
  unfold HerbrandHMinusOne
  exact QuotientGroup.mk'
    ((augmentationSubgroup G A σ).subgroupOf (normKernelSubgroup G A))

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- The degree-zero quotient equivalence sends the canonical class to the raw quotient class. -/
@[simp]
theorem HerbrandH0.equiv_mk (a : fixedSubgroup G A) :
    HerbrandH0.equiv (G := G) (A := A) (HerbrandH0.mk a) =
      QuotientGroup.mk a := by
  rfl

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- The degree-minus-one quotient equivalence sends the canonical class to the
raw quotient class. -/
@[simp]
theorem HerbrandHMinusOne.equiv_mk (σ : G) (a : normKernelSubgroup G A) :
    HerbrandHMinusOne.equiv (G := G) (A := A) σ
        (HerbrandHMinusOne.mk σ a) =
      QuotientGroup.mk a := by
  rfl

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- A fixed-point representative gives the trivial degree-zero class exactly
when it is a Tate norm. -/
@[simp]
theorem HerbrandH0.mk_eq_one_iff (a : fixedSubgroup G A) :
    HerbrandH0.mk a = 1 ↔ (a : A) ∈ tateNormSubgroup G A := by
  constructor
  · intro h
    have hraw :
        (QuotientGroup.mk a :
          fixedSubgroup G A ⧸
            (tateNormSubgroup G A).subgroupOf (fixedSubgroup G A)) = 1 := by
      simpa only [HerbrandH0.equiv_mk, map_one] using
        congrArg (HerbrandH0.equiv (G := G) (A := A)) h
    simpa only [Subgroup.mem_subgroupOf] using
      (QuotientGroup.eq_one_iff a).1 hraw
  · intro h
    apply (HerbrandH0.equiv (G := G) (A := A)).injective
    rw [HerbrandH0.equiv_mk, map_one]
    apply (QuotientGroup.eq_one_iff a).2
    simpa only [Subgroup.mem_subgroupOf] using h

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- Descend a homomorphism on fixed points through `H⁰(G,A)`. -/
def HerbrandH0.lift {M : Type*} [Group M]
    (f : fixedSubgroup G A →* M)
    (h : (tateNormSubgroup G A).subgroupOf (fixedSubgroup G A) ≤ f.ker) :
    HerbrandH0 G A →* M := by
  unfold HerbrandH0
  exact QuotientGroup.lift
    ((tateNormSubgroup G A).subgroupOf (fixedSubgroup G A)) f h

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- A homomorphism descended through degree-zero Herbrand cohomology agrees on representatives. -/
@[simp]
theorem HerbrandH0.lift_mk {M : Type*} [Group M]
    (f : fixedSubgroup G A →* M)
    (h : (tateNormSubgroup G A).subgroupOf (fixedSubgroup G A) ≤ f.ker)
    (a : fixedSubgroup G A) : HerbrandH0.lift f h (HerbrandH0.mk a) = f a := by
  rfl

end Herbrand
end ProfiniteCohomology

end
end CyclicCohomology
end

section
-- module Solutions.OAIQ244_DUKE.InducedFunctions
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Induced groups of equivariant functions

For a subgroup `H` of `G` acting on a commutative group `B`, the induced
group consists of functions satisfying `f (h * x) = h • f x`. Right
translation gives its `G`-action. Evaluation at the identity is an
`H`-equivariant epimorphism, without any finite-index assumption.
-/

namespace ProCGroups.InducedFunctions

universe uG uB

variable {G : Type uG} {B : Type uB}

/-- The subgroup of equivariant functions defining the induced group. -/
def inducedSubgroup [Group G] (H : Subgroup G) [CommGroup B]
    [MulDistribMulAction H B] : Subgroup (G → B) where
  carrier := {f | ∀ (h : H) (x : G), f (h.1 * x) = h • f x}
  one_mem' := by
    intro h x
    exact (smul_one h).symm
  mul_mem' := by
    intro f k hf hk h x
    simp only [Pi.mul_apply, hf h x, hk h x]
    exact (MulDistribMulAction.smul_mul h (f x) (k x)).symm
  inv_mem' := by
    intro f hf h x
    simp only [Pi.inv_apply, hf h x]
    exact (map_inv (MulDistribMulAction.toMonoidHom B h) (f x)).symm

/-- The commutative group of equivariant functions. -/
abbrev InducedModule [Group G] (H : Subgroup G) [CommGroup B]
    [MulDistribMulAction H B] :=
  inducedSubgroup (G := G) (B := B) H

/-- The canonical right-translation action on equivariant functions. -/
instance inducedMulDistribMulAction [Group G] (H : Subgroup G) [CommGroup B]
    [MulDistribMulAction H B] :
    MulDistribMulAction G (InducedModule (B := B) H) where
  smul g f := ⟨fun x ↦ f.1 (x * g), by
    intro h x
    simpa only [mul_assoc] using f.2 h (x * g)⟩
  one_smul := by
    intro f
    apply Subtype.ext
    funext x
    change f.1 (x * 1) = f.1 x
    rw [mul_one]
  mul_smul := by
    intro g k f
    apply Subtype.ext
    funext x
    change f.1 (x * (g * k)) = f.1 ((x * g) * k)
    rw [mul_assoc]
  smul_mul := by
    intro g f k
    ext x
    rfl
  smul_one := by
    intro g
    ext x
    rfl

/-- Evaluation at the identity element of the ambient group. -/
def inducedEvaluation [Group G] (H : Subgroup G) [CommGroup B]
    [MulDistribMulAction H B] :
    InducedModule (B := B) H →* B where
  toFun f := f.1 1
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem inducedEvaluation_apply [Group G] (H : Subgroup G) [CommGroup B]
    [MulDistribMulAction H B] (f : InducedModule (B := B) H) :
    inducedEvaluation H f = f.1 1 :=
  rfl

end ProCGroups.InducedFunctions
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_Induced
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Multiplicative induced modules

This file supplies the multiplicative induced-module model used in the
Herbrand quotient calculation.  If `H ≤ G` acts on a commutative group `B`, then
`Ind_H^G B` is represented by the equivariant functions

`f : G → B`,  `f (h * x) = h • f x`.

The ambient group acts by right translation.  This convention is the one
used for the products of the local multiplicative groups above a place.
The basic equivariant-function model is supplied by `ProCGroups.InducedFunctions`;
this module adds the cyclic-coordinate and Herbrand calculations.
-/

noncomputable section

namespace CyclicCohomology

open CyclicCohomology.ProfiniteCohomology.Herbrand

universe uG uB

variable {G : Type uG} {B : Type uB}

export ProCGroups.InducedFunctions
  (inducedSubgroup InducedModule inducedEvaluation inducedEvaluation_apply)

/-- Compatibility name for the canonical action supplied by the common core.
This alias is not registered as an additional instance. -/
abbrev inducedMulDistribMulAction [Group G] (H : Subgroup G) [CommGroup B]
    [MulDistribMulAction H B] :
    MulDistribMulAction G (InducedModule (B := B) H) :=
  ProCGroups.InducedFunctions.inducedMulDistribMulAction H

/-- Evaluation at the identity identifies the fixed points of an induced
module with the fixed points for the inducing subgroup. -/
noncomputable def inducedFixedEquiv [Group G] (H : Subgroup G)
    [CommGroup B] [MulDistribMulAction H B] :
    fixedSubgroup G (InducedModule (B := B) H) ≃*
      fixedSubgroup H B where
  toFun f := ⟨f.1.1 1, by
    intro h
    have hcov := f.1.2 h 1
    have hfix := congrArg
      (fun q : InducedModule (B := B) H ↦ q.1 1) (f.2 h.1)
    change f.1.1 (h.1 * 1) = h • f.1.1 1 at hcov
    change f.1.1 (1 * h.1) = f.1.1 1 at hfix
    have hcov' : h • f.1.1 1 = f.1.1 h.1 := by
      simpa using hcov.symm
    have hfix' : f.1.1 h.1 = f.1.1 1 := by
      simpa using hfix
    exact hcov'.trans hfix'⟩
  invFun b := ⟨⟨fun _ ↦ b.1, by
      intro h x
      exact (b.2 h).symm⟩,
    by
      intro g
      apply Subtype.ext
      funext x
      rfl⟩
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    have hx := congrArg
      (fun q : InducedModule (B := B) H ↦ q.1 1) (f.2 x)
    change f.1.1 (1 * x) = f.1.1 1 at hx
    simpa using hx.symm
  right_inv b := by
    apply Subtype.ext
    rfl
  map_mul' _ _ := rfl

@[simp]
theorem inducedFixedEquiv_apply_coe [Group G] (H : Subgroup G)
    [CommGroup B] [MulDistribMulAction H B]
    (f : fixedSubgroup G (InducedModule (B := B) H)) :
    (inducedFixedEquiv H f : B) = f.1.1 1 :=
  rfl

section CyclicCoordinates

variable [CommGroup G] [Fintype G]

omit [Fintype G] in
/-- A chosen generator of a finite cyclic group also generates its quotient
by any subgroup. -/
theorem quotientGenerator_generates (H : Subgroup G) (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ) :
    ∀ q : G ⧸ H, q ∈
      Subgroup.zpowers (QuotientGroup.mk' H σ) := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H q
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen x)
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  rw [← map_zpow]
  exact congrArg (QuotientGroup.mk' H) hk

omit [Fintype G] in
/-- The image of a cyclic generator in `G/H` has order `[G:H]`. -/
theorem quotientGenerator_order (H : Subgroup G) (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ) :
    orderOf (QuotientGroup.mk' H σ) = H.index := by
  rw [H.index_eq_card]
  exact orderOf_eq_card_of_forall_mem_zpowers
    (quotientGenerator_generates H σ hgen)

/-- The powers `1, σ, ..., σ^([G:H]-1)` form the canonical transversal
used in the cyclic induced-module calculation. -/
noncomputable def cyclicCosetEquiv (H : Subgroup G) (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ) :
    H × Fin H.index ≃ G := by
  classical
  letI : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  refine Equiv.ofBijective
    (fun p : H × Fin H.index ↦ p.1.1 * σ ^ p.2.1) ⟨?_, ?_⟩
  · intro p q hpq
    have hquot :
        (QuotientGroup.mk' H σ) ^ p.2.1 =
          (QuotientGroup.mk' H σ) ^ q.2.1 := by
      have hpone : QuotientGroup.mk' H p.1.1 = 1 :=
        (QuotientGroup.eq_one_iff p.1.1).mpr p.1.2
      have hqone : QuotientGroup.mk' H q.1.1 = 1 :=
        (QuotientGroup.eq_one_iff q.1.1).mpr q.1.2
      calc
        (QuotientGroup.mk' H σ) ^ p.2.1 =
            QuotientGroup.mk' H (p.1.1 * σ ^ p.2.1) := by
          rw [map_mul, map_pow, hpone, one_mul]
        _ = QuotientGroup.mk' H (q.1.1 * σ ^ q.2.1) :=
          congrArg (QuotientGroup.mk' H) hpq
        _ = (QuotientGroup.mk' H σ) ^ q.2.1 := by
          rw [map_mul, map_pow, hqone, one_mul]
    have hmod : p.2.1 ≡ q.2.1 [MOD H.index] := by
      have hm := (pow_eq_pow_iff_modEq
        (x := QuotientGroup.mk' H σ)).mp hquot
      rw [quotientGenerator_order H σ hgen] at hm
      exact hm
    have hij : p.2.1 = q.2.1 :=
      Nat.ModEq.eq_of_lt_of_lt hmod p.2.2 q.2.2
    have hfin : p.2 = q.2 := Fin.ext hij
    cases p with
    | mk ph pi =>
      cases q with
      | mk qh qi =>
        dsimp at hfin hpq ⊢
        subst qi
        apply congrArg (fun h : H ↦ (h, pi))
        apply Subtype.ext
        exact mul_right_cancel hpq
  · intro x
    have hcover := IsCyclic.image_range_card
      (a := QuotientGroup.mk' H σ)
      (quotientGenerator_generates H σ hgen)
    rw [← H.index_eq_card] at hcover
    have hxmem : QuotientGroup.mk' H x ∈
        Finset.image (fun i : ℕ ↦
          (QuotientGroup.mk' H σ) ^ i)
          (Finset.range H.index) := by
      rw [hcover]
      simp
    obtain ⟨i, hi, hqi⟩ := Finset.mem_image.mp hxmem
    have hdiv : x / σ ^ i ∈ H := by
      apply QuotientGroup.eq_iff_div_mem.mp
      simpa using hqi.symm
    refine
      ⟨(⟨x / σ ^ i, hdiv⟩,
        ⟨i, Finset.mem_range.mp hi⟩), ?_⟩
    exact div_mul_cancel x (σ ^ i)

@[simp]
theorem cyclicCosetEquiv_apply (H : Subgroup G) (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ)
    (h : H) (i : Fin H.index) :
    cyclicCosetEquiv H σ hgen (h, i) =
      h.1 * σ ^ i.1 := by
  exact congrFun
    (Equiv.coe_ofBijective
      (fun p : H × Fin H.index => p.1.1 * σ ^ p.2.1)
      (cyclicCosetEquiv H σ hgen).bijective) (h, i)

omit [Fintype G] in
/-- The power `σ^[G:H]` belongs to `H`. -/
theorem cyclic_pow_index_mem (H : Subgroup G) (σ : G) :
    σ ^ H.index ∈ H :=
  H.pow_index_mem σ

/-- The canonical generator of `H` attached to `σ`. -/
def subgroupGenerator (H : Subgroup G) (σ : G) : H :=
  ⟨σ ^ H.index, cyclic_pow_index_mem H σ⟩

omit [Fintype G] in
@[simp]
theorem subgroupGenerator_coe (H : Subgroup G) (σ : G) :
    (subgroupGenerator H σ : G) = σ ^ H.index :=
  rfl

end CyclicCoordinates

section InducedCoordinates

variable [CommGroup G] [Fintype G] [CommGroup B]
variable (H : Subgroup G) [MulDistribMulAction H B]

/-- Restriction to the canonical cyclic transversal identifies an induced
module with a finite product of copies of the inducing group. -/
noncomputable def inducedCoordinates (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ) :
    InducedModule (B := B) H ≃*
      (Fin H.index → B) where
  toFun f i := f.1 (σ ^ i.1)
  invFun v := ⟨fun x ↦
      let p := (cyclicCosetEquiv H σ hgen).symm x
      p.1 • v p.2,
    by
      intro h x
      let e := cyclicCosetEquiv H σ hgen
      let p := e.symm x
      have hp : p.1.1 * σ ^ p.2.1 = x := by
        have hx := e.apply_symm_apply x
        change p.1.1 * σ ^ p.2.1 = x at hx
        exact hx
      have hsymm :
          e.symm (h.1 * x) = (h * p.1, p.2) := by
        apply e.injective
        rw [e.apply_symm_apply]
        change h.1 * x =
          (h * p.1).1 * σ ^ p.2.1
        rw [← hp]
        simp only [Subgroup.coe_mul]
        exact (mul_assoc h.1 p.1.1
          (σ ^ p.2.1)).symm
      change
        (e.symm (h.1 * x)).1 •
            v (e.symm (h.1 * x)).2 =
          h • p.1 • v p.2
      rw [hsymm]
      exact mul_smul h p.1 (v p.2)⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    let e := cyclicCosetEquiv H σ hgen
    let p := e.symm x
    have hp : p.1.1 * σ ^ p.2.1 = x := by
      have hx := e.apply_symm_apply x
      change p.1.1 * σ ^ p.2.1 = x at hx
      exact hx
    change p.1 • f.1 (σ ^ p.2.1) = f.1 x
    rw [← hp]
    exact (f.2 p.1 (σ ^ p.2.1)).symm
  right_inv v := by
    funext i
    let e := cyclicCosetEquiv H σ hgen
    have hsymm : e.symm (σ ^ i.1) = (1, i) := by
      apply e.injective
      simp [e]
    change
      (e.symm (σ ^ i.1)).1 •
          v (e.symm (σ ^ i.1)).2 = v i
    rw [hsymm]
    exact one_smul H (v i)
  map_mul' f k := by
    funext i
    rfl

@[simp]
theorem inducedCoordinates_apply (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ)
    (f : InducedModule (B := B) H)
    (i : Fin H.index) :
    inducedCoordinates H σ hgen f i =
      f.1 (σ ^ i.1) :=
  rfl

/-- The multiplicative section supported on the first transversal
coordinate. -/
def inducedFirstCoordinateHom :
    B →* (Fin H.index → B) where
  toFun b i := if i.1 = 0 then b else 1
  map_one' := by
    funext i
    split <;> rfl
  map_mul' b c := by
    funext i
    by_cases hi : i.1 = 0 <;> simp [hi]

/-- The canonical multiplicative section from the inducing group. -/
noncomputable def inducedSection (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ) :
    B →* InducedModule (B := B) H :=
  (inducedCoordinates H σ hgen).symm.toMonoidHom.comp
    (inducedFirstCoordinateHom H)

@[simp]
theorem inducedSection_apply_one (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ) (b : B) :
    (inducedSection H σ hgen b).1 1 = b := by
  have hn : 0 < H.index := by
    rw [H.index_eq_card]
    exact Nat.card_pos
  let i0 : Fin H.index := ⟨0, hn⟩
  have h :=
    (inducedCoordinates_apply H σ hgen
      ((inducedCoordinates H σ hgen).symm
        (inducedFirstCoordinateHom H b)) i0).symm.trans
      (congrFun
        ((inducedCoordinates H σ hgen).apply_symm_apply
          (inducedFirstCoordinateHom H b)) i0)
  change (inducedSection H σ hgen b).1 (σ ^ (0 : ℕ)) = b at h
  simpa only [pow_zero] using h

/-- Product over the canonical transversal. -/
noncomputable def inducedCoordinateProduct (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ) :
    InducedModule (B := B) H →* B where
  toFun f :=
    ∏ i : Fin H.index,
      inducedCoordinates H σ hgen f i
  map_one' := by simp
  map_mul' f k := by
    simp only [map_mul, Pi.mul_apply,
      Finset.prod_mul_distrib]

@[simp]
theorem inducedCoordinateProduct_apply (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ)
    (f : InducedModule (B := B) H) :
    inducedCoordinateProduct H σ hgen f =
      ∏ i : Fin H.index, f.1 (σ ^ i.1) :=
  rfl

/-- The first-coordinate section is a right inverse to the transversal
product. -/
@[simp]
theorem inducedCoordinateProduct_section (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ) (b : B) :
    inducedCoordinateProduct H σ hgen
        (inducedSection H σ hgen b) = b := by
  classical
  have hn : 0 < H.index := by
    rw [H.index_eq_card]
    exact Nat.card_pos
  let i0 : Fin H.index := ⟨0, hn⟩
  change (∏ i : Fin H.index,
    inducedCoordinates H σ hgen
      ((inducedCoordinates H σ hgen).symm
        (inducedFirstCoordinateHom H b)) i) = b
  rw [(inducedCoordinates H σ hgen).apply_symm_apply
    (inducedFirstCoordinateHom H b)]
  refine Finset.prod_eq_single i0 ?_ ?_
  · intro i _hi hne
    have hi0 : i.1 ≠ 0 := by
      intro hi
      apply hne
      exact Fin.ext hi
    simp [inducedFirstCoordinateHom, hi0]
  · intro hnot
    exact (hnot (Finset.mem_univ i0)).elim

end InducedCoordinates

end CyclicCohomology
end
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_HerbrandLowDegree_Product
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Low-degree Tate cohomology of products

This file proves that multiplicative Tate `H⁰` and `H⁻¹` commute with
dependent products, giving the product step for low-degree Herbrand quotients.
-/

noncomputable section

namespace CyclicCohomology

open CyclicCohomology.ProfiniteCohomology.Herbrand

universe uG uι uA

/-- The componentwise multiplicative action on a dependent product. -/
@[reducible]
def piMulDistribMulAction
    (G : Type uG) [Group G]
    {ι : Type uι} (A : ι → Type uA)
    [∀ i, CommGroup (A i)]
    [∀ i, MulDistribMulAction G (A i)] :
    MulDistribMulAction G (∀ i, A i) where
  smul g x i := g • x i
  one_smul x := by
    funext i
    exact one_smul G (x i)
  mul_smul g h x := by
    funext i
    exact mul_smul g h (x i)
  smul_one g := by
    funext i
    exact MulDistribMulAction.smul_one g
  smul_mul g x y := by
    funext i
    exact MulDistribMulAction.smul_mul g (x i) (y i)

end CyclicCohomology
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_ResidueExtension
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
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

/-- The local-ring homomorphism on valuation integer rings induced by an extension
of valuations. -/
def integerRingMapOfValuationExtension (K L : Type u) [Field K] [ValuativeRel K]
    [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    𝒪[K] →+* 𝒪[L] :=
  algebraMap 𝒪[K] 𝒪[L]

/-- The map of valuation rings induced by a valued-field extension is a local ring homomorphism. -/
instance integerRingMapOfValuationExtension_isLocalHom (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    IsLocalHom (integerRingMapOfValuationExtension K L) := by
  change IsLocalHom (algebraMap 𝒪[K] 𝒪[L])
  infer_instance

/-- The valuation-ring map of an extension is the ambient algebra map on underlying elements. -/
@[simp]
theorem integerRingMapOfValuationExtension_apply (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (x : 𝒪[K]) :
    integerRingMapOfValuationExtension K L x = algebraMap 𝒪[K] 𝒪[L] x :=
  rfl

/-- The residue-field map induced by a valuation extension.  This is the
canonical `algebraMap 𝓀[K] 𝓀[L]`, named so later
local class field theory files can use it without unfolding mathlib's valuation-extension instances. -/
def residueFieldMapOfValuationExtension (K L : Type u) [Field K] [ValuativeRel K]
    [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    𝓀[K] →+* 𝓀[L] :=
  IsLocalRing.ResidueField.map (integerRingMapOfValuationExtension K L)

/-- The residue-field map sends the residue of a base integer to the residue of its image in the
extension. -/
@[simp]
theorem residueFieldMapOfValuationExtension_residue (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (x : 𝒪[K]) :
    residueFieldMapOfValuationExtension K L (IsLocalRing.residue 𝒪[K] x) =
      IsLocalRing.residue 𝒪[L] (integerRingMapOfValuationExtension K L x) :=
  rfl

/-- The residue-field algebra map commutes with reduction of valuation-ring elements. -/
@[simp]
theorem residueField_algebraMap_residue (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (x : 𝒪[K]) :
    algebraMap 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[K] x) =
      IsLocalRing.residue 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] x) :=
  rfl

/-- The induced map on residue-field unit groups. -/
def residueUnitsMapOfValuationExtension (K L : Type u) [Field K] [ValuativeRel K]
    [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    𝓀[K]ˣ →* 𝓀[L]ˣ :=
  Units.map (residueFieldMapOfValuationExtension K L)

/-- The induced map on residue-field units applies the residue-field extension map to the underlying
residue. -/
@[simp]
theorem residueUnitsMapOfValuationExtension_apply (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (u : 𝓀[K]ˣ) :
    ((residueUnitsMapOfValuationExtension K L u : 𝓀[L]ˣ) : 𝓀[L]) =
      algebraMap 𝓀[K] 𝓀[L] (u : 𝓀[K]) :=
  rfl

/-- Base integer units embedded into extension integer units. -/
def integerUnitsMapOfValuationExtension (K L : Type u) [Field K] [ValuativeRel K]
    [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    𝒪[K]ˣ →* 𝒪[L]ˣ :=
  Units.map (integerRingMapOfValuationExtension K L).toMonoidHom

/-- The induced map on valuation-ring units applies the extension's integer-ring map to the
underlying unit. -/
@[simp]
theorem integerUnitsMapOfValuationExtension_apply (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (u : 𝒪[K]ˣ) :
    ((integerUnitsMapOfValuationExtension K L u : 𝒪[L]ˣ) : 𝒪[L]) =
      integerRingMapOfValuationExtension K L (u : 𝒪[K]) :=
  rfl

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_GaloisIntegerRing
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
/-!
# Galois actions on valuation rings

Restricts Galois automorphisms to valuation rings and transports their action
to ideals, ideal-power quotients, principal units, and successive quotients.
-/

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- A real Galois automorphism preserves the valuation integer ring when that
ring is the integral closure of the base valuation integer ring.

This is the source-producing replacement for proving integer-ring preservation
from a valuation-invariance certificate: integrality is transported by the
`K`-algebra automorphism, and integral-closure membership brings the element
back to `𝒪[L]`. -/
theorem galoisGroup_mem_integerRing_of_isIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (σ : Gal(L / K)) (x : 𝒪[L]) :
    σ (x : L) ∈ 𝒪[L] := by
  have hx : IsIntegral 𝒪[K] ((x : 𝒪[L]) : L) :=
    (IsIntegralClosure.isIntegral_iff (A := 𝒪[L]) (R := 𝒪[K]) (B := L)).2
      ⟨x, rfl⟩
  have hσ : IsIntegral 𝒪[K] (σ ((x : 𝒪[L]) : L)) :=
    IsIntegral.map σ.toAlgHom hx
  rcases (IsIntegralClosure.isIntegral_iff (A := 𝒪[L]) (R := 𝒪[K]) (B := L)).1 hσ
    with ⟨y, hy⟩
  exact hy ▸ y.2

/-- Restrict a real Galois automorphism to the valuation integer ring using the
actual integral-closure property of valuation integer rings. -/
def galoisGroupIntegerRingEquivOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L / K)) :
    𝒪[L] ≃+* 𝒪[L] where
  toFun x :=
    ⟨σ (x : L), galoisGroup_mem_integerRing_of_isIntegralClosure K L σ x⟩
  invFun x :=
    ⟨σ.symm (x : L), galoisGroup_mem_integerRing_of_isIntegralClosure K L σ.symm x⟩
  left_inv := by
    intro x
    ext
    simp
  right_inv := by
    intro x
    ext
    simp
  map_mul' := by
    intro x y
    ext
    simp
  map_add' := by
    intro x y
    ext
    simp

/-- Restriction sends a field automorphism to the corresponding automorphism of the integral-closure
valuation ring. -/
@[simp]
theorem galoisGroupIntegerRingEquivOfIsIntegralClosure_apply
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (σ : Gal(L / K)) (x : 𝒪[L]) :
    ((galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ x : 𝒪[L]) : L) =
      σ (x : L) :=
  rfl

/-- The inverse restriction equivalence extends an integer-ring automorphism to the ambient field. -/
@[simp]
theorem galoisGroupIntegerRingEquivOfIsIntegralClosure_symm_apply
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (σ : Gal(L / K)) (x : 𝒪[L]) :
    (((galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).symm x : 𝒪[L]) : L) =
      σ.symm (x : L) :=
  rfl

/-- Restriction of a Galois automorphism commutes with the inclusion of the integer ring into the
field. -/
theorem galoisGroupIntegerRingEquivOfIsIntegralClosure_integerRingMap
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (σ : Gal(L / K)) (x : 𝒪[K]) :
    galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ
        (integerRingMapOfValuationExtension K L x) =
      integerRingMapOfValuationExtension K L x := by
  ext
  change σ (algebraMap K L (x : K)) = algebraMap K L (x : K)
  exact σ.commutes (x : K)

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_IdealQuotients
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial
attribute [-simp] _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-! ### Residue and maximal-ideal successive quotients -/

/-- Additive identification of the residue field with `𝒪[K]/𝓂[K]`.

This is definitional for mathlib's local-ring residue field, but we expose it as
part of the local CFT boundary so later files do not depend on unfolding the
residue-field definition. -/
def integerRingModMaximalIdealAddEquivResidue
    (K : Type u) [Field K] [ValuativeRel K] :
    (𝒪[K] ⧸ (𝓂[K] : Ideal 𝒪[K])) ≃+ 𝓀[K] :=
  AddEquiv.refl _

/-- The additive equivalence from the integer ring modulo its maximal ideal sends a representative
to its residue class. -/
@[simp]
theorem integerRingModMaximalIdealAddEquivResidue_mk
    (K : Type u) [Field K] [ValuativeRel K] (x : 𝒪[K]) :
    integerRingModMaximalIdealAddEquivResidue K
        (Ideal.Quotient.mk (𝓂[K] : Ideal 𝒪[K]) x) =
      IsLocalRing.residue 𝒪[K] x :=
  rfl

/-- A chosen DVR uniformizer of the valuation ring of a nonarchimedean local
field, viewed as an irreducible element of `𝒪[K]`. -/
def chosenIntegerRingUniformizer
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : 𝒪[K] :=
  Classical.choose (IsDiscreteValuationRing.exists_irreducible 𝒪[K])

/-- The chosen integer-ring uniformizer is irreducible in the discrete valuation ring. -/
theorem chosenIntegerRingUniformizer_irreducible
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Irreducible (chosenIntegerRingUniformizer K) :=
  Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible 𝒪[K])

/-- The maximal ideal is the principal ideal generated by the chosen integer-ring uniformizer. -/
theorem chosenIntegerRingUniformizer_maximalIdeal_eq
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    (𝓂[K] : Ideal 𝒪[K]) = Ideal.span ({chosenIntegerRingUniformizer K} : Set 𝒪[K]) :=
  (chosenIntegerRingUniformizer_irreducible K).maximalIdeal_eq

/-- The chosen DVR uniformizer of `𝒪[K]`, viewed as a nonzero field unit.

This is the source object for the local class-field decomposition by powers of
a prime element.  Valuation normalization is proved separately; it is not an
extra argument of this definition. -/
def integerRingUniformizerFieldUnit
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Kˣ :=
  Units.mk0 (((chosenIntegerRingUniformizer K : 𝒪[K]) : K)) (by
    intro h
    exact (chosenIntegerRingUniformizer_irreducible K).ne_zero (Subtype.ext h))

/-- The field unit associated to the chosen integer-ring uniformizer has the same underlying field
element. -/
@[simp]
theorem integerRingUniformizerFieldUnit_coe
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    ((integerRingUniformizerFieldUnit K : Kˣ) : K) =
      (((chosenIntegerRingUniformizer K : 𝒪[K]) : K)) :=
  rfl

/-- The inverse of the chosen DVR uniformizer, as a field unit.

With the normalized additive valuation used by `valuationMap`, this is the
element expected to have value `1`.  The proof of that normalization is the next
source-producing frontier. -/
def inverseIntegerRingUniformizerFieldUnit
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Kˣ :=
  (integerRingUniformizerFieldUnit K)⁻¹

/-- The inverse uniformizer field unit coerces to the inverse of the chosen uniformizer. -/
@[simp]
theorem inverseIntegerRingUniformizerFieldUnit_coe
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    ((inverseIntegerRingUniformizerFieldUnit K : Kˣ) : K) =
      (((chosenIntegerRingUniformizer K : 𝒪[K]) : K))⁻¹ :=
  rfl

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_Valuation
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false
/-! Provides the public declarations in the `LocalClassFieldTheory.ClassFormation.Valuation` Lean module. -/

namespace LocalClassFieldTheory

open LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel
open IsNonarchimedeanLocalField

/-- The actual `Gal(L / K)` action on field units, obtained by applying each
field automorphism to a unit. -/
@[implicit_reducible]
def galoisGroupFieldUnitsMulDistribMulAction
    (K L : Type u) [Field K] [Field L] [Algebra K L] :
    MulDistribMulAction (Gal(L / K)) Lˣ where
  smul σ x := Units.mapEquiv σ.toMulEquiv x
  one_smul := by
    intro x
    ext
    rfl
  mul_smul := by
    intro σ τ x
    ext
    rfl
  smul_mul := by
    intro σ x y
    exact map_mul (Units.mapEquiv σ.toMulEquiv) x y
  smul_one := by
    intro σ
    exact map_one (Units.mapEquiv σ.toMulEquiv)

/-- States the theorem `galoisGroupFieldUnitsMulDistribMulAction_smul`. -/
@[simp]
theorem galoisGroupFieldUnitsMulDistribMulAction_smul
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (σ : Gal(L / K)) (x : Lˣ) :
    letI := galoisGroupFieldUnitsMulDistribMulAction K L
    σ • x = Units.mapEquiv σ.toMulEquiv x :=
  rfl

/-- The actual `Gal(L / K)` action on integer units.  Its source is the
restriction of the field automorphism to the integral closure `𝒪[L]`. -/
@[implicit_reducible]
def galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    MulDistribMulAction (Gal(L / K)) 𝒪[L]ˣ where
  smul σ x := Units.mapEquiv
    (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).toMulEquiv x
  one_smul := by
    intro x
    ext
    rfl
  mul_smul := by
    intro σ τ x
    ext
    rfl
  smul_mul := by
    intro σ x y
    exact map_mul
      (Units.mapEquiv
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).toMulEquiv) x y
  smul_one := by
    intro σ
    exact map_one
      (Units.mapEquiv
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).toMulEquiv)

/-- States the theorem `galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure_smul`. -/
@[simp]
theorem galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure_smul
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (σ : Gal(L / K)) (x : 𝒪[L]ˣ) :
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    σ • x = Units.mapEquiv
      (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).toMulEquiv x :=
  rfl

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_AbsoluteValue_Completeness
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial
attribute [-simp] _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- The nontrivial-valuation convention excludes the trivial valuation; this supplies the
corresponding mathlib `NontriviallyNormedField` instance for `WithAbs v`. -/
@[reducible]
def withAbsNontriviallyNormedField
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (hv : v.IsNontrivial) :
    NontriviallyNormedField (WithAbs v) :=
  NontriviallyNormedField.ofNormNeOne
    (by
      rcases hv with ⟨x, hx0, hx1⟩
      refine ⟨(WithAbs.equiv v).symm x, ?_, ?_⟩
      · intro hx
        apply hx0
        simpa using congrArg (WithAbs.equiv v) hx
      · simpa [WithAbs.norm_eq_apply_ofAbs] using hx1)

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Henselian_Factorization_Basic
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial
attribute [-simp] _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- Polynomial coefficient maps distribute over the Bezout expression used in
the Hensel input. -/
theorem henselFactorization_map_mul_add_mul
    {R k : Type*} [CommSemiring R] [CommSemiring k] (φ : R →+* k)
    (a b g h : R[X]) :
    (a * g + b * h).map φ = a.map φ * g.map φ + b.map φ * h.map φ := by
  simp [Polynomial.map_add, Polynomial.map_mul]

/-- lift input: a residue polynomial can be lifted along a
surjective coefficient map with the same polynomial degree. -/
theorem henselFactorization_exists_polynomial_lift_degree_eq
    {R k : Type*} [CommRing R] [CommRing k] (φ : R →+* k)
    (hφ : Function.Surjective φ) (fbar : k[X]) :
    ∃ f : R[X], f.map φ = fbar ∧ f.degree = fbar.degree := by
  have hlifts : fbar ∈ Polynomial.lifts φ := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact hφ (fbar.coeff n)
  rcases Polynomial.exists_degree_eq_of_mem_lifts hlifts with
    ⟨f, hmap, hdegree⟩
  exact ⟨f, hmap, hdegree⟩

/-- lift input: a residue polynomial can be lifted along a
surjective coefficient map with the same natural degree. -/
theorem henselFactorization_exists_polynomial_lift_natDegree_eq
    {R k : Type*} [CommRing R] [CommRing k] (φ : R →+* k)
    (hφ : Function.Surjective φ) (fbar : k[X]) :
    ∃ f : R[X], f.map φ = fbar ∧ f.natDegree = fbar.natDegree := by
  rcases henselFactorization_exists_polynomial_lift_degree_eq φ hφ fbar with
    ⟨f, hmap, hdegree⟩
  exact ⟨f, hmap, Polynomial.natDegree_eq_of_degree_eq hdegree⟩

/-- Bezout lift input: if the two residual factors are
coprime, then after choosing arbitrary lifts `g0`, `h0`, the Bezout
coefficients can also be lifted so that `a g0 + b h0` reduces to `1`. -/
theorem henselFactorization_exists_bezout_lifts
    {R k : Type*} [CommRing R] [CommRing k] (φ : R →+* k)
    (hφ : Function.Surjective φ)
    {gbar hbar : k[X]} (hcop : IsCoprime gbar hbar)
    {g0 h0 : R[X]} (hg0 : g0.map φ = gbar) (hh0 : h0.map φ = hbar) :
    ∃ a b : R[X], (a * g0 + b * h0).map φ = 1 := by
  rcases hcop with ⟨abar, bbar, hbezout⟩
  rcases henselFactorization_exists_polynomial_lift_degree_eq φ hφ abar with
    ⟨a, ha, _⟩
  rcases henselFactorization_exists_polynomial_lift_degree_eq φ hφ bbar with
    ⟨b, hb, _⟩
  refine ⟨a, b, ?_⟩
  calc
    (a * g0 + b * h0).map φ =
        a.map φ * g0.map φ + b.map φ * h0.map φ := by
      exact henselFactorization_map_mul_add_mul φ a b g0 h0
    _ = abar * gbar + bbar * hbar := by
      rw [ha, hb, hg0, hh0]
    _ = 1 := hbezout

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Henselian_Factorization_AdicLimits
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- assemble finitely many coefficient limits into the
polynomial supported in degrees at most `N`. -/
def henselFactorization_polyOfLimitCoeffs
    {R : Type*} [Semiring R] (N : ℕ) (c : ℕ → R) : R[X] :=
  Finset.sum (Finset.range (N + 1)) fun i => Polynomial.monomial i (c i)

/-- coefficients of the finite polynomial assembled from
coefficient limits, inside the cutoff. -/
theorem henselFactorization_polyOfLimitCoeffs_coeff_of_le
    {R : Type*} [Semiring R] {N n : ℕ} (c : ℕ → R) (hn : n ≤ N) :
    (henselFactorization_polyOfLimitCoeffs N c).coeff n = c n := by
  classical
  unfold henselFactorization_polyOfLimitCoeffs
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single n]
  · simp
  · intro b _hb hbn
    simp [Polynomial.coeff_monomial, hbn]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr (Nat.lt_succ_of_le hn)))

/-- coefficients of the finite polynomial assembled from
coefficient limits vanish above the cutoff. -/
theorem henselFactorization_polyOfLimitCoeffs_coeff_eq_zero_of_lt
    {R : Type*} [Semiring R] {N n : ℕ} (c : ℕ → R) (hn : N < n) :
    (henselFactorization_polyOfLimitCoeffs N c).coeff n = 0 := by
  classical
  unfold henselFactorization_polyOfLimitCoeffs
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero ?_
  intro b hb
  have hbn : b ≠ n := by
    intro hbn
    have hn_le : n ≤ N := Nat.lt_succ_iff.mp (by simpa [hbn] using hb)
    exact (Nat.not_lt_of_ge hn_le) hn
  simp [Polynomial.coeff_monomial, hbn]

/-- the polynomial assembled from finitely many coefficient
limits has the stated degree bound. -/
theorem henselFactorization_polyOfLimitCoeffs_natDegree_le
    {R : Type*} [Semiring R] (N : ℕ) (c : ℕ → R) :
    (henselFactorization_polyOfLimitCoeffs N c).natDegree ≤ N := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  exact henselFactorization_polyOfLimitCoeffs_coeff_eq_zero_of_lt (c := c) hn

/-- if all coefficients of the left factor lie in an ideal,
then all coefficients of its product with any polynomial lie in the same
ideal. -/
theorem henselFactorization_mul_left_coeff_mem_ideal
    {R : Type*} [CommRing R] (I : Ideal R) {A B : R[X]}
    (hA : ∀ i : ℕ, A.coeff i ∈ I) :
    ∀ i : ℕ, (A * B).coeff i ∈ I := by
  intro i
  rw [Polynomial.coeff_mul]
  exact I.sum_mem fun p _hp => I.mul_mem_right _ (hA p.1)

/-- if all coefficients of the right factor lie in an ideal,
then all coefficients of its product with any polynomial lie in the same
ideal. -/
theorem henselFactorization_mul_right_coeff_mem_ideal
    {R : Type*} [CommRing R] (I : Ideal R) {A B : R[X]}
    (hB : ∀ i : ℕ, B.coeff i ∈ I) :
    ∀ i : ℕ, (A * B).coeff i ∈ I := by
  intro i
  rw [Polynomial.coeff_mul]
  exact I.sum_mem fun p _hp => I.mul_mem_left _ (hB p.2)

/-- coefficientwise convergence is preserved by multiplying
two polynomial approximants. -/
theorem henselFactorization_mul_sub_mul_coeff_mem_of_coeff_mem
    {R : Type*} [CommRing R] (I : Ideal R) {A A' B B' : R[X]}
    (hA : ∀ i : ℕ, (A - A').coeff i ∈ I)
    (hB : ∀ i : ℕ, (B - B').coeff i ∈ I) :
    ∀ i : ℕ, (A * B - A' * B').coeff i ∈ I := by
  have hdecomp : A * B - A' * B' = (A - A') * B + A' * (B - B') := by
    ring
  intro i
  rw [hdecomp, Polynomial.coeff_add]
  exact I.add_mem
    (henselFactorization_mul_left_coeff_mem_ideal (I := I) hA i)
    (henselFactorization_mul_right_coeff_mem_ideal (I := I) hB i)

/-- combine the product convergence with the residual error
estimate at one adic level. -/
theorem henselFactorization_limit_factor_coeff_mem_of_approximants
    {R : Type*} [CommRing R] (I : Ideal R)
    {f G H Gn Hn : R[X]}
    (herr : ∀ i : ℕ, (f - Gn * Hn).coeff i ∈ I)
    (hG : ∀ i : ℕ, (Gn - G).coeff i ∈ I)
    (hH : ∀ i : ℕ, (Hn - H).coeff i ∈ I) :
    ∀ i : ℕ, (f - G * H).coeff i ∈ I := by
  have hdecomp : f - G * H = (f - Gn * Hn) + (Gn * Hn - G * H) := by
    ring
  intro i
  rw [hdecomp, Polynomial.coeff_add]
  exact I.add_mem (herr i)
    (henselFactorization_mul_sub_mul_coeff_mem_of_coeff_mem
      (I := I) hG hH i)

/-- a polynomial whose coefficients lie in every adic power is
zero in a Hausdorff coefficient ring. -/
theorem henselFactorization_polynomial_eq_zero_of_coeff_mem_all_powers
    {R : Type*} [CommRing R] (I : Ideal R) [IsHausdorff I R]
    {P : R[X]}
    (hP : ∀ n i : ℕ, P.coeff i ∈ I ^ n) :
    P = 0 := by
  ext i
  apply IsHausdorff.haus (show IsHausdorff I R from inferInstance)
  intro n
  have hmem : P.coeff i - 0 ∈ I ^ n := by
    simpa using hP n i
  simpa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using hmem

/-- if the approximating factorization and both factors
converge coefficientwise at every adic level, then the limiting polynomials
factor `f`. -/
theorem henselFactorization_limit_factor_eq_of_approximants
    {R : Type*} [CommRing R] (I : Ideal R) [IsHausdorff I R]
    {f G H : R[X]} {Gseq Hseq : ℕ → R[X]}
    (herr : ∀ n i : ℕ, (f - Gseq n * Hseq n).coeff i ∈ I ^ n)
    (hG : ∀ n i : ℕ, (Gseq n - G).coeff i ∈ I ^ n)
    (hH : ∀ n i : ℕ, (Hseq n - H).coeff i ∈ I ^ n) :
    f = G * H := by
  have hzero : f - G * H = 0 := by
    apply henselFactorization_polynomial_eq_zero_of_coeff_mem_all_powers (I := I)
    intro n i
    exact henselFactorization_limit_factor_coeff_mem_of_approximants
      (I := I ^ n) (herr n) (hG n) (hH n) i
  exact sub_eq_zero.mp hzero

/-- the limit of approximants preserving a fixed residual
class preserves that residual class.  Only the first adic level is needed. -/
theorem henselFactorization_limit_reduction_of_approx_reduction
    {R : Type*} [CommRing R] (I : Ideal R)
    {P P0 : R[X]} {Pseq : ℕ → R[X]}
    (hlim : ∀ n i : ℕ, (Pseq n - P).coeff i ∈ I ^ n)
    (hred : ∀ n i : ℕ, (Pseq n - P0).coeff i ∈ I) :
    ∀ i : ℕ, (P - P0).coeff i ∈ I := by
  intro i
  have hlim1 : (Pseq 1 - P).coeff i ∈ I := by
    simpa using hlim 1 i
  have hred1 : (Pseq 1 - P0).coeff i ∈ I := hred 1 i
  have hdecomp : P - P0 = -(Pseq 1 - P) + (Pseq 1 - P0) := by
    ring
  rw [hdecomp, Polynomial.coeff_add, Polynomial.coeff_neg]
  exact I.add_mem (I.neg_mem hlim1) hred1

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Henselian_Factorization_ErrorPowers
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- a displayed `C(π^n)` factor gives coefficientwise
membership in the principal ideal `(π^n)`. -/
theorem henselFactorization_coeff_mem_span_singleton_pow_of_factor
    {R : Type*} [CommRing R] {π : R} {n : ℕ} {P Q : R[X]}
    (hfactor : P = Polynomial.C (π ^ n) * Q) :
    ∀ i : ℕ, P.coeff i ∈ Ideal.span ({π ^ n} : Set R) := by
  intro i
  rw [hfactor, Polynomial.coeff_C_mul]
  refine Ideal.mem_span_singleton'.mpr ⟨Q.coeff i, ?_⟩
  ring

/-- a displayed `C(π^n)` factor gives coefficientwise
membership in the `n`-th power of the principal ideal `(π)`. -/
theorem henselFactorization_coeff_mem_span_pow_of_factor
    {R : Type*} [CommRing R] {π : R} {n : ℕ} {P Q : R[X]}
    (hfactor : P = Polynomial.C (π ^ n) * Q) :
    ∀ i : ℕ, P.coeff i ∈ Ideal.span ({π} : Set R) ^ n := by
  intro i
  rw [Ideal.span_singleton_pow]
  exact henselFactorization_coeff_mem_span_singleton_pow_of_factor
    (π := π) (n := n) hfactor i


end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Henselian_Factorization_CoefficientMinimum
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial
attribute [-simp] _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- finite divisibility minimum in a valuation ring: every
nonempty finite set has an element that divides all elements of the set. -/
theorem henselFactorization_exists_mem_finset_dvd_all
    {R : Type*} [Monoid R] [PreValuationRing R] {s : Finset R}
    (hs : s.Nonempty) :
    ∃ π ∈ s, ∀ x ∈ s, π ∣ x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rcases hs with ⟨x, hx⟩
      simp at hx
  | @insert a s ha ih =>
      by_cases hs' : s.Nonempty
      · rcases ih hs' with ⟨π, hπs, hπall⟩
        rcases ValuationRing.dvd_total π a with hπa | haπ
        · refine ⟨π, Finset.mem_insert_of_mem hπs, ?_⟩
          intro x hx
          rw [Finset.mem_insert] at hx
          rcases hx with rfl | hxs
          · exact hπa
          · exact hπall x hxs
        · refine ⟨a, Finset.mem_insert_self a s, ?_⟩
          intro x hx
          rw [Finset.mem_insert] at hx
          rcases hx with rfl | hxs
          · exact dvd_refl _
          · exact dvd_trans haπ (hπall x hxs)
      · refine ⟨a, Finset.mem_insert_self a s, ?_⟩
        intro x hx
        rw [Finset.mem_insert] at hx
        rcases hx with rfl | hxs
        · exact dvd_refl _
        · exact False.elim (hs' ⟨x, hxs⟩)

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Henselian_Factorization_DivisionBounds
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# degree bounds for the division remainder

This file supplies the degree estimate for the remainder in the coefficientwise Hensel
correction step.  It removes the later need to assume separately that the
residue of the remainder has small degree.
-/

noncomputable section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- the remainder estimate before reducing
coefficients. -/
theorem henselFactorization_remainder_natDegree_le_of_degree_lt
    {R : Type*} [CommRing R] {g0 p : R[X]} {m : ℕ}
    (hg0nat : g0.natDegree = m) (hpdeg : p.degree < g0.degree) :
    p.natDegree ≤ m := by
  apply Polynomial.natDegree_le_of_degree_le
  have hlt : p.degree < (m : WithBot ℕ) := by
    calc
      p.degree < g0.degree := hpdeg
      _ ≤ (g0.natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
      _ = (m : WithBot ℕ) := by rw [hg0nat]
  exact hlt.le


end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Henselian_Factorization_DegreeBounds
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial
attribute [-simp] _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- a natural-degree bound survives reduction of
coefficients. -/
theorem henselFactorization_map_natDegree_le_of_natDegree_le
    {R k : Type*} [CommRing R] [CommRing k] (φ : R →+* k)
    {P : R[X]} {d : ℕ} (hP : P.natDegree ≤ d) :
    (P.map φ).natDegree ≤ d :=
  Polynomial.natDegree_map_le.trans hP

/-- exact degree is recovered from a bounded lift whose
reduction has nonzero leading coefficient in the prescribed degree. -/
theorem henselFactorization_natDegree_eq_of_residue_eq_of_le
    {R : Type*} [CommRing R] [IsLocalRing R]
    {P : R[X]} {gbar : (IsLocalRing.ResidueField R)[X]} {m : ℕ}
    (hP : P.natDegree ≤ m)
    (hmap : P.map (IsLocalRing.residue R) = gbar)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0) :
    P.natDegree = m := by
  refine le_antisymm hP ?_
  have hcoeff_map :=
    congrArg (fun Q : (IsLocalRing.ResidueField R)[X] => Q.coeff m) hmap
  have hcoeff :
      IsLocalRing.residue R (P.coeff m) = gbar.coeff m := by
    simpa [Polynomial.coeff_map] using hcoeff_map
  have hgcoeff : gbar.coeff m ≠ 0 := by
    simpa [Polynomial.leadingCoeff, hgbar_nat] using hglead
  have hPcoeff : P.coeff m ≠ 0 := by
    intro hzero
    apply hgcoeff
    rw [← hcoeff, hzero, map_zero]
  exact Polynomial.le_natDegree_of_ne_zero hPcoeff

/-- the stated degree bound for the second residual factor:
if `fbar = gbar*hbar`, `deg fbar≤d`, and `deg gbar=m` with `gbar≠0`, then
`deg hbar≤d-m`. -/
theorem henselFactorization_residual_right_natDegree_le
    {k : Type*} [Field k] {fbar gbar hbar : k[X]} {m d : ℕ}
    (hfbar : fbar = gbar * hbar)
    (hf : fbar.natDegree ≤ d)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0) :
    hbar.natDegree ≤ d - m := by
  by_cases hh : hbar = 0
  · simp [hh]
  · have hg : gbar ≠ 0 := Polynomial.leadingCoeff_ne_zero.mp hglead
    have hprod : (gbar * hbar).natDegree ≤ d := by
      simpa [hfbar] using hf
    have hsum : m + hbar.natDegree ≤ d := by
      simpa [hgbar_nat, Polynomial.natDegree_mul hg hh] using hprod
    exact Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using hsum)

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Henselian_Factorization_Assembly
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial
attribute [-simp] _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# explicit valuation-ring Hensel statement

This file connects the chosen finite-minimum coefficient to
the displayed-factor complete-limit theorem.
-/

noncomputable section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- Degree-controlled polynomial lifts of a nonzero residual
factorization.  This is the algebraic preparation shared by the maximal-ideal
and principal-adic forms of Hensel's lemma. -/
theorem henselFactorization_exists_degreeControlledLifts_of_residual_factorization
    {R : Type*} [CommRing R] [IsLocalRing R]
    {f : R[X]} {gbar hbar : (IsLocalRing.ResidueField R)[X]}
    (hprim : f.map (IsLocalRing.residue R) ≠ 0)
    (hfbar : f.map (IsLocalRing.residue R) = gbar * hbar) :
    ∃ g0 h0 : R[X],
      g0.map (IsLocalRing.residue R) = gbar ∧
        h0.map (IsLocalRing.residue R) = hbar ∧
          g0.natDegree = gbar.natDegree ∧
            h0.natDegree ≤ f.natDegree - gbar.natDegree ∧
              gbar.natDegree ≤ f.natDegree ∧
                gbar.leadingCoeff ≠ 0 := by
  have hfmap :
      (f.map (IsLocalRing.residue R)).natDegree ≤ f.natDegree :=
    henselFactorization_map_natDegree_le_of_natDegree_le
      (IsLocalRing.residue R) le_rfl
  have hgbar_ne : gbar ≠ 0 := by
    intro hgbar
    apply hprim
    rw [hfbar, hgbar, zero_mul]
  have hhbar_ne : hbar ≠ 0 := by
    intro hhbar
    apply hprim
    rw [hfbar, hhbar, mul_zero]
  have hglead : gbar.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hgbar_ne
  have hprod_degree :
      (gbar * hbar).natDegree ≤ f.natDegree := by
    simpa [hfbar] using hfmap
  have hsum :
      gbar.natDegree + hbar.natDegree ≤ f.natDegree := by
    simpa [Polynomial.natDegree_mul hgbar_ne hhbar_ne] using hprod_degree
  have hmd : gbar.natDegree ≤ f.natDegree :=
    (Nat.le_add_right gbar.natDegree hbar.natDegree).trans hsum
  have hhbar_deg :
      hbar.natDegree ≤ f.natDegree - gbar.natDegree :=
    henselFactorization_residual_right_natDegree_le
      (fbar := f.map (IsLocalRing.residue R))
      (gbar := gbar) (hbar := hbar)
      (m := gbar.natDegree) (d := f.natDegree)
      hfbar hfmap rfl hglead
  rcases henselFactorization_exists_polynomial_lift_natDegree_eq
      (IsLocalRing.residue R) IsLocalRing.residue_surjective gbar with
    ⟨g0, hg0map, hg0nat⟩
  rcases henselFactorization_exists_polynomial_lift_natDegree_eq
      (IsLocalRing.residue R) IsLocalRing.residue_surjective hbar with
    ⟨h0, hh0map, hh0nat⟩
  refine ⟨g0, h0, hg0map, hh0map, hg0nat, ?_, hmd, hglead⟩
  simpa [hh0nat] using hhbar_deg

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_NormalBasisLattice
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-! Provides the public normal-basis lattice declarations used in Herbrand computations. -/

namespace CyclicCohomology

open LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel
open Filter

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

variable [ValuativeRel K]

/-- The classical normal-basis lattice candidate `M`: the `𝒪_K`-span of the
normal-basis orbit.  Bounds comparing this lattice with `𝒪_L` are deliberately
made explicit in the lattice-comparison theorems below. -/
def chosenNormalBasisIntegerLattice : Submodule 𝒪[K] L :=
  Submodule.span 𝒪[K]
    (Set.range (fun σ : Gal(L / K) =>
      σ (IsGalois.normalBasis K L (1 : Gal(L / K)))))

/-- Every normal-basis vector lies in the `𝒪_K`-span lattice `M`. -/
theorem normalBasis_mem_integerLattice (σ : Gal(L / K)) :
    IsGalois.normalBasis K L σ ∈ chosenNormalBasisIntegerLattice K L := by
  rw [IsGalois.normalBasis_apply]
  exact Submodule.subset_span (Set.mem_range_self σ)

/-- The normal-basis lattice `M` is stable under the actual `Gal(L / K)`
action. -/
theorem galoisGroup_apply_mem_chosenNormalBasisIntegerLattice
    (τ : Gal(L / K)) {x : L}
    (hx : x ∈ chosenNormalBasisIntegerLattice K L) :
    τ x ∈ chosenNormalBasisIntegerLattice K L := by
  refine Submodule.span_induction
    (p := fun x _ => τ x ∈ chosenNormalBasisIntegerLattice K L)
    ?hgen ?hzero ?hadd ?hsmul hx
  · intro x hx
    rcases hx with ⟨σ, rfl⟩
    have hτ :
        τ (σ (IsGalois.normalBasis K L (1 : Gal(L / K)))) =
          IsGalois.normalBasis K L (τ * σ) := by
      rw [IsGalois.normalBasis_apply (K := K) (L := L) (τ * σ)]
      rfl
    rw [hτ]
    exact normalBasis_mem_integerLattice (K := K) (L := L) (τ * σ)
  · simp
  · intro x y _ _ hx hy
    simpa using
      (chosenNormalBasisIntegerLattice K L).add_mem hx hy
  · intro a x _ hx
    have ha : τ (algebraMap 𝒪[K] L a) = algebraMap 𝒪[K] L a := by
      change τ (algebraMap K L (a : K)) = algebraMap K L (a : K)
      exact τ.commutes (a : K)
    simpa [Algebra.smul_def, ha, map_mul] using
      (chosenNormalBasisIntegerLattice K L).smul_mem a hx

/-- Multiplication by a base integer-ring element, as an `𝒪_K`-linear endomorphism
of the extension field. -/
def baseIntegerScalarMulLinearMap (a : 𝒪[K]) : L →ₗ[𝒪[K]] L where
  toFun x := algebraMap 𝒪[K] L a * x
  map_add' := by
    intro x y
    rw [mul_add]
  map_smul' := by
    intro r x
    simp [Algebra.smul_def, mul_comm, mul_left_comm]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Evaluates the linear map given by scalar multiplication from the base integer ring. -/
@[simp]
theorem baseIntegerScalarMulLinearMap_apply (a : 𝒪[K]) (x : L) :
    baseIntegerScalarMulLinearMap K L a x = algebraMap 𝒪[K] L a * x :=
  rfl

/-- The image of an `𝒪_K`-submodule under multiplication by a base
integer-ring element. -/
def baseIntegerScalarMulSubmodule (a : 𝒪[K]) (N : Submodule 𝒪[K] L) :
    Submodule 𝒪[K] L :=
  N.map (baseIntegerScalarMulLinearMap K L a)

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- Multiplication of an `𝒪_K`-submodule by a power of the chosen base
uniformizer.  The name deliberately records the construction's dependence on
`chosenIntegerRingUniformizer K`; no uniformizer-independence result is part of
this API.  This is the concrete shape of the `π_K^n` lattices used in the local
class-field-axiom calculation. -/
def chosenBaseUniformizerPowSubmodule (n : Nat) (N : Submodule 𝒪[K] L) :
    Submodule 𝒪[K] L :=
  baseIntegerScalarMulSubmodule K L (chosenIntegerRingUniformizer K ^ n) N

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Characterizes membership in a chosen uniformizer-power submodule. -/
@[simp]
theorem mem_chosenBaseUniformizerPowSubmodule_iff
    (n : Nat) (N : Submodule 𝒪[K] L) (x : L) :
    x ∈ chosenBaseUniformizerPowSubmodule K L n N ↔
      ∃ y : L, y ∈ N ∧
        algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * y = x :=
  Iff.rfl

variable [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

/-- The actual carrier of the classical auxiliary principal-unit lattice
`V^n = 1 + π_K^n M`, viewed as a set of units of `𝒪_L`.

This set becomes a subgroup once inverse closure is supplied by the complete
geometric-series argument. -/
def chosenNormalBasisPrincipalUnitSet (n : Nat) : Set 𝒪[L]ˣ :=
  {u | ((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) ∈
    chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)}

omit [Valuation.HasExtension
  (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- Characterizes membership in the principal-unit set arising from a normal-basis lattice. -/
@[simp]
theorem mem_chosenNormalBasisPrincipalUnitSet_iff (n : Nat) (u : 𝒪[L]ˣ) :
    u ∈ chosenNormalBasisPrincipalUnitSet K L n ↔
      ((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) ∈
        chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) :=
  Iff.rfl

end
end CyclicCohomology

universe u

namespace CyclicCohomology

open LocalFieldTheory

noncomputable section

open scoped ValuativeRel
open Filter

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

/-! ### Additive quotient boundary -/

/-- The denominator submodule `π_K^(n+1)M`, viewed inside `π_K^nM`. -/
def chosenNormalBasisLatticeSuccSubmodule (n : Nat) :
    Submodule 𝒪[K]
      (chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) :=
  (chosenBaseUniformizerPowSubmodule K L (n + 1)
    (chosenNormalBasisIntegerLattice K L)).submoduleOf
      (chosenBaseUniformizerPowSubmodule K L n
        (chosenNormalBasisIntegerLattice K L))

/-- The additive quotient `π_K^nM / π_K^(n+1)M` used in the local class-field calculation. -/
def chosenNormalBasisLatticeSuccQuot (n : Nat) : Type u :=
  (chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) ⧸
    chosenNormalBasisLatticeSuccSubmodule K L n

/-- A successive quotient of normal-basis lattices is an additive commutative group. -/
instance chosenNormalBasisLatticeSuccQuotAddCommGroup (n : Nat) :
    AddCommGroup (chosenNormalBasisLatticeSuccQuot K L n) := by
  change AddCommGroup
    ((chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) ⧸
      chosenNormalBasisLatticeSuccSubmodule K L n)
  infer_instance

/-- A successive normal-basis lattice quotient carries the natural residue-field
module structure. -/
instance chosenNormalBasisLatticeSuccQuotModule (n : Nat) :
    Module 𝒪[K] (chosenNormalBasisLatticeSuccQuot K L n) := by
  change Module 𝒪[K]
    ((chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) ⧸
      chosenNormalBasisLatticeSuccSubmodule K L n)
  infer_instance

/-- Explicit access to the concrete submodule quotient implementing the
chosen normal-basis lattice graded piece. -/
def chosenNormalBasisLatticeSuccQuotConcreteLinearEquiv (n : Nat) :
    chosenNormalBasisLatticeSuccQuot K L n ≃ₗ[𝒪[K]]
      ((chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) ⧸
        chosenNormalBasisLatticeSuccSubmodule K L n) := by
  change
    ((chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) ⧸
        chosenNormalBasisLatticeSuccSubmodule K L n) ≃ₗ[𝒪[K]]
      ((chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) ⧸
        chosenNormalBasisLatticeSuccSubmodule K L n)
  exact LinearEquiv.refl 𝒪[K] _

omit [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- Characterizes membership in the next normal-basis lattice submodule. -/
@[simp]
theorem mem_chosenNormalBasisLatticeSuccSubmodule_iff (n : Nat)
    (x : chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) :
    x ∈ chosenNormalBasisLatticeSuccSubmodule K L n ↔
      (x : L) ∈ chosenBaseUniformizerPowSubmodule K L (n + 1)
        (chosenNormalBasisIntegerLattice K L) :=
  Iff.rfl

/-- The quotient map `π_K^nM -> π_K^nM / π_K^(n+1)M`. -/
def chosenNormalBasisLatticeSuccQuotMk (n : Nat) :
    chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →ₗ[𝒪[K]]
      chosenNormalBasisLatticeSuccQuot K L n := by
  change
    chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →ₗ[𝒪[K]]
      ((chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) ⧸
        chosenNormalBasisLatticeSuccSubmodule K L n)
  exact (chosenNormalBasisLatticeSuccSubmodule K L n).mkQ

omit [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- The concrete linear equivalence sends a lattice element to its canonical quotient class. -/
@[simp]
theorem chosenNormalBasisLatticeSuccQuotConcreteLinearEquiv_mk (n : Nat)
    (x : chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) :
    chosenNormalBasisLatticeSuccQuotConcreteLinearEquiv K L n
        (chosenNormalBasisLatticeSuccQuotMk K L n x) =
      Submodule.Quotient.mk x :=
  rfl

/-- Descend a representative-level function constant modulo the next chosen
normal-basis lattice. -/
def chosenNormalBasisLatticeSuccQuotLift
    {P : Sort*} (n : Nat)
    (f :
      chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) → P)
    (h : ∀ x y, x - y ∈ chosenNormalBasisLatticeSuccSubmodule K L n →
      f x = f y) :
    chosenNormalBasisLatticeSuccQuot K L n → P := by
  change
    ((chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ⧸
      chosenNormalBasisLatticeSuccSubmodule K L n) → P)
  refine Quotient.lift f ?_
  intro x y hxy
  have hq :
      (Submodule.Quotient.mk x :
        (chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ⧸
          chosenNormalBasisLatticeSuccSubmodule K L n)) =
        Submodule.Quotient.mk y :=
    Quotient.sound hxy
  exact h x y
    ((Submodule.Quotient.eq
      (chosenNormalBasisLatticeSuccSubmodule K L n)).1 hq)

omit [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- The lifted map on a successive lattice quotient evaluates to the original
map on representatives. -/
@[simp] theorem chosenNormalBasisLatticeSuccQuotLift_mk
    {P : Sort*} (n : Nat)
    (f :
      chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) → P)
    (h : ∀ x y, x - y ∈ chosenNormalBasisLatticeSuccSubmodule K L n →
      f x = f y)
    (x : chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) :
    chosenNormalBasisLatticeSuccQuotLift K L n f h
        (chosenNormalBasisLatticeSuccQuotMk K L n x) = f x :=
  rfl

/-- Descend a linear map vanishing on the next chosen normal-basis lattice. -/
def chosenNormalBasisLatticeSuccQuotLinearLift
    {M : Type*} [AddCommGroup M] [Module 𝒪[K] M] (n : Nat)
    (f :
      chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)
        →ₗ[𝒪[K]] M)
    (h : chosenNormalBasisLatticeSuccSubmodule K L n ≤ f.ker) :
    chosenNormalBasisLatticeSuccQuot K L n →ₗ[𝒪[K]] M := by
  change
    (chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ⧸
      chosenNormalBasisLatticeSuccSubmodule K L n) →ₗ[𝒪[K]] M
  exact (chosenNormalBasisLatticeSuccSubmodule K L n).liftQ f h

omit [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- The lifted linear map agrees with the original linear map on quotient representatives. -/
@[simp] theorem chosenNormalBasisLatticeSuccQuotLinearLift_mk
    {M : Type*} [AddCommGroup M] [Module 𝒪[K] M] (n : Nat)
    (f :
      chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)
        →ₗ[𝒪[K]] M)
    (h : chosenNormalBasisLatticeSuccSubmodule K L n ≤ f.ker)
    (x : chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) :
    chosenNormalBasisLatticeSuccQuotLinearLift K L n f h
        (chosenNormalBasisLatticeSuccQuotMk K L n x) = f x :=
  rfl

omit [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- Two lattice representatives agree in the successive quotient exactly when
their difference lies at the next level. -/
@[simp]
theorem chosenNormalBasisLatticeSuccQuotMk_eq_iff (n : Nat)
    (x y :
      chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) :
    chosenNormalBasisLatticeSuccQuotMk K L n x =
        chosenNormalBasisLatticeSuccQuotMk K L n y ↔
      x - y ∈ chosenNormalBasisLatticeSuccSubmodule K L n := by
  change
    (Submodule.Quotient.mk x :
      (chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) ⧸
        chosenNormalBasisLatticeSuccSubmodule K L n) =
      Submodule.Quotient.mk y ↔ _
  exact Submodule.Quotient.eq (chosenNormalBasisLatticeSuccSubmodule K L n)

end
end CyclicCohomology
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_NormalBasisGaloisAction
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- Restrict a multiplicative group action to an invariant subgroup.  This
is the honest action used below on the standard subgroups `V^n`. -/
@[implicit_reducible]
def subgroupMulDistribMulActionOfStable
    (G : Type uG) (A : Type uA) [Group G] [CommGroup A]
    [MulDistribMulAction G A] (V : Subgroup A)
    (hstable : ∀ (g : G) (a : A), a ∈ V → g • a ∈ V) :
    MulDistribMulAction G V where
  smul g a := ⟨g • (a : A), hstable g a a.2⟩
  one_smul := by
    intro a
    apply Subtype.ext
    exact one_smul G (a : A)
  mul_smul := by
    intro g h a
    apply Subtype.ext
    exact mul_smul g h (a : A)
  smul_mul := by
    intro g a b
    apply Subtype.ext
    exact MulDistribMulAction.smul_mul g (a : A) (b : A)
  smul_one := by
    intro g
    apply Subtype.ext
    exact MulDistribMulAction.smul_one g

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- Every dilate `π_K^n M` of the normal-basis lattice is stable under the
actual action of `Gal(L / K)`. -/
theorem galoisGroup_apply_mem_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice
    (n : Nat) (sigma : Gal(L / K)) {x : L}
    (hx : x ∈ chosenBaseUniformizerPowSubmodule K L n
      (chosenNormalBasisIntegerLattice K L)) :
    sigma x ∈ chosenBaseUniformizerPowSubmodule K L n
      (chosenNormalBasisIntegerLattice K L) := by
  rcases (mem_chosenBaseUniformizerPowSubmodule_iff
      (K := K) (L := L) n (chosenNormalBasisIntegerLattice K L) x).1 hx with
    ⟨y, hy, rfl⟩
  refine (mem_chosenBaseUniformizerPowSubmodule_iff
      (K := K) (L := L) n (chosenNormalBasisIntegerLattice K L) _).2
    ⟨sigma y,
      galoisGroup_apply_mem_chosenNormalBasisIntegerLattice
        (K := K) (L := L) sigma hy, ?_⟩
  rw [map_mul]
  change
    algebraMap K L (((chosenIntegerRingUniformizer K ^ n : 𝒪[K]) : K)) *
        sigma y =
      sigma (algebraMap K L
        (((chosenIntegerRingUniformizer K ^ n : 𝒪[K]) : K))) * sigma y
  rw [sigma.commutes]

variable [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L]

/-- The actual integer-unit Galois action preserves each normal-basis
principal-unit set `V^n = 1 + π_K^n M`. -/
theorem galoisGroup_smul_mem_chosenNormalBasisPrincipalUnitSet
    (n : Nat) (sigma : Gal(L / K)) {a : 𝒪[L]ˣ}
    (ha : a ∈ chosenNormalBasisPrincipalUnitSet K L n) :
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    sigma • a ∈ chosenNormalBasisPrincipalUnitSet K L n := by
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  rw [mem_chosenNormalBasisPrincipalUnitSet_iff] at ha ⊢
  have hstable :=
    galoisGroup_apply_mem_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice
      (K := K) (L := L) n sigma ha
  simpa [galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure_smul,
    map_sub, map_one] using hstable

/-- The restricted actual Galois action on any subgroup whose carrier is
the standard `V^n`. -/
@[implicit_reducible]
def chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction
    (n : Nat) (V : Subgroup 𝒪[L]ˣ)
    (hV : (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n) :
    MulDistribMulAction (Gal(L / K)) V := by
  letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  exact subgroupMulDistribMulActionOfStable (Gal(L / K)) 𝒪[L]ˣ V
    (by
      intro sigma a ha
      change sigma • (a : 𝒪[L]ˣ) ∈ (V : Set 𝒪[L]ˣ)
      rw [hV]
      exact galoisGroup_smul_mem_chosenNormalBasisPrincipalUnitSet
        (K := K) (L := L) n sigma (hV ▸ ha))

/-- The induced Galois action on the principal-unit subgroup agrees with the ambient action. -/
@[simp]
theorem chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction_smul
    (n : Nat) (V : Subgroup 𝒪[L]ˣ)
    (hV : (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (sigma : Gal(L / K)) (a : V) :
    letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV
    ((sigma • a : V) : 𝒪[L]ˣ) =
      letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
      sigma • (a : 𝒪[L]ˣ) :=
  rfl

/-- Coercing the subgroup Tate norm gives the ambient product over the Galois group. -/
@[simp]
theorem chosenNormalBasisPrincipalUnitSubgroup_tateNorm_coe
    (n : Nat) (V : Subgroup 𝒪[L]ˣ)
    (hV : (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (a : V) :
    letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    ((tateNorm (Gal(L / K)) V a : V) : 𝒪[L]ˣ) =
      tateNorm (Gal(L / K)) 𝒪[L]ˣ (a : 𝒪[L]ˣ) := by
  let := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  unfold tateNorm
  change V.subtype (∏ g : Gal(L / K), g • a) =
    ∏ g : Gal(L / K), g • (a : 𝒪[L]ˣ)
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro g _hg
  rfl

/-- Coercion commutes with the `σ - 1` operation on the principal-unit subgroup. -/
@[simp]
theorem chosenNormalBasisPrincipalUnitSubgroup_sigmaMinusOne_coe
    (n : Nat) (V : Subgroup 𝒪[L]ˣ)
    (hV : (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (sigma : Gal(L / K)) (a : V) :
    letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    ((sigmaMinusOne (Gal(L / K)) V sigma a : V) : 𝒪[L]ˣ) =
      sigmaMinusOne (Gal(L / K)) 𝒪[L]ˣ sigma (a : 𝒪[L]ˣ) := by
  let := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  rfl

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_SeparableClosureEmbedding
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Embeddings into a separable closure

This file provides the common realization of a separable extension inside the
chosen separable closure of its base field.
-/

noncomputable section

namespace AlgebraicNumberTheory

universe u v

/-- Conjugation by a field equivalence is continuous on automorphism
groups equipped with the Krull topology. -/
theorem continuous_algEquiv_autCongr
    {F E E' : Type*}
    [Field F] [Field E] [Field E']
    [Algebra F E] [Algebra F E']
    (e : E ≃ₐ[F] E') :
    Continuous (AlgEquiv.autCongr e) := by
  apply continuous_of_continuousAt_one _
  rw [continuousAt_def]
  intro s hs
  rw [map_one, krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨M, hMfinite, hMs⟩ := hs
  let : FiniteDimensional F M := hMfinite
  let N : IntermediateField F E :=
    M.map e.symm.toAlgHom
  let : FiniteDimensional F N :=
    (M.equivMap e.symm.toAlgHom).toLinearEquiv.finiteDimensional
  rw [krullTopology_mem_nhds_one_iff]
  refine ⟨N, inferInstance, ?_⟩
  intro σ hσ
  apply hMs
  apply (IntermediateField.mem_fixingSubgroup_iff M
    (AlgEquiv.autCongr e σ)).2
  intro x hx
  have hxN : e.symm x ∈ N :=
    ⟨x, hx, rfl⟩
  have hfix :=
    (IntermediateField.mem_fixingSubgroup_iff N σ).1 hσ
      (e.symm x) hxN
  change e (σ (e.symm x)) = x
  rw [hfix, e.apply_symm_apply]

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
  [Algebra.IsSeparable K L]

/-- A chosen embedding of a separable extension into the separable closure of
its base field. -/
noncomputable def separableEmbeddingIntoSeparableClosure :
    L →ₐ[K] SeparableClosure K :=
  IsSepClosed.lift

variable (K : Type*) [Field K] [NumberField K]

/-- A chosen `ℚ`-embedding of a number field into mathlib's fixed
separable closure of `ℚ`. -/
noncomputable def numberFieldSeparableClosureEmbedding :
    K →ₐ[ℚ] SeparableClosure ℚ :=
  IsSepClosed.lift

/-- The actual copy of `K` cut out by the chosen embedding into
`SeparableClosure ℚ`. -/
def numberFieldInRationalSeparableClosure :
    IntermediateField ℚ (SeparableClosure ℚ) :=
  (numberFieldSeparableClosureEmbedding K).fieldRange

noncomputable instance
    numberFieldInRationalSeparableClosure_finiteDimensional :
    FiniteDimensional ℚ
      (numberFieldInRationalSeparableClosure K) :=
  ((numberFieldSeparableClosureEmbedding K).equivFieldRange.toLinearEquiv).finiteDimensional

noncomputable instance
    numberFieldInRationalSeparableClosure_numberField :
    NumberField (numberFieldInRationalSeparableClosure K) where
  to_charZero := inferInstance
  to_finiteDimensional := inferInstance

end AlgebraicNumberTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_ResidueGalois
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.LocalClassFieldTheory.galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- Actual integral-closure version of the residue-field automorphism induced by
a real Galois automorphism.

the local class-field calculation reduces the product of conjugates modulo the maximal ideal;
  this is the source map for that reduction, built from the already constructed
  integral-closure action on `𝒪[L]`. -/
def galoisGroupResidueFieldEquivOfIsIntegralClosure (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L / K)) :
    𝓀[L] ≃+* 𝓀[L] :=
  IsLocalRing.ResidueField.mapEquiv
    (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ)

/-- The residue-field action of a Galois automorphism sends a reduced integer to the reduction of
its conjugate. -/
@[simp]
theorem galoisGroupResidueFieldEquivOfIsIntegralClosure_residue (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L / K)) (x : 𝒪[L]) :
    galoisGroupResidueFieldEquivOfIsIntegralClosure K L σ
        (IsLocalRing.residue 𝒪[L] x) =
      IsLocalRing.residue 𝒪[L]
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ x) := by
  rfl

/-- The induced residue-field automorphism fixes the image of the base residue field. -/
theorem galoisGroupResidueFieldEquivOfIsIntegralClosure_algebraMap (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L / K)) (x : 𝓀[K]) :
    galoisGroupResidueFieldEquivOfIsIntegralClosure K L σ (algebraMap 𝓀[K] 𝓀[L] x) =
      algebraMap 𝓀[K] 𝓀[L] x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change galoisGroupResidueFieldEquivOfIsIntegralClosure K L σ
      (algebraMap 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[K] a)) =
    algebraMap 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[K] a)
  rw [residueField_algebraMap_residue K L a]
  rw [galoisGroupResidueFieldEquivOfIsIntegralClosure_residue]
  exact congrArg (fun z : 𝒪[L] => IsLocalRing.residue 𝒪[L] z)
    (galoisGroupIntegerRingEquivOfIsIntegralClosure_integerRingMap K L σ a)

/-- Actual integral-closure residue action as a `𝓀[K]`-algebra automorphism. -/
@[implicit_reducible]
def galoisGroupResidueAlgEquivOfIsIntegralClosure (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L / K)) :
    𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L] where
  __ := galoisGroupResidueFieldEquivOfIsIntegralClosure K L σ
  commutes' := galoisGroupResidueFieldEquivOfIsIntegralClosure_algebraMap K L σ

/-- Actual integral-closure residue action as a group homomorphism. -/
def galoisGroupResidueAlgEquivHomOfIsIntegralClosure (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    Gal(L / K) →* (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) where
  toFun := galoisGroupResidueAlgEquivOfIsIntegralClosure K L
  map_one' := by
    apply AlgEquiv.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  map_mul' := by
    intro σ τ
    apply AlgEquiv.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl


end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_FiniteUnramified
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false
/-!
# Finite unramified valued extensions

Develops the ideal, residue-field, Galois, trace, and norm consequences of a
finite valued extension with ramification index one and full residue degree.
-/

namespace LocalFieldTheory

noncomputable section

universe u

namespace IsNonarchimedeanLocalField

open scoped ValuativeRel

/-- A finite valuation extension is unramified at the actual valuation-ring
frontier when the ramification index of the maximal ideals is one.

This is the concrete source needed for residue-field automorphism comparisons. -/
class IsUnramifiedValuedExtension (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]] : Prop where
  /-- The maximal ideal of `𝒪[L]` has ramification index one over `𝒪[K]`. -/
  maximalIdeal_ramificationIdx_eq_one :
    (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] = 1

end IsNonarchimedeanLocalField

open scoped ValuativeRel
open _root_.LocalFieldTheory.IsNonarchimedeanLocalField
open Filter

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_LocalBlocks_Tensor
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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
open CyclicCohomology

universe u v

variable {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [IsGalois K L]

/-- The local tensor algebra occurring as the factor of
`𝔸_K ⊗[K] L` at `v`. -/
abbrev LocalTensorAlgebra (vK : AbsoluteValue K ℝ) :=
  vK.Completion ⊗[K] L

/-- Galois conjugation on the second factor of the local tensor algebra. -/
noncomputable def localTensorConjugation
    (vK : AbsoluteValue K ℝ) (σ : L ≃ₐ[K] L) :
    LocalTensorAlgebra (L := L) vK ≃ₐ[vK.Completion]
      LocalTensorAlgebra (L := L) vK := by
  let f :
      LocalTensorAlgebra (L := L) vK →ₐ[vK.Completion]
        LocalTensorAlgebra (L := L) vK :=
    Algebra.TensorProduct.map
      (AlgHom.id vK.Completion vK.Completion) σ.toAlgHom
  let g :
      LocalTensorAlgebra (L := L) vK →ₐ[vK.Completion]
        LocalTensorAlgebra (L := L) vK :=
    Algebra.TensorProduct.map
      (AlgHom.id vK.Completion vK.Completion) σ.symm.toAlgHom
  exact AlgEquiv.ofAlgHom f g
    (by ext x; simp [f, g])
    (by ext x; simp [f, g])

omit [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem localTensorConjugation_tmul
    (vK : AbsoluteValue K ℝ) (σ : L ≃ₐ[K] L)
    (b : vK.Completion) (x : L) :
    localTensorConjugation vK σ (b ⊗ₜ[K] x) =
      b ⊗ₜ[K] σ x :=
  rfl

section RightCosetCoordinates

universe uG uB

variable {G : Type uG} {B : Type uB}
    [Group G] [CommGroup B]
    (H : Subgroup G) [MulDistribMulAction H B]

/-- Right cosets `H \ G`, appropriate for the convention
`f (h * g) = h • f g` used by `InducedModule`. -/
abbrev InducedRightCosets :=
  Quotient (QuotientGroup.rightRel H)

/-- The element carrying the chosen representative of the right coset of
`g` to `g`. -/
noncomputable def rightCosetCoefficient (g : G) : H := by
  let q : InducedRightCosets H := Quotient.mk'' g
  refine ⟨g * (Quotient.out q)⁻¹, ?_⟩
  exact QuotientGroup.rightRel_apply.mp
    (Quotient.exact' (Quotient.out_eq' q))

end RightCosetCoordinates

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Relative_Support
attribute [-instance] _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Finite coefficient support for relative ideles

This file supplies the finite-support input for the actual scalar-extension model

`𝔸_K ⊗[K] L`.

Fixing the canonical chosen `K`-basis of `L`, every relative adele has
finitely many base-adele coefficients.  For a relative idele we take
the union of the nonintegral finite places of the coefficients of the
idele and of its inverse.  Outside this finite set both local tensor
components therefore lie in the lattice spanned by that basis over
the local valuation ring.

This produces the finite support from a basis lattice.  Passing from
that lattice to the product of local integer rings additionally requires
integral compatibility of the relative tensor decomposition.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section


universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- The finite index type of the canonical chosen `K`-basis of `L`. -/
abbrev RelativeAdeleBasisIndex :=
  Module.Free.ChooseBasisIndex K L

/-- The canonical chosen `K`-basis used to extract base-adele
coefficients. -/
noncomputable def relativeExtensionBasis :
    Module.Basis (RelativeAdeleBasisIndex (K := K) (L := L)) K L :=
  Module.Free.chooseBasis K L

/-- The set of places at which a base adele is not in the local
valuation ring is finite. -/
theorem finite_adeleNonIntegralPlaces
    (a : NumberField.AdeleRing (𝓞 K) K) :
    {w : HeightOneSpectrum (𝓞 K) |
      a.2 w ∉ w.adicCompletionIntegers K}.Finite :=
  Filter.eventually_cofinite.mp a.2.2

/-- The exceptional finite places at which a base adele is not in the
local valuation ring. -/
noncomputable def adeleNonIntegralPlaces
    (a : NumberField.AdeleRing (𝓞 K) K) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  (finite_adeleNonIntegralPlaces (K := K) a).toFinset

@[simp]
theorem mem_adeleNonIntegralPlaces_iff
    (a : NumberField.AdeleRing (𝓞 K) K)
    (w : HeightOneSpectrum (𝓞 K)) :
    w ∈ adeleNonIntegralPlaces (K := K) a ↔
      a.2 w ∉ w.adicCompletionIntegers K := by
  exact
    Set.Finite.mem_toFinset
      (finite_adeleNonIntegralPlaces (K := K) a)
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_IntegralTensorSupport_AbsoluteValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Integral lattices for the relative tensor basis

This file continues the finite-support construction for relative tensor
decompositions.  A single nonzero integer is chosen which carries every
vector of the fixed `K`-basis of `L` into `𝓞 L`.  Their
`𝓞 K`-span is a full lattice in `𝓞 L`.

The quotient of `𝓞 L` by this lattice is then proved directly to be a
finite torsion `𝓞 K`-module.  A nonzero element of its annihilator
therefore gives an actual finite set of bad height-one primes.  Outside
that set the scaled lattice generates the localization of `𝓞 L` over
the local ring of `K`.

Finally, a universe-polymorphic comparison between the absolute-value
and adic models of `K_v` carries this result through the canonical local tensor decomposition.
Away from the same bad set, the chosen basis-integral lattice maps into
the product of the completion valuation rings; applying the statement
to a unit and its inverse gives the actual product of local integer
unit groups needed in the finite-support decomposition.
-/

open scoped NumberField TensorProduct NNReal
open NumberField IsDedekindDomain

noncomputable section


open AlgebraicNumberTheory.Valuations

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- A nonarchimedean real absolute value, regarded as a valuation with
values in the nonnegative reals. -/
noncomputable def realAbsoluteValueValuation
    {F : Type*} [Field F]
    (vF : AbsoluteValue F ℝ)
    (hvF : IsNonarchimedean (vF : F → ℝ)) :
    Valuation F NNReal where
  toFun x := ⟨vF x, vF.nonneg x⟩
  map_one' := by
    ext
    exact vF.map_one
  map_zero' := by
    ext
    exact vF.map_zero
  map_mul' x y := by
    ext
    exact vF.map_mul x y
  map_add_le_max' x y := by
    change vF (x + y) ≤ max (vF x) (vF y)
    exact hvF x y

/-- The following two lemmas expose the valuation-subring interface used by later modules. -/

@[simp]
theorem realAbsoluteValueValuation_apply
    {F : Type*} [Field F]
    (vF : AbsoluteValue F ℝ)
    (hvF : IsNonarchimedean (vF : F → ℝ))
    (x : F) :
    ((realAbsoluteValueValuation vF hvF x : NNReal) : ℝ) =
      vF x :=
  rfl
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_IntegralTensorSupport_FinitePlaceCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Finite-place completion maps for relative tensor factors

This module compares the absolute-value and adic-completion models at finite
places and records how the resulting maps preserve norms and integrality.
-/

open scoped NumberField TensorProduct NNReal
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- The canonical dense map from the absolute-value model at a finite
place to mathlib's adic-completion model, universe-polymorphic in the
number field. -/
noncomputable def relativeFinitePlaceCompletionBaseMap
    (w : HeightOneSpectrum (𝓞 K)) :
    WithAbs (NumberField.HeightOneSpectrum.adicAbv K w) →+*
      w.adicCompletion K :=
  (FinitePlace.embedding w).comp
    (WithAbs.equiv
      (NumberField.HeightOneSpectrum.adicAbv K w)).toRingHom

/-- These lemmas record the canonical map and equivalence interfaces for the finite-place model. -/

@[simp]
theorem relativeFinitePlaceCompletionBaseMap_apply
    (w : HeightOneSpectrum (𝓞 K))
    (x : WithAbs
      (NumberField.HeightOneSpectrum.adicAbv K w)) :
    relativeFinitePlaceCompletionBaseMap w x =
      FinitePlace.embedding w
        (WithAbs.equiv
          (NumberField.HeightOneSpectrum.adicAbv K w) x) :=
  rfl

/-- The canonical finite-place map preserves norms. -/
theorem relativeFinitePlaceCompletionBaseMap_norm
    (w : HeightOneSpectrum (𝓞 K))
    (x : WithAbs
      (NumberField.HeightOneSpectrum.adicAbv K w)) :
    ‖relativeFinitePlaceCompletionBaseMap w x‖ = ‖x‖ := by
  rw [relativeFinitePlaceCompletionBaseMap_apply,
    FinitePlace.norm_embedding]
  rfl

/-- The canonical finite-place map is an isometry. -/
theorem relativeFinitePlaceCompletionBaseMap_isometry
    (w : HeightOneSpectrum (𝓞 K)) :
    Isometry (relativeFinitePlaceCompletionBaseMap w) :=
  AddMonoidHomClass.isometry_of_norm _
    (relativeFinitePlaceCompletionBaseMap_norm w)

/-- Extension of the preceding dense map to the completion. -/
noncomputable def relativeFinitePlaceCompletionRingHom
    (w : HeightOneSpectrum (𝓞 K)) :
    (NumberField.HeightOneSpectrum.adicAbv K w).Completion →+*
      w.adicCompletion K :=
  UniformSpace.Completion.extensionHom
    (relativeFinitePlaceCompletionBaseMap w)
    (relativeFinitePlaceCompletionBaseMap_isometry w).continuous

/-- Coercion, isometry, and surjectivity facts for the canonical ring homomorphism. -/

@[simp]
theorem relativeFinitePlaceCompletionRingHom_coe
    (w : HeightOneSpectrum (𝓞 K))
    (x : WithAbs
      (NumberField.HeightOneSpectrum.adicAbv K w)) :
    relativeFinitePlaceCompletionRingHom w
        (x :
          (NumberField.HeightOneSpectrum.adicAbv K w).Completion) =
      relativeFinitePlaceCompletionBaseMap w x :=
  UniformSpace.Completion.extensionHom_coe
    (relativeFinitePlaceCompletionBaseMap w)
    (relativeFinitePlaceCompletionBaseMap_isometry w).continuous x

/-- The canonical finite-place ring homomorphism is an isometry. -/
theorem relativeFinitePlaceCompletionRingHom_isometry
    (w : HeightOneSpectrum (𝓞 K)) :
    Isometry (relativeFinitePlaceCompletionRingHom w) :=
  (relativeFinitePlaceCompletionBaseMap_isometry w).completion_extension

/-- The canonical finite-place ring homomorphism is surjective. -/
theorem relativeFinitePlaceCompletionRingHom_surjective
    (w : HeightOneSpectrum (𝓞 K)) :
    Function.Surjective
      (relativeFinitePlaceCompletionRingHom w) := by
  let f := relativeFinitePlaceCompletionRingHom w
  have hrangeClosed : IsClosed (Set.range f) :=
    (relativeFinitePlaceCompletionRingHom_isometry w).isClosedEmbedding.isClosed_range
  have hdense :
      DenseRange (algebraMap K (w.adicCompletion K)) :=
    w.denseRange_algebraMap K
  have hrange :
      Set.range (algebraMap K (w.adicCompletion K)) ⊆
        Set.range f := by
    rintro _ ⟨x, rfl⟩
    let x' : WithAbs
        (NumberField.HeightOneSpectrum.adicAbv K w) :=
      (WithAbs.equiv
        (NumberField.HeightOneSpectrum.adicAbv K w)).symm x
    refine
      ⟨(x' :
          (NumberField.HeightOneSpectrum.adicAbv K w).Completion),
        ?_⟩
    rw [relativeFinitePlaceCompletionRingHom_coe]
    rfl
  intro x
  have hx :
      x ∈ closure
        (Set.range (algebraMap K (w.adicCompletion K))) := by
    rw [hdense.closure_range]
    trivial
  exact closure_minimal hrange hrangeClosed hx

/-- Canonical ring equivalence between the two models of `K_w`. -/
noncomputable def relativeFinitePlaceCompletionRingEquiv
    (w : HeightOneSpectrum (𝓞 K)) :
    (NumberField.HeightOneSpectrum.adicAbv K w).Completion ≃+*
      w.adicCompletion K :=
  RingEquiv.ofBijective
    (relativeFinitePlaceCompletionRingHom w)
    ⟨(relativeFinitePlaceCompletionRingHom_isometry w).injective,
      relativeFinitePlaceCompletionRingHom_surjective w⟩

/-- The same comparison as a `K`-algebra equivalence. -/
noncomputable def relativeFinitePlaceCompletionAlgEquiv
    (w : HeightOneSpectrum (𝓞 K)) :
    (NumberField.HeightOneSpectrum.adicAbv K w).Completion ≃ₐ[K]
      w.adicCompletion K where
  __ := relativeFinitePlaceCompletionRingEquiv w
  commutes' x := by
    change
      relativeFinitePlaceCompletionRingHom w
          (((WithAbs.equiv
            (NumberField.HeightOneSpectrum.adicAbv K w)).symm x :
              WithAbs
                (NumberField.HeightOneSpectrum.adicAbv K w)) :
            (NumberField.HeightOneSpectrum.adicAbv K w).Completion) =
        algebraMap K (w.adicCompletion K) x
    rw [relativeFinitePlaceCompletionRingHom_coe]
    rfl

/-- Base change in the first tensor factor, now without a universe
restriction. -/
noncomputable def relativeFinitePlaceLocalTensorAlgEquiv
    (w : HeightOneSpectrum (𝓞 K)) :
    (NumberField.HeightOneSpectrum.adicAbv K w).Completion ⊗[K] L
        ≃ₐ[K]
      w.adicCompletion K ⊗[K] L :=
  Algebra.TensorProduct.congr
    (relativeFinitePlaceCompletionAlgEquiv w)
    (AlgEquiv.refl : L ≃ₐ[K] L)
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Completion_ChosenLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# The chosen localization at a finite place

This file equips the actual chosen localization of a finite number-field
extension with its canonical valued local-field structures. It also defines
unramifiedness for that actual completed extension.
-/

open scoped NumberField Classical ValuativeRel NNReal
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The completion of the base field at the chosen finite place. -/
abbrev ChosenFinitePlaceBaseCompletion
    (w₀ : HeightOneSpectrum (𝓞 K)) :=
  (HeightOneSpectrum.adicAbv K w₀).Completion
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_FiniteAbelianCompositum
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Finite abelian composita

This file gives a common realization, in a chosen separable closure, of the
compositum of two finite abelian Galois extensions.  It also records the
canonical factor embeddings and their elementary degree bounds.
-/

noncomputable section

namespace AlgebraicNumberTheory

open scoped IsMulCommutative

universe u v

section AbelianCompositum

variable (K : Type u) [Field K]
variable {Omega : Type v} [Field Omega] [Algebra K Omega]

/-- The compositum, inside a common overfield, of two abelian Galois
intermediate fields is again abelian Galois over the base. -/
theorem isAbelianGalois_sup
    (A B : IntermediateField K Omega)
    [FiniteDimensional K A] [FiniteDimensional K B]
    [IsAbelianGalois K A] [IsAbelianGalois K B] :
    IsAbelianGalois K (A ⊔ B : IntermediateField K Omega) := by
  let M : IntermediateField K Omega := A ⊔ B
  let j : M →ₐ[K] Omega := M.val
  let A' : IntermediateField K M := A.comap j
  let B' : IntermediateField K M := B.comap j

  have hjrange : j.fieldRange = M :=
    IntermediateField.fieldRange_val M
  have hAmap : A'.map j = A := by
    apply IntermediateField.map_comap_eq_self
    rw [hjrange]
    exact le_sup_left
  have hBmap : B'.map j = B := by
    apply IntermediateField.map_comap_eq_self
    rw [hjrange]
    exact le_sup_right
  have hsup : A' ⊔ B' = ⊤ := by
    apply IntermediateField.map_injective j
    rw [IntermediateField.map_sup, hAmap, hBmap,
      ← AlgHom.fieldRange_eq_map, hjrange]

  let eA : A' →ₐ[K] A :=
    ((j.comp A'.val).codRestrict A.toSubalgebra fun x ↦ x.2)
  let eB : B' →ₐ[K] B :=
    ((j.comp B'.val).codRestrict B.toSubalgebra fun x ↦ x.2)
  let : IsAbelianGalois K A' := IsAbelianGalois.of_algHom eA
  let : IsAbelianGalois K B' := IsAbelianGalois.of_algHom eB
  let : IsGalois K M := inferInstance

  let rA : (M ≃ₐ[K] M) →* (A' ≃ₐ[K] A') :=
    AlgEquiv.restrictNormalHom A'
  let rB : (M ≃ₐ[K] M) →* (B' ≃ₐ[K] B') :=
    AlgEquiv.restrictNormalHom B'
  let r : (M ≃ₐ[K] M) →* (A' ≃ₐ[K] A') × (B' ≃ₐ[K] B') :=
    rA.prod rB
  have hr : Function.Injective r := by
    rw [injective_iff_map_eq_one]
    intro sigma hsigma
    have hAone : rA sigma = 1 := congrArg Prod.fst hsigma
    have hBone : rB sigma = 1 := congrArg Prod.snd hsigma
    have hmemA : sigma ∈ A'.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker]
      exact hAone
    have hmemB : sigma ∈ B'.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker]
      exact hBone
    have hmem : sigma ∈ (A' ⊔ B').fixingSubgroup := by
      rw [IntermediateField.fixingSubgroup_sup]
      exact ⟨hmemA, hmemB⟩
    simpa [hsup] using hmem

  exact
    { is_comm.comm := fun sigma tau ↦ by
        apply hr
        rw [map_mul, map_mul]
        apply Prod.ext
        · change rA sigma * rA tau = rA tau * rA sigma
          exact mul_comm (rA sigma) (rA tau)
        · change rB sigma * rB tau = rB tau * rB sigma
          exact mul_comm (rB sigma) (rB tau) }

end AbelianCompositum

end AlgebraicNumberTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Padic_Cyclotomic_TotallyRamified_EisensteinPolynomial
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# The Eisenstein polynomial of the `p`-power cyclotomic extension

For a primitive `p ^ m`-th root of unity `ζ`, with `m > 0`, the local
cyclotomic calculation proves that `ℚ_[p](ζ) / ℚ_[p]` is totally ramified of degree
`φ (p ^ m)`, identifies its Galois group with `(ZMod (p ^ m))ˣ`, identifies
its valuation ring with `ℤ_[p][ζ]`, and shows that `1 - ζ` is a prime
element of norm `p`.

The source is the translated cyclotomic Eisenstein polynomial
`Φ_{p^(k+1)}(X + 1)`.  We first transport its integral Eisenstein criterion
to the actual p-adic integer ring; no irreducibility or ramification
conclusion is assumed.
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

open Polynomial
open scoped Polynomial

universe u

/-- The translated prime-power cyclotomic polynomial over the actual p-adic
integer ring. -/
def padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt
    (p k : ℕ) [Fact p.Prime] : ℤ_[p][X] :=
  (cyclotomic (p ^ (k + 1)) ℤ_[p]).comp (X + 1)

theorem padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt_eq_map
    (p k : ℕ) [Fact p.Prime] :
    padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt p k =
      (((cyclotomic (p ^ (k + 1)) ℤ).comp (X + 1)).map
        (algebraMap ℤ ℤ_[p])) := by
  simp [padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt, Polynomial.map_comp]

/-- The translated cyclotomic polynomial remains Eisenstein after
completion from `ℤ` to `ℤ_[p]`. -/
theorem padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt_isEisensteinAt
    (p k : ℕ) [Fact p.Prime] :
    (padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt p k).IsEisensteinAt
      (Ideal.span ({(p : ℤ_[p])} : Set ℤ_[p])) := by
  let F : ℤ[X] := (cyclotomic (p ^ (k + 1)) ℤ).comp (X + 1)
  let G : ℤ_[p][X] := padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt p k
  have hF : F.IsEisensteinAt (Ideal.span ({(p : ℤ)} : Set ℤ)) := by
    simpa [F] using cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt p k
  have hGmonic : G.Monic := by
    dsimp [G, padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt]
    exact (cyclotomic.monic _ ℤ_[p]).comp_X_add_C 1
  refine hGmonic.isEisensteinAt_of_mem_of_notMem
    (Ideal.IsPrime.ne_top ((Ideal.span_singleton_prime PadicInt.prime_p.ne_zero).2
      PadicInt.prime_p)) ?_ ?_
  · intro i hi
    have hdeg : G.natDegree = F.natDegree := by
      change (padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt p k).natDegree = F.natDegree
      rw [padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt_eq_map]
      exact Polynomial.Monic.natDegree_map
        ((cyclotomic.monic (p ^ (k + 1)) ℤ).comp_X_add_C 1)
        (algebraMap ℤ ℤ_[p])
    have hmemF : F.coeff i ∈ Ideal.span ({(p : ℤ)} : Set ℤ) :=
      hF.mem (hdeg ▸ hi)
    rw [Ideal.mem_span_singleton] at hmemF ⊢
    change (p : ℤ_[p]) ∣ (padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt p k).coeff i
    rw [padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt_eq_map, coeff_map]
    obtain ⟨a, ha⟩ := hmemF
    refine ⟨(a : ℤ_[p]), ?_⟩
    simpa [F] using congrArg (algebraMap ℤ ℤ_[p]) ha
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro hdiv
    change (p : ℤ_[p]) ^ 2 ∣
      (padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt p k).coeff 0 at hdiv
    rw [padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt_eq_map, coeff_map] at hdiv
    have hdivZ : (p : ℤ) ^ 2 ∣ F.coeff 0 :=
      (PadicInt.pow_p_dvd_int_iff 2 (F.coeff 0)).mp hdiv
    exact hF.notMem (by
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact hdivZ)

/-- The translated polynomial is irreducible over `ℤ_[p]` by Eisenstein. -/
theorem padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt_irreducible
    (p k : ℕ) [Fact p.Prime] :
    Irreducible (padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt p k) := by
  have hei := padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt_isEisensteinAt p k
  have hprime :
      (Ideal.span ({(p : ℤ_[p])} : Set ℤ_[p])).IsPrime :=
    (Ideal.span_singleton_prime PadicInt.prime_p.ne_zero).2 PadicInt.prime_p
  have hmonic : (padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt p k).Monic :=
    (cyclotomic.monic _ ℤ_[p]).comp_X_add_C 1
  apply hei.irreducible hprime hmonic.isPrimitive
  rw [padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt, natDegree_comp,
    show (X + 1 : ℤ_[p][X]) = X + C 1 by simp,
    natDegree_X_add_C, mul_one, natDegree_cyclotomic]
  exact (Nat.totient_pos.mpr (pow_pos (Fact.out : Nat.Prime p).pos _))

/-- The translated polynomial is irreducible over the p-adic field. -/
theorem padicCyclotomicTotallyRamifiedShiftedCyclotomicPadic_irreducible
    (p k : ℕ) [Fact p.Prime] :
    Irreducible
      ((cyclotomic (p ^ (k + 1)) ℚ_[p]).comp (X + 1)) := by
  let G := padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt p k
  have hG : Irreducible G :=
    padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt_irreducible p k
  have hGmonic : G.Monic := (cyclotomic.monic _ ℤ_[p]).comp_X_add_C 1
  have hmap : Irreducible (G.map (algebraMap ℤ_[p] ℚ_[p])) :=
    hGmonic.irreducible_iff_irreducible_map_fraction_map.mp hG
  simpa [G, padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt,
    Polynomial.map_comp] using hmap

/-- The prime-power cyclotomic polynomial is irreducible over `ℚ_[p]`.
This supplies the local irreducibility input for the ramification analysis. -/
theorem padicCyclotomicPolynomial_irreducible_prime_pow_succ
    (p k : ℕ) [Fact p.Prime] :
    Irreducible (cyclotomic (p ^ (k + 1)) ℚ_[p]) := by
  let F : ℚ_[p][X] := cyclotomic (p ^ (k + 1)) ℚ_[p]
  have hs : Irreducible (F.comp (X + 1)) := by
    simpa [F] using padicCyclotomicTotallyRamifiedShiftedCyclotomicPadic_irreducible p k
  have hb := hs.map (Polynomial.algEquivAevalXAddC (-1 : ℚ_[p]))
  rw [Polynomial.algEquivAevalXAddC_apply, ← comp_eq_aeval] at hb
  simpa [F, comp_assoc] using hb

section CyclotomicExtension

variable {p k : ℕ} [Fact p.Prime]
variable {L : Type u} [Field L] [Algebra ℚ_[p] L]

local instance padicCyclotomicTotallyRamifiedAlgebraPadicInt_r9ff11f_1 : Algebra ℤ_[p] L :=
  ((algebraMap ℚ_[p] L).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra
local instance padicCyclotomicTotallyRamifiedScalarTowerPadicInt_r9ff11f_1 :
    IsScalarTower ℤ_[p] ℚ_[p] L :=
  IsScalarTower.of_algebraMap_eq' rfl
/-- A field generated over `ℚ_[p]` by the displayed primitive root is the
corresponding cyclotomic extension.  The generation hypothesis only spells
out the notation `ℚ_[p](ζ)`; none of the totally ramified cyclotomic theorem's conclusions is
assumed. -/
theorem padic_isCyclotomicExtension_of_primitiveRoot_adjoin_eq_top
    (ζ : L) (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))
    (hgen : Algebra.adjoin ℚ_[p] ({ζ} : Set L) = ⊤) :
    IsCyclotomicExtension {p ^ (k + 1)} ℚ_[p] L := by
  let A := Algebra.adjoin ℚ_[p] ({ζ} : Set L)
  let : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero⟩
  let hA : IsCyclotomicExtension {p ^ (k + 1)} ℚ_[p] A :=
    hζ.adjoin_isCyclotomicExtension ℚ_[p]
  let e : A ≃ₐ[ℚ_[p]] L :=
    (Subalgebra.equivOfEq A ⊤ hgen).trans Subalgebra.topEquiv
  exact IsCyclotomicExtension.equiv {p ^ (k + 1)} ℚ_[p] A e

end CyclotomicExtension

end Valuations
end AlgebraicNumberTheory

end
end


