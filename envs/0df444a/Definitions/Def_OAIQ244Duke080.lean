-- Prove2me | Definitions.Def_OAIQ244Duke080
-- name    : OAIQ244Duke080
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T23:12:27.99019+00:00
-- url     : https://prove2.me/theorems/2215e125-59c3-4dd2-96b5-0630a26cbd07
-- title:
--   Definitions bundle OAIQ244Duke080 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 34 declarations of OpenAI's Lean: 8 definitions and 26 theorems. The definitions and types are `GlobalClassFieldTheory.Reciprocity.chosenFinitePlaceArtinMonoidHom`, `GlobalClassFieldTheory.Reciprocity.finitePlaceArtinMonoidHomOfExtension`, `GlobalClassFieldTheory.Reciprocity.finitePlaceGlobalArtinMonoidHom`, `GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinMonoidHom`, `GlobalClassFieldTheory.Reciprocity.finitePlaceNormLowerArtin`, `GlobalClassFieldTheory.Reciprocity.finitePlaceNormRestrictedArtin`, `GlobalClassFieldTheory.Reciprocity.globalArtinMonoidHom`, `LocalClassFieldTheory.intrinsicFrobeniusFixedFieldEquivAmbientEmbeddedField`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `GlobalClassFieldTheory_ClassFieldAxiom_CyclicIdeleClassNormIndex`, `GlobalClassFieldTheory_Cohomology_CofinitelySplitFiniteExtension`, `GlobalClassFieldTheory_Reciprocity_FiniteIdeleArtin`, `GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_Conjugation`, `GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_Construction`, `GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_Core`, `GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_NormRestriction`, `GlobalClassFieldTheory_Reciprocity_GlobalArtin`, `LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_EmbeddedFrobeniusTransport`, `LocalClassFieldTheory_Finite_LocalReciprocity_GeneralTowerNaturality`, `LubinTate_Padic_ChangedUniformizerIntertwiner_IntertwinerConstruction`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke074` and `OAIQ244Duke075` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke084`, `OAIQ244Duke086`, `OAIQ244Duke087` and `OAIQ244Duke115`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
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
import Mathlib.Algebra.Group.Hom.Instances
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
import Mathlib.Algebra.Polynomial.Monic
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
import Mathlib.FieldTheory.Galois.Notation
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
import Mathlib.RingTheory.Finiteness.Cardinality
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
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Evaluation
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
import Mathlib.RingTheory.WittVector.Compare
import Mathlib.RingTheory.WittVector.Complete
import Mathlib.RingTheory.WittVector.FrobeniusFractionField
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
import Definitions.Def_OAIQ244Duke074
import Definitions.Def_OAIQ244Duke075

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_CyclicIdeleClassNormIndex
attribute [-instance] _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.Padic.padicUnitFiniteFactor_finite _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

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

open CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand

section NormQuotientCommutativity

attribute [local instance] GlobalClassFieldTheory.ClassFieldAxiom.cyclicNormBase_isMulCommutative
/-- Finiteness and cardinalities of the actual low-degree Tate cohomology
groups of the relative idele class representation. -/
theorem ideleClass_tate_lowDegree_finite_card_eq_finrank_cyclic
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (sigma : L ≃ₐ[K] L)
    (hsigma :
      ∀ tau : L ≃ₐ[K] L,
        tau ∈ Subgroup.zpowers sigma) :
    letI :=
      RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
    Finite
          (tateCohomology
            (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
              (RelativeIdeleGroup.ClassGroup K L)) 0) ∧
      Finite
          (tateCohomology
            (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
              (RelativeIdeleGroup.ClassGroup K L)) (-1)) ∧
      Nat.card
          (tateCohomology
            (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
              (RelativeIdeleGroup.ClassGroup K L)) 0) =
        Module.finrank K L ∧
      Nat.card
          (tateCohomology
            (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
              (RelativeIdeleGroup.ClassGroup K L)) (-1)) =
        1 := by
  let :=
    RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
  have hHerbrand :=
    ideleClass_lowDegree_card_eq_finrank_cyclic
      K L sigma hsigma
  let :
      Finite
        (HerbrandH0 (L ≃ₐ[K] L)
          (RelativeIdeleGroup.ClassGroup K L)) :=
    Nat.finite_of_card_ne_zero (by
      rw [hHerbrand.1]
      exact Nat.ne_of_gt Module.finrank_pos)
  let :
      Finite
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (RelativeIdeleGroup.ClassGroup K L) sigma) :=
    Nat.finite_of_card_ne_zero (by
      rw [hHerbrand.2]
      exact one_ne_zero)
  let e0 :
      tateCohomology
          (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
            (RelativeIdeleGroup.ClassGroup K L)) 0 ≃
        Additive
          (HerbrandH0 (L ≃ₐ[K] L)
            (RelativeIdeleGroup.ClassGroup K L)) :=
    (tateH0IsoHerbrandH0
      (G := L ≃ₐ[K] L)
      (A := RelativeIdeleGroup.ClassGroup K L)).toLinearEquiv.toEquiv
  let em :
      tateCohomology
          (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
            (RelativeIdeleGroup.ClassGroup K L)) (-1) ≃
        Additive
          (HerbrandHMinusOne (L ≃ₐ[K] L)
            (RelativeIdeleGroup.ClassGroup K L) sigma) :=
    (tateHMinusOneIsoHerbrandHMinusOne
      (G := L ≃ₐ[K] L)
      (A := RelativeIdeleGroup.ClassGroup K L)
      sigma hsigma).toLinearEquiv.toEquiv
  let :
      Finite
        (tateCohomology
          (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
            (RelativeIdeleGroup.ClassGroup K L)) 0) :=
    Finite.of_injective e0 e0.injective
  let :
      Finite
        (tateCohomology
          (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
            (RelativeIdeleGroup.ClassGroup K L)) (-1)) :=
    Finite.of_injective em em.injective
  refine ⟨inferInstance, inferInstance, ?_, ?_⟩
  · calc
      Nat.card
            (tateCohomology
              (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
                (RelativeIdeleGroup.ClassGroup K L)) 0) =
          Nat.card
            (Additive
              (HerbrandH0 (L ≃ₐ[K] L)
                (RelativeIdeleGroup.ClassGroup K L))) :=
        Nat.card_congr e0
      _ = Module.finrank K L := by
        change
          Nat.card
              (HerbrandH0 (L ≃ₐ[K] L)
                (RelativeIdeleGroup.ClassGroup K L)) =
            Module.finrank K L
        exact hHerbrand.1
  · calc
      Nat.card
            (tateCohomology
              (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
                (RelativeIdeleGroup.ClassGroup K L)) (-1)) =
          Nat.card
            (Additive
              (HerbrandHMinusOne (L ≃ₐ[K] L)
                (RelativeIdeleGroup.ClassGroup K L) sigma)) :=
        Nat.card_congr em
      _ = 1 := by
        change
          Nat.card
              (HerbrandHMinusOne (L ≃ₐ[K] L)
                (RelativeIdeleGroup.ClassGroup K L) sigma) =
            1
        exact hHerbrand.2

end NormQuotientCommutativity

end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Cohomology_CofinitelySplitFiniteExtension
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldNumberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicLevel_numberField _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.cyclicPrimeDegreeIntermediate_base_isCyclic _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeDegreeIntermediate_top_isCyclic _root_.cyclicPrimeDegreeIntermediate_top_isGalois
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitKummerCoordinatePlace_decompositionGroup _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Cofinitely split finite extensions are trivial

For a finite extension of number fields `L / K`, if all but finitely
many finite places of `K` split completely in `L`, then `L / K` has
degree one.  The normal-closure and splitting-transport constructions
used in the proof live in their general algebraic-number-theory
modules; this file contains only the global class-field-theoretic
conclusion.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Cohomology

variable
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

/-- If all but finitely many finite places of `K` split completely in
the finite extension `L / K`, then the extension has degree one.

The proof passes to the finite normal closure `M`.  If `M / K` were
nontrivial, a prime-order automorphism would give an intermediate field
`K'` for which `M / K'` is cyclic of prime degree.  The infinitude of
full-decomposition places in cyclic prime-degree extensions then supplies
infinitely many nonsplitting places of `K'`, contradicting the finiteness
transported from `M / K`. -/
theorem finrank_eq_one_of_finite_nonSplittingPlaces
    (hfinite :
      {v : HeightOneSpectrum (𝓞 K) |
        ¬ FinitePlaceSplitsCompletelyInExtension
          (K := K) (E := L) v}.Finite) :
    Module.finrank K L = 1 := by
  let M := finiteNormalClosure K L
  let : NumberField M :=
    finiteNormalClosure_numberField K L
  let : IsGalois K M :=
    finiteNormalClosure_isGalois K L
  have hfiniteM :
      {v : HeightOneSpectrum (𝓞 K) |
        ¬ FinitePlaceSplitsCompletely
          (K := K) (L := M) v}.Finite := by
    simpa only [M] using
      finite_nonSplittingPlaces_normalClosure_of_original
        K L hfinite
  have hdegreeM : Module.finrank K M = 1 := by
    by_contra hne
    have hgt : 1 < Module.finrank K M := by
      have hpos : 0 < Module.finrank K M :=
        Module.finrank_pos
      omega
    let K' :=
      primeOrderFixedField
        (K := K) (L := M) hgt
    let p :=
      fixedFieldPrime
        (K := K) (L := M) hgt
    have hp : p.Prime := by
      simpa only [p] using
        fixedFieldPrime_prime
          (K := K) (L := M) hgt
    have hrelativeDegree :
        Module.finrank K' M = p := by
      simpa only [K', p] using
        primeOrderFixedField_finrank
          (K := K) (L := M) hgt
    have hrelativeNontrivial :
        1 < Module.finrank K' M := by
      rw [hrelativeDegree]
      exact hp.one_lt
    have hcard :
        Nat.card (M ≃ₐ[K'] M) = p ^ 1 := by
      calc
        Nat.card (M ≃ₐ[K'] M) = p := by
          simpa only [K', p] using
            primeOrderFixedField_card_aut
              (K := K) (L := M) hgt
        _ = p ^ 1 := by simp
    have hinfinite :
        Set.Infinite
          {v : HeightOneSpectrum (𝓞 K') |
            finitePlaceDecompositionGroup
                (K := K') (L := M) v = ⊤} :=
      cyclic_prime_power_infinite_fullDecompositionPlaces
        (K := K') (L := M)
        hp (by omega) hcard
    have hfiniteRelative :
        {v : HeightOneSpectrum (𝓞 K') |
          ¬ FinitePlaceSplitsCompletely
            (K := K') (L := M) v}.Finite :=
      finite_nonsplittingPlaces_over_intermediate
        (K := K) (M := K') (L := M) hfiniteM
    apply hinfinite
    apply hfiniteRelative.subset
    intro v hv
    exact
      finitePlace_not_splitsCompletely_of_decompositionGroup_eq_top
        (K := K') (L := M)
        hrelativeNontrivial v hv
  have hle :
      Module.finrank K L ≤ Module.finrank K M := by
    simpa only [M] using finrank_le_finiteNormalClosure K L
  have hpos : 0 < Module.finrank K L :=
    Module.finrank_pos
  omega

end Cohomology
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_Construction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionIsAlgebraic _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.gLocallyCompact _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instLocallyCompactSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xLocallyCompact _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.chosenFinitePlaceBaseValuationIsNontrivial _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceExtensionCompletionAlgebra _root_.chosenFinitePlaceExtensionCompletionSMul _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsUltrametricDist _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Construction of finite-place Artin homomorphisms

This module constructs the local Artin map for a chosen extension of a finite place and transports it through the actual decomposition group into the global Galois group.
-/

open scoped Classical IsMulCommutative NNReal NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [hKLfinite : FiniteDimensional K L] [IsAbelianGalois K L]

/-- The finite-place Artin homomorphism associated with a specified
extension of the base adic absolute value to the global extension. -/
noncomputable def finitePlaceArtinMonoidHomOfExtension
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L) :
    (v.adicCompletion K)ˣ →* (L ≃ₐ[K] L) := by
  let vK :=
    NumberField.HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  letI hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  letI :=
    LocalClassFieldTheory.localizedCompletionGlobalAlgebra vK w
  letI :=
    LocalClassFieldTheory.localizedCompletionIsScalarTower vK w
  let E :=
    AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  letI : FiniteDimensional vK.Completion E :=
    AlgebraicNumberTheory.Valuations.localizedCompletionModuleFinite vK hvK w
  letI : IsAbelianGalois vK.Completion E :=
    LocalClassFieldTheory.localizedCompletion_isAbelianGalois
      vK hvK w
  letI : NontriviallyNormedField vK.Completion :=
    absoluteValueExtension_completionNontriviallyNormedField
      vK hvK
  letI : LocallyCompactSpace vK.Completion :=
    AbsoluteValue.Completion.locallyCompactSpace
      (finitePlaceCompletionBaseMap_isometry v)
  let hvKna : IsNonarchimedean (vK : K → ℝ) :=
    NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v
  letI : IsUltrametricDist vK.Completion :=
    finitePlaceArtinCompletionIsUltrametricDist vK hvKna
  letI : Valued vK.Completion ℝ≥0 :=
    finitePlaceArtinCompletionValued vK hvKna
  let vC : Valuation vK.Completion ℝ≥0 :=
    Valued.v
  letI : vC.IsNontrivial :=
    (inferInstance :
      (NormedField.valuation
        (K := vK.Completion)).IsNontrivial)
  letI : ValuativeRel vK.Completion :=
    finitePlaceArtinCompletionValuativeRel vK hvKna
  letI : vC.Compatible :=
    Valuation.Compatible.ofValuation vC
  letI : ValuativeRel.IsNontrivial vK.Completion :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vC).2
      inferInstance
  letI : IsValuativeTopology vK.Completion :=
    isValuativeTopology_of_valued_ofValuation
      vK.Completion ℝ≥0
  letI : IsNonarchimedeanLocalField vK.Completion :=
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }
  let eD :
      absoluteValueDecompositionGroup K w.1 ≃*
        (E ≃ₐ[vK.Completion] E) :=
    decompositionGroupEquivAlgebraicLocalizationAut
      vK hvK w
  let eK :
      vK.Completionˣ ≃* (v.adicCompletion K)ˣ :=
    finitePlaceCompletionUnitsContinuousMulEquiv v
  exact
    (absoluteValueDecompositionGroup K w.1).subtype.comp
      (eD.symm.toMonoidHom.comp
        ((LocalClassFieldTheory.abelianLocalArtinMonoidHom
          vK.Completion E).comp eK.symm.toMonoidHom))

/-- The local Artin homomorphism on the algebraic localization attached to a chosen extension of a finite place. -/
noncomputable def finitePlaceLocalArtinMonoidHom
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    letI : Algebra vK.Completion E :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    (v.adicCompletion K)ˣ →* (E ≃ₐ[vK.Completion] E) := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  letI : Algebra vK.Completion E :=
    finitePlaceLocalArtinLocalizedAlgebra v w
  letI : FiniteDimensional vK.Completion E :=
    finitePlaceLocalArtinFiniteDimensional v w
  letI : IsAbelianGalois vK.Completion E :=
    finitePlaceLocalArtinIsAbelianGalois v w hKLfinite
  letI : ValuativeRel vK.Completion :=
    finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField vK.Completion :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  exact
    (LocalClassFieldTheory.abelianLocalArtinMonoidHom
      vK.Completion E).comp
        (finitePlaceLocalArtinInputMonoidHom v)

/-- Evaluation of the localized finite-place Artin homomorphism through the canonical completion equivalence. -/
theorem finitePlaceLocalArtinMonoidHom_apply
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (x : (v.adicCompletion K)ˣ) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let hvK : vK.IsNontrivial :=
      RayClass.adicAbv_isNontrivial v
    letI hK :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    letI : FiniteDimensional vK.Completion E :=
      AlgebraicNumberTheory.Valuations.localizedCompletionModuleFinite vK hvK w
    letI : IsAbelianGalois vK.Completion E :=
      LocalClassFieldTheory.localizedCompletion_isAbelianGalois
        vK hvK w
    letI : NontriviallyNormedField vK.Completion :=
      absoluteValueExtension_completionNontriviallyNormedField
        vK hvK
    letI : LocallyCompactSpace vK.Completion :=
      AbsoluteValue.Completion.locallyCompactSpace
        (finitePlaceCompletionBaseMap_isometry v)
    let hvKna : IsNonarchimedean (vK : K → ℝ) :=
      NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v
    letI : IsUltrametricDist vK.Completion :=
      finitePlaceArtinCompletionIsUltrametricDist vK hvKna
    letI : Valued vK.Completion ℝ≥0 :=
      finitePlaceArtinCompletionValued vK hvKna
    letI : ValuativeRel vK.Completion :=
      finitePlaceArtinCompletionValuativeRel vK hvKna
    letI : IsNonarchimedeanLocalField vK.Completion :=
      finitePlaceArtinCompletionIsNonarchimedeanLocalField
        vK hvKna
    let eK :
        vK.Completionˣ ≃* (v.adicCompletion K)ˣ :=
      finitePlaceCompletionUnitsContinuousMulEquiv v
    finitePlaceLocalArtinMonoidHom
        (K := K) (L := L) v w x =
      LocalClassFieldTheory.abelianLocalArtinMonoidHom
        vK.Completion E (eK.symm x) := by
  rfl

/-- The finite-place Artin map factors through the localized Artin map and the decomposition-group inclusion. -/
theorem finitePlaceArtinMonoidHomOfExtension_factor
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L) :
    finitePlaceArtinMonoidHomOfExtension
        (K := K) (L := L) v w =
      (finitePlaceLocalToGlobalMonoidHom
        (K := K) (L := L) v w).comp
        (finitePlaceLocalArtinMonoidHom
          (K := K) (L := L) v w) := by
  rfl

/-- The finite-place Artin homomorphism from the concrete adic
completion into the actual global Galois group.  Its image is contained
in the decomposition group at the chosen extension above `v`. -/
noncomputable def chosenFinitePlaceArtinMonoidHom
    (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →* (L ≃ₐ[K] L) :=
  finitePlaceArtinMonoidHomOfExtension
    (K := K) (L := L) v
    (chosenFinitePlaceExtension (L := L) v)

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_GeneralTowerNaturality
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_isGalois _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceLocalizedIsGalois _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

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

/-- The actual finite abelian local Artin maps commute with the genuine
restriction homomorphism in every finite abelian tower `K ⊂ E ⊂ L`. -/
theorem abelianLocalArtinMonoidHom_restrict_tower
    (K E L : Type)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [FiniteDimensional K E] [FiniteDimensional K L]
    [IsAbelianGalois K E] [IsAbelianGalois K L] :
    (AlgEquiv.restrictNormalHom E).comp
        (abelianLocalArtinMonoidHom K L) =
      abelianLocalArtinMonoidHom K E := by
  apply MonoidHom.ext
  intro a
  exact localArtinAutomorphism_restrict_tower K E L a

/-- Finite local Artin maps are natural under a `K`-algebra equivalence of
finite abelian extensions.  The Galois groups are identified by conjugating
automorphisms with that equivalence. -/
theorem abelianLocalArtinMonoidHom_autCongr
    (K L M : Type)
    [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsAbelianGalois K L] [IsAbelianGalois K M]
    (e : L ≃ₐ[K] M) :
    (AlgEquiv.autCongr e).toMonoidHom.comp
        (abelianLocalArtinMonoidHom K L) =
      abelianLocalArtinMonoidHom K M := by
  let : Algebra M L := e.symm.toRingHom.toAlgebra
  let : IsScalarTower K M L :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro x
      exact (e.symm.commutes x).symm)
  rw [← restrictNormalHom_eq_autCongr K L M e]
  exact abelianLocalArtinMonoidHom_restrict_tower K M L

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_Conjugation
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionIsAlgebraic _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceExtensionCompletionAlgebra _root_.chosenFinitePlaceExtensionCompletionSMul _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsUltrametricDist _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Conjugation of finite-place Artin homomorphisms

This module identifies localized completions associated with conjugate extensions and proves conjugation invariance of the resulting finite-place Artin map.
-/

open scoped Classical IsMulCommutative NNReal NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

/-- Local Artin maps are natural under the localized-completion
equivalence induced by conjugating a finite-place extension. -/
theorem finitePlaceLocalArtinMonoidHom_conjugate
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (g : L ≃ₐ[K] L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let wc := absoluteValueExtensionConjugate vK w g
    let Ew := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    let Ewc := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wc
    letI : Algebra vK.Completion Ew :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    letI : Algebra vK.Completion Ewc :=
      finitePlaceLocalArtinLocalizedAlgebra v wc
    let e :=
      finitePlaceConjugateLocalizedCompletionAlgEquiv
        (K := K) (L := L) v w g
    (AlgEquiv.autCongr e).toMonoidHom.comp
        (finitePlaceLocalArtinMonoidHom
          (K := K) (L := L) v wc) =
      finitePlaceLocalArtinMonoidHom
        (K := K) (L := L) v w := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let wc := absoluteValueExtensionConjugate vK w g
  let Ew := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  let Ewc := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wc
  let : Algebra vK.Completion Ew :=
    finitePlaceLocalArtinLocalizedAlgebra v w
  let : Algebra vK.Completion Ewc :=
    finitePlaceLocalArtinLocalizedAlgebra v wc
  let : FiniteDimensional vK.Completion Ew :=
    finitePlaceLocalArtinFiniteDimensional v w
  let : FiniteDimensional vK.Completion Ewc :=
    finitePlaceLocalArtinFiniteDimensional v wc
  let : IsAbelianGalois vK.Completion Ew :=
    finitePlaceLocalArtinIsAbelianGalois v w
      (inferInstance : FiniteDimensional K L)
  let : IsAbelianGalois vK.Completion Ewc :=
    finitePlaceLocalArtinIsAbelianGalois v wc
      (inferInstance : FiniteDimensional K L)
  let : ValuativeRel vK.Completion :=
    finitePlaceLocalArtinCompletionValuativeRel v
  let : IsNonarchimedeanLocalField vK.Completion :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let e :=
    finitePlaceConjugateLocalizedCompletionAlgEquiv
      (K := K) (L := L) v w g
  let eK :
      vK.Completionˣ ≃* (v.adicCompletion K)ˣ :=
    finitePlaceCompletionUnitsContinuousMulEquiv v
  change
    (AlgEquiv.autCongr e).toMonoidHom.comp
        ((LocalClassFieldTheory.abelianLocalArtinMonoidHom
          vK.Completion Ewc).comp eK.symm.toMonoidHom) =
      (LocalClassFieldTheory.abelianLocalArtinMonoidHom
        vK.Completion Ew).comp eK.symm.toMonoidHom
  exact
    congrArg (fun f => f.comp eK.symm.toMonoidHom)
      (LocalClassFieldTheory.abelianLocalArtinMonoidHom_autCongr
        vK.Completion Ewc Ew e)

/-- Conjugating the chosen extension of a finite place does not change
its Artin homomorphism when the global extension is abelian. -/
theorem finitePlaceArtinMonoidHomOfExtension_conjugate
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (g : L ≃ₐ[K] L) :
    finitePlaceArtinMonoidHomOfExtension
        (K := K) (L := L) v
        (absoluteValueExtensionConjugate
          (NumberField.HeightOneSpectrum.adicAbv K v) w g) =
      finitePlaceArtinMonoidHomOfExtension
        (K := K) (L := L) v w := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let wc := absoluteValueExtensionConjugate vK w g
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let hwK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hwK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let hwcK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) wc.1
  let : SMul K wc.1.Completion := hwcK.toSMul
  let : Algebra vK.Completion wc.1.Completion :=
    AbsoluteValue.completionAlgebra vK wc.1 wc.2
  let Ew := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  let Ewc := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wc
  let e :=
    finitePlaceConjugateLocalizedCompletionAlgEquiv
      (K := K) (L := L) v w g
  let eDw :
      absoluteValueDecompositionGroup K w.1 ≃*
        (Ew ≃ₐ[vK.Completion] Ew) :=
    decompositionGroupEquivAlgebraicLocalizationAut
      vK hvK w
  let eDwc :
      absoluteValueDecompositionGroup K wc.1 ≃*
        (Ewc ≃ₐ[vK.Completion] Ewc) :=
    decompositionGroupEquivAlgebraicLocalizationAut
      vK hvK wc
  have htransport :=
    finitePlaceDecompositionTransport_conjugate
      (K := K) (L := L) v w g
  have hlocal :=
    finitePlaceLocalArtinMonoidHom_conjugate
      (K := K) (L := L) v w g
  change
    ((absoluteValueDecompositionGroup K wc.1).subtype.comp
        eDwc.symm.toMonoidHom).comp
        (finitePlaceLocalArtinMonoidHom
          (K := K) (L := L) v wc) =
      ((absoluteValueDecompositionGroup K w.1).subtype.comp
        eDw.symm.toMonoidHom).comp
        (finitePlaceLocalArtinMonoidHom
          (K := K) (L := L) v w)
  calc
    _ =
        (((absoluteValueDecompositionGroup K w.1).subtype.comp
            eDw.symm.toMonoidHom).comp
          (AlgEquiv.autCongr e).toMonoidHom).comp
            (finitePlaceLocalArtinMonoidHom
              (K := K) (L := L) v wc) :=
      congrArg
        (fun f => f.comp
          (finitePlaceLocalArtinMonoidHom
            (K := K) (L := L) v wc))
        htransport
    _ =
        ((absoluteValueDecompositionGroup K w.1).subtype.comp
          eDw.symm.toMonoidHom).comp
            ((AlgEquiv.autCongr e).toMonoidHom.comp
              (finitePlaceLocalArtinMonoidHom
                (K := K) (L := L) v wc)) := by
      rfl
    _ = _ := by rw [hlocal]

/-- The finite-place Artin homomorphism is independent of the chosen
extension of the base place in an abelian extension. -/
theorem finitePlaceArtinMonoidHomOfExtension_eq
    (v : HeightOneSpectrum (𝓞 K))
    (w w' : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L) :
    finitePlaceArtinMonoidHomOfExtension
        (K := K) (L := L) v w =
      finitePlaceArtinMonoidHomOfExtension
        (K := K) (L := L) v w' := by
  let : NumberField L := NumberField.of_module_finite K L
  let W :=
    finitePlaceExtensionCentre
      (K := K) (L := L) v w
  let W' :=
    finitePlaceExtensionCentre
      (K := K) (L := L) v w'
  let : Finite (L ≃ₐ[K] L) :=
    IsGaloisGroup.finite (L ≃ₐ[K] L) K L
  let :
      IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing
      (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
  let : W.asIdeal.LiesOver v.asIdeal :=
    ⟨(finitePlaceExtensionCentreIdeal_under
      (K := K) (L := L) v w).symm⟩
  let : W'.asIdeal.LiesOver v.asIdeal :=
    ⟨(finitePlaceExtensionCentreIdeal_under
      (K := K) (L := L) v w').symm⟩
  obtain ⟨g, hg⟩ :=
    HilbertRamification.Dedekind.exists_smul_eq_of_isGaloisGroup
      v.asIdeal W.asIdeal W'.asIdeal (L ≃ₐ[K] L)
  have hplace :
      finitePlaceEquiv K L g W = W' := by
    apply HeightOneSpectrum.ext
    rw [finitePlaceEquiv_asIdeal]
    exact hg
  have hconjugate :
      absoluteValueExtensionConjugate
          (NumberField.HeightOneSpectrum.adicAbv K v)
          w g⁻¹ =
        w' := by
    apply
      finitePlaceExtensionCentre_injective
        (K := K) (L := L) v
    rw [finitePlaceExtensionCentre_conjugate]
    simpa only [inv_inv, W, W'] using hplace
  rw [← hconjugate]
  exact
    (finitePlaceArtinMonoidHomOfExtension_conjugate
      (K := K) (L := L) v w g⁻¹).symm

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_EmbeddedFrobeniusTransport
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RayClass.Modulus.congruenceSubgroup_normal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.ideleGroupIsTopologicalGroup _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

/-- The intrinsic-to-ambient quotient equivalence preserves and reflects
membership in the Frobenius closure generated by a Frobenius element. -/
theorem
    intrinsicFrobeniusClosure_iff_ambientEmbeddedField
    (j : E →ₐ[K] SeparableClosure K) :
    let i :=
      j.comp (IsScalarTower.toAlgHom K F E)
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    ∀ e : SeparableClosure F ≃ₐ[F] SeparableClosure K,
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
      let RF :=
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
      ∀ (sigma :
          (localResidueDatum F).FrobeniusElements
            RF EI.field EI.below)
        (q :
          (intrinsicAbstractBase F).toSubgroup ⧸
            (localResidueDatum F).extensionInertiaWithin
              (intrinsicAbstractBase F) EI.field EI.below),
        q ∈ ((localResidueDatum F).frobeniusClosure
            RF EI.field EI.below sigma).toSubgroup ↔
          intrinsicFrobeniusQuotientContinuousEquivAmbientEmbeddedField
              K F E j e q ∈
            ((localResidueDatum K).frobeniusClosure
              RH J₀ hJH
              (intrinsicFrobeniusElementToAmbientEmbeddedField
                K F E j e sigma)).toSubgroup := by
  dsimp only
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  let : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  intro e
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
  have hRange :
      AlgHom.fieldRange i ≤ AlgHom.fieldRange j := by
    intro x hx
    rcases hx with ⟨y, rfl⟩
    exact ⟨algebraMap F E y, rfl⟩
  let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
    change
      (AlgHom.fieldRange j).fixingSubgroup ≤
        (AlgHom.fieldRange i).fixingSubgroup
    exact (AlgHom.fieldRange i).fixingSubgroup_le hRange
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
  let RF :=
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
  intro sigma q
  let xi :=
    intrinsicFrobeniusQuotientContinuousEquivAmbientEmbeddedField
      K F E j e
  let xiHom :=
    ContinuousMonoidHom.toContinuousMonoidHom xi
  let xiInvHom :=
    ContinuousMonoidHom.toContinuousMonoidHom xi.symm
  constructor
  · intro hq
    change
      q ∈
        (closedSubgroupGenerated
          (Set.range (fun _ : Unit => sigma.1) : Set
            ((intrinsicAbstractBase F).toSubgroup ⧸
              (localResidueDatum F).extensionInertiaWithin
                (intrinsicAbstractBase F) EI.field EI.below)) :
          Subgroup _) at hq
    have hmap :=
      map_mem_closedSubgroupGenerated_image
        xiHom
        hq
    have hgenerators :
        xiHom ''
            Set.range (fun _ : Unit => sigma.1) =
          Set.range (fun _ : Unit => xiHom sigma.1) := by
      ext y
      constructor
      · rintro ⟨x, ⟨u, rfl⟩, rfl⟩
        exact ⟨u, rfl⟩
      · rintro ⟨u, rfl⟩
        exact ⟨sigma.1, ⟨u, rfl⟩, rfl⟩
    rw [hgenerators] at hmap
    change
      xiHom q ∈
        (closedSubgroupGenerated
          (Set.range (fun _ : Unit => xiHom sigma.1) : Set
            (H₀.toSubgroup ⧸
              (localResidueDatum K).extensionInertiaWithin
                H₀ J₀ hJH)) :
          Subgroup _)
    exact hmap
  · intro hq
    change
      xiHom q ∈
        (closedSubgroupGenerated
          (Set.range (fun _ : Unit => xiHom sigma.1) : Set
            (H₀.toSubgroup ⧸
              (localResidueDatum K).extensionInertiaWithin
                H₀ J₀ hJH)) :
          Subgroup _) at hq
    have hmap :=
      map_mem_closedSubgroupGenerated_image
        xiInvHom
        hq
    have hgenerators :
        xiInvHom ''
            Set.range (fun _ : Unit => xiHom sigma.1) =
          Set.range (fun _ : Unit => sigma.1) := by
      ext y
      constructor
      · rintro ⟨x, ⟨u, rfl⟩, rfl⟩
        exact ⟨u, (xi.symm_apply_apply sigma.1).symm⟩
      · rintro ⟨u, rfl⟩
        exact
          ⟨xiHom sigma.1, ⟨u, rfl⟩,
            xi.symm_apply_apply sigma.1⟩
    rw [hgenerators] at hmap
    have hvalue : xiInvHom (xiHom q) = q :=
      xi.symm_apply_apply q
    rw [hvalue] at hmap
    change
      q ∈
        (closedSubgroupGenerated
          (Set.range (fun _ : Unit => sigma.1) : Set
            ((intrinsicAbstractBase F).toSubgroup ⧸
              (localResidueDatum F).extensionInertiaWithin
                (intrinsicAbstractBase F) EI.field EI.below)) :
          Subgroup _)
    exact hmap

/-- The intrinsic-to-ambient absolute Galois equivalence preserves and reflects
membership in the Frobenius fixed subgroup. -/
theorem
    intrinsicFrobeniusFixedSubgroup_iff_ambientEmbeddedField
    (j : E →ₐ[K] SeparableClosure K) :
    let i :=
      j.comp (IsScalarTower.toAlgHom K F E)
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    ∀ e : SeparableClosure F ≃ₐ[F] SeparableClosure K,
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
      let RF :=
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
      ∀ (sigma :
          (localResidueDatum F).FrobeniusElements
            RF EI.field EI.below)
        (tau : (intrinsicAbstractBase F).toSubgroup),
        tau ∈ (localResidueDatum F).frobeniusFixedSubgroupWithin
            RF EI.field EI.below sigma ↔
          intrinsicBaseEquivAmbientEmbeddedField K F i e tau ∈
            (localResidueDatum K).frobeniusFixedSubgroupWithin
              RH J₀ hJH
              (intrinsicFrobeniusElementToAmbientEmbeddedField
                K F E j e sigma) := by
  dsimp only
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  let : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  intro e
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
  let RF :=
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
    ⟨H₀, ambientEmbeddedAbsoluteQuotientFinite K F i⟩
  let RH :=
    H.toFiniteResidueAbstractField (localResidueDatum K)
  intro sigma tau
  have htransport :=
    intrinsicFrobeniusClosure_iff_ambientEmbeddedField
      K F E j e sigma (QuotientGroup.mk tau)
  have hquotientMk :
      intrinsicFrobeniusQuotientContinuousEquivAmbientEmbeddedField
          K F E j e (QuotientGroup.mk tau) =
        QuotientGroup.mk
          (intrinsicBaseEquivAmbientEmbeddedField K F i e tau) := by
    exact
      LocalFieldTheory.QuotientGroup.continuousCongr_mk
        _ _ _ _ tau
  rw [hquotientMk] at htransport
  change
    QuotientGroup.mk tau ∈
        ((localResidueDatum F).frobeniusClosure
          RF EI.field EI.below sigma).toSubgroup ↔
      QuotientGroup.mk
          (intrinsicBaseEquivAmbientEmbeddedField K F i e tau) ∈
        ((localResidueDatum K).frobeniusClosure
          RH J₀ hJH
          (intrinsicFrobeniusElementToAmbientEmbeddedField
            K F E j e sigma)).toSubgroup
  convert htransport using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [ i, jF, jI, EI, H₀, J₀, RF, H, RH])
  · rfl
  · rfl

/-- Restricting the ambient separable-closure equivalence gives an
`F`-algebra equivalence between the intrinsic and ambient Frobenius fixed
fields. -/
noncomputable def
    intrinsicFrobeniusFixedFieldEquivAmbientEmbeddedField
    (j : E →ₐ[K] SeparableClosure K) :
    let i :=
      j.comp (IsScalarTower.toAlgHom K F E)
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    ∀ e : SeparableClosure F ≃ₐ[F] SeparableClosure K,
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
      let RF :=
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
      ∀ sigma :
          (localResidueDatum F).FrobeniusElements
            RF EI.field EI.below,
        let sigmaH :=
          intrinsicFrobeniusElementToAmbientEmbeddedField
            K F E j e sigma
        let SF :=
          (localResidueDatum F).frobeniusFixedField
            RF EI.field EI.below sigma
        let SH :=
          (localResidueDatum K).frobeniusFixedField
            RH J₀ hJH sigmaH
        let hSHH :=
          (localResidueDatum K).frobeniusFixedField_le
            RH J₀ hJH sigmaH
        let LH :=
          abstractRelativeFixedField K (SeparableClosure K) hSHH
        let iLH : F →ₐ[K] LH :=
          i.codRestrict (LH.restrictScalars K).toSubalgebra (fun x => by
            change
              i x ∈ IntermediateField.fixedField SH.toSubgroup
            rw [IntermediateField.mem_fixedField_iff]
            intro rho hrho
            have hrhoH : rho ∈ H₀.toSubgroup :=
              hSHH hrho
            change rho (i x) = i x
            change
              rho ∈ (AlgHom.fieldRange i).fixingSubgroup at hrhoH
            rw [IntermediateField.mem_fixingSubgroup_iff] at hrhoH
            exact hrhoH (i x) ⟨x, rfl⟩)
        letI : Algebra F LH :=
          iLH.toRingHom.toAlgebra
        abstractFixedField F (SeparableClosure F) SF ≃ₐ[F] LH := by
  dsimp only
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  letI : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  intro e
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
  let RF :=
    (intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField
      (localResidueDatum F)
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
  let RH :=
    H.toFiniteResidueAbstractField (localResidueDatum K)
  intro sigma
  let sigmaH :=
    intrinsicFrobeniusElementToAmbientEmbeddedField
      K F E j e sigma
  let SF :=
    (localResidueDatum F).frobeniusFixedField
      RF EI.field EI.below sigma
  let SH :=
    (localResidueDatum K).frobeniusFixedField
      RH J₀ hJH sigmaH
  let hSFB :=
    (localResidueDatum F).frobeniusFixedField_le
      RF EI.field EI.below sigma
  let hSHH :=
    (localResidueDatum K).frobeniusFixedField_le
      RH J₀ hJH sigmaH
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
  letI : Algebra F LH :=
    iLH.toRingHom.toAlgebra
  let psi :=
    intrinsicBaseEquivAmbientEmbeddedField K F i e
  have hmem (x : SeparableClosure F) :
      x ∈ IntermediateField.fixedField SF.toSubgroup ↔
        e x ∈ IntermediateField.fixedField SH.toSubgroup := by
    constructor
    · intro hx
      rw [IntermediateField.mem_fixedField_iff]
      intro rho hrho
      let rhoH : H₀.toSubgroup := ⟨rho, hSHH hrho⟩
      have hrhoExtension :
          rhoH ∈ extensionSubgroup RH.field SH hSHH := by
        exact hrho
      have hrhoInternal :
          rhoH ∈ (localResidueDatum K).frobeniusFixedSubgroupWithin
            RH J₀ hJH sigmaH := by
        rw [← (localResidueDatum K).extensionSubgroup_frobeniusFixedField
          RH J₀ hJH sigmaH]
        exact hrhoExtension
      let tau :
          (intrinsicAbstractBase F).toSubgroup :=
        psi.symm rhoH
      have htauInternal :
          tau ∈ (localResidueDatum F).frobeniusFixedSubgroupWithin
            RF EI.field EI.below sigma :=
        (intrinsicFrobeniusFixedSubgroup_iff_ambientEmbeddedField
          K F E j e sigma tau).2 (by
            have hpsiApply :
                intrinsicBaseEquivAmbientEmbeddedField K F i e tau =
                  rhoH :=
              psi.apply_symm_apply rhoH
            rw [hpsiApply]
            simpa only [
              i, jF, jI, EI, H₀, J₀, hJH, RF, hHabsolute, H, RH,
              sigmaH] using hrhoInternal)
      have htauExtension :
          tau ∈ extensionSubgroup
            RF.field SF hSFB := by
        rw [(localResidueDatum F).extensionSubgroup_frobeniusFixedField
          RF EI.field EI.below sigma]
        exact htauInternal
      have hxfix : tau.1 x = x :=
        (IntermediateField.mem_fixedField_iff SF.toSubgroup x).1
          hx tau.1 htauExtension
      have hpsi : psi tau = rhoH :=
        psi.apply_symm_apply rhoH
      have hrhoeq : (psi tau).1 = rho :=
        congrArg Subtype.val hpsi
      calc
        rho (e x) = (psi tau).1.1 (e x) := by
          exact congrArg
            (fun g : Gal(SeparableClosure K / K) => g (e x))
            hrhoeq.symm
        _ = e (tau.1 x) := by
          rw [intrinsicBaseEquivAmbientEmbeddedField_apply_val,
            e.symm_apply_apply]
        _ = e x := congrArg e hxfix
    · intro hx
      rw [IntermediateField.mem_fixedField_iff]
      intro tau₀ htau₀
      let tau :
          (intrinsicAbstractBase F).toSubgroup :=
        ⟨tau₀, by
          rw [intrinsicAbstractBase,
            closedFixingSubgroup_bot_eq_baseField]
          exact Subgroup.mem_top _⟩
      have htauExtension :
          tau ∈ extensionSubgroup
            RF.field SF hSFB := by
        exact htau₀
      have htauInternal :
          tau ∈ (localResidueDatum F).frobeniusFixedSubgroupWithin
            RF EI.field EI.below sigma := by
        rw [← (localResidueDatum F).extensionSubgroup_frobeniusFixedField
          RF EI.field EI.below sigma]
        exact htauExtension
      have hrhoInternal :
          psi tau ∈ (localResidueDatum K).frobeniusFixedSubgroupWithin
            RH J₀ hJH sigmaH :=
        (intrinsicFrobeniusFixedSubgroup_iff_ambientEmbeddedField
          K F E j e sigma tau).1 htauInternal
      have hrhoExtension :
          psi tau ∈ extensionSubgroup RH.field SH hSHH := by
        rw [(localResidueDatum K).extensionSubgroup_frobeniusFixedField
          RH J₀ hJH sigmaH]
        exact hrhoInternal
      have hxfix : (psi tau).1.1 (e x) = e x :=
        (IntermediateField.mem_fixedField_iff SH.toSubgroup (e x)).1
          hx (psi tau).1 hrhoExtension
      apply e.injective
      calc
        e (tau₀ x) = e (tau.1 x) := rfl
        _ = (psi tau).1.1 (e x) := by
          rw [intrinsicBaseEquivAmbientEmbeddedField_apply_val,
            e.symm_apply_apply]
        _ = e x := hxfix
  exact {
    toFun := fun x =>
      ⟨e (x : SeparableClosure F),
        (hmem (x : SeparableClosure F)).1 x.property⟩
    invFun := fun y =>
      ⟨e.symm (y : SeparableClosure K),
        (hmem (e.symm (y : SeparableClosure K))).2
          (by
            rw [e.apply_symm_apply]
            exact y.property)⟩
    left_inv := fun x => by
      apply Subtype.ext
      exact e.symm_apply_apply (x : SeparableClosure F)
    right_inv := fun y => by
      apply Subtype.ext
      exact e.apply_symm_apply (y : SeparableClosure K)
    map_mul' := fun x y => by
      apply Subtype.ext
      exact e.map_mul (x : SeparableClosure F) (y : SeparableClosure F)
    map_add' := fun x y => by
      apply Subtype.ext
      exact e.map_add (x : SeparableClosure F) (y : SeparableClosure F)
    commutes' := fun x => by
      apply Subtype.ext
      exact e.commutes x }

end EmbeddedFrobeniusTransport

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_NormRestriction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionIsAlgebraic _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceExtensionCompletionAlgebra _root_.chosenFinitePlaceExtensionCompletionSMul _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsUltrametricDist _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Norm--restriction for finite-place Artin homomorphisms

This module proves norm--restriction naturality for finite-place Artin maps in an actual square of number fields and their chosen completed local extensions.
-/

open scoped Classical IsMulCommutative NNReal NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

section FinitePlaceNormRestrictionInstances

variable {K' L' : Type}
    [Field K'] [NumberField K']
    [Field L'] [NumberField L']
    [Algebra K K'] [Algebra K' L'] [Algebra K L']
    [IsScalarTower K K' L']
    [Algebra L L'] [IsScalarTower K L L']
    [IsAbelianGalois K' L']
    (v : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 K'))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (w' : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K' W) L')

local notation "vKₙ" =>
  NumberField.HeightOneSpectrum.adicAbv K v
local notation "vKₙ'" =>
  NumberField.HeightOneSpectrum.adicAbv K' W
local notation "Cₙ" =>
  finitePlaceNormCompletion K v
local notation "Dₙ" =>
  finitePlaceNormCompletion K' W
local notation "Eₙ" =>
  finitePlaceNormLocalizedCompletion K L v w
local notation "Eₙ'" =>
  finitePlaceNormLocalizedCompletion K' L' W w'

local instance finitePlaceNormLowerExtensionAlgebra_r27a6b5_1 :
    Algebra K w.1.Completion :=
  AbsoluteValue.extensionCompletionAlgebra
    (K := K) w.1
local instance finitePlaceNormLowerCompletionAlgebra_r27a6b5_1 :
    Algebra Cₙ w.1.Completion :=
  AbsoluteValue.completionAlgebra vKₙ w.1 w.2
local instance finitePlaceNormLowerGlobalAlgebra_r27a6b5_1 :
    Algebra K Eₙ :=
  LocalClassFieldTheory.localizedCompletionGlobalAlgebra vKₙ w
local instance finitePlaceNormUpperExtensionAlgebra_r27a6b5_1 :
    Algebra K' w'.1.Completion :=
  AbsoluteValue.extensionCompletionAlgebra
    (K := K') w'.1
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePlaceNormUpperCompletionAlgebra
local instance finitePlaceNormUpperGlobalAlgebra_r27a6b5_1 :
    Algebra K' Eₙ' :=
  LocalClassFieldTheory.localizedCompletionGlobalAlgebra vKₙ' w'
local instance finitePlaceNormLowerNontriviallyNormedField_r27a6b5_1 :
    NontriviallyNormedField Cₙ :=
  absoluteValueExtension_completionNontriviallyNormedField
    vKₙ (RayClass.adicAbv_isNontrivial v)
local instance finitePlaceNormLowerLocallyCompactSpace_r27a6b5_1 :
    LocallyCompactSpace Cₙ :=
  AbsoluteValue.Completion.locallyCompactSpace
    (finitePlaceCompletionBaseMap_isometry v)
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePlaceNormUpperNontriviallyNormedField
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePlaceNormUpperLocallyCompactSpace
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePlaceNormLowerLocalizedFiniteDimensional
local instance finitePlaceNormLowerLocalizedAbelianGalois_r27a6b5_1 :
    IsAbelianGalois Cₙ Eₙ :=
  LocalClassFieldTheory.localizedCompletion_isAbelianGalois
    vKₙ (RayClass.adicAbv_isNontrivial v) w
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePlaceNormUpperLocalizedFiniteDimensional
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePlaceNormUpperLocalizedAbelianGalois
local instance finitePlaceNormLowerUltrametric_r27a6b5_1 :
    IsUltrametricDist Cₙ :=
  finitePlaceArtinCompletionIsUltrametricDist vKₙ
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v)
local instance finitePlaceNormLowerValued_r27a6b5_1 :
    Valued Cₙ ℝ≥0 :=
  finitePlaceArtinCompletionValued vKₙ
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v)
local instance finitePlaceNormLowerValuationNontrivial_r27a6b5_1 :
    (Valued.v : Valuation Cₙ ℝ≥0).IsNontrivial :=
  (inferInstance :
    (NormedField.valuation (K := Cₙ)).IsNontrivial)
local instance finitePlaceNormLowerValuativeRel_r27a6b5_1 :
    ValuativeRel Cₙ :=
  finitePlaceArtinCompletionValuativeRel vKₙ
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v)
local instance finitePlaceNormLowerValuationCompatible_r27a6b5_1 :
    (Valued.v : Valuation Cₙ ℝ≥0).Compatible :=
  Valuation.Compatible.ofValuation
    (Valued.v : Valuation Cₙ ℝ≥0)
local instance finitePlaceNormLowerValuativeRelNontrivial_r27a6b5_1 :
    ValuativeRel.IsNontrivial Cₙ :=
  (ValuativeRel.isNontrivial_iff_isNontrivial
    (Valued.v : Valuation Cₙ ℝ≥0)).2 inferInstance
local instance finitePlaceNormLowerLocalField_r27a6b5_1 :
    IsNonarchimedeanLocalField Cₙ :=
  finitePlaceArtinCompletionIsNonarchimedeanLocalField vKₙ
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v)
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePlaceNormUpperUltrametric
local instance finitePlaceNormUpperValued_r27a6b5_1 :
    Valued Dₙ ℝ≥0 :=
  finitePlaceArtinCompletionValued vKₙ'
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K' W)
local instance finitePlaceNormUpperValuationNontrivial_r27a6b5_1 :
    (Valued.v : Valuation Dₙ ℝ≥0).IsNontrivial :=
  (inferInstance :
    (NormedField.valuation (K := Dₙ)).IsNontrivial)
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePlaceNormUpperValuativeRel
local instance finitePlaceNormUpperValuationCompatible_r27a6b5_1 :
    (Valued.v : Valuation Dₙ ℝ≥0).Compatible :=
  Valuation.Compatible.ofValuation
    (Valued.v : Valuation Dₙ ℝ≥0)
local instance finitePlaceNormUpperValuativeRelNontrivial_r27a6b5_1 :
    ValuativeRel.IsNontrivial Dₙ :=
  (ValuativeRel.isNontrivial_iff_isNontrivial
    (Valued.v : Valuation Dₙ ℝ≥0)).2 inferInstance
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePlaceNormUpperLocalField
noncomputable def finitePlaceNormRestrictedArtin
    [NumberField L]
    (hW : finitePlaceBelow (K := K) W = v)
    (hcentres :
      finitePlaceBelow (K := L)
          (finitePlaceExtensionCentre
            (K := K') (L := L') W w') =
        finitePlaceExtensionCentre
          (K := K) (L := L) v w)
    (y : Dₙˣ) :
    finitePlaceNormLocalizedAut K L v w := by
  exact
    finitePlaceCrossLocalRestrictionMonoidHom
      (K := K) (L := L) (K' := K') (L' := L')
      v W hW w w' hcentres
      (finitePlaceLocalArtinMonoidHom
        (K := K') (L := L') W w'
        (finitePlaceCompletionUnitsContinuousMulEquiv W y))

noncomputable def finitePlaceNormLowerArtin
    (hW : finitePlaceBelow (K := K) W = v)
    (y : Dₙˣ) :
    finitePlaceNormLocalizedAut K L v w := by
  exact
    finitePlaceLocalArtinMonoidHom
      (K := K) (L := L) v w
      (finitePlaceCompletionUnitsContinuousMulEquiv v
      (finitePlaceRelativeNormUnits
          (K := K) (K' := K') v W hW y))

theorem finitePlaceNormUpperArtin_eq_raw
    (y : Dₙˣ) :
    finitePlaceLocalArtinMonoidHom
        (K := K') (L := L') W w'
        (finitePlaceCompletionUnitsContinuousMulEquiv W y) =
      finitePlaceNormUpperRawArtin
        (K' := K') (L' := L') W w' y := by
  rw [
    finitePlaceLocalArtinMonoidHom_apply
      (K := K') (L := L') W w'
        (finitePlaceCompletionUnitsContinuousMulEquiv W y)]
  have hy :
      (↑(finitePlaceCompletionUnitsContinuousMulEquiv W) :
          Dₙˣ ≃* (W.adicCompletion K')ˣ).symm
          (finitePlaceCompletionUnitsContinuousMulEquiv W y) =
        y :=
    (finitePlaceCompletionUnitsContinuousMulEquiv W).symm_apply_apply y
  rw [hy]
  rfl

theorem finitePlaceNormLowerArtin_eq_raw
    (hW : finitePlaceBelow (K := K) W = v)
    (y : Dₙˣ) :
    finitePlaceNormLowerArtin
        (K := K) (L := L) (K' := K')
        v W w hW y =
      finitePlaceNormLowerRawArtin
        (K := K) (L := L) (K' := K')
        v W w hW y := by
  unfold finitePlaceNormLowerArtin
  rw [
    finitePlaceLocalArtinMonoidHom_apply
      (K := K) (L := L) v w
        (finitePlaceCompletionUnitsContinuousMulEquiv v
          (finitePlaceRelativeNormUnits
            (K := K) (K' := K') v W hW y))]
  have hy :
      (↑(finitePlaceCompletionUnitsContinuousMulEquiv v) :
          Cₙˣ ≃* (v.adicCompletion K)ˣ).symm
          (finitePlaceCompletionUnitsContinuousMulEquiv v
            (finitePlaceRelativeNormUnits
              (K := K) (K' := K') v W hW y)) =
        finitePlaceRelativeNormUnits
          (K := K) (K' := K') v W hW y :=
    (finitePlaceCompletionUnitsContinuousMulEquiv v).symm_apply_apply _
  rw [hy]
  rfl

end FinitePlaceNormRestrictionInstances

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_Core
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionIsAlgebraic _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.gLocallyCompact _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instLocallyCompactSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xLocallyCompact _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.chosenFinitePlaceBaseValuationIsNontrivial _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceExtensionCompletionAlgebra _root_.chosenFinitePlaceExtensionCompletionSMul _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsUltrametricDist _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Image and kernel of finite-place Artin homomorphisms

This module identifies the image with the chosen decomposition group and the kernel with the chosen local norm subgroup.
-/

open scoped Classical IsMulCommutative NNReal NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The kernel of the concrete finite-place Artin homomorphism is
exactly the chosen local norm subgroup. -/
theorem chosenFinitePlaceArtinMonoidHom_ker
    (v : HeightOneSpectrum (𝓞 K)) :
    MonoidHom.ker
        (chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v) =
      chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v := by
  let vK :=
    NumberField.HeightOneSpectrum.adicAbv K v
  let w :=
    chosenFinitePlaceExtension (L := L) v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let :=
    LocalClassFieldTheory.localizedCompletionGlobalAlgebra vK w
  let :=
    LocalClassFieldTheory.localizedCompletionIsScalarTower vK w
  let E :=
    AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  let : FiniteDimensional vK.Completion E :=
    AlgebraicNumberTheory.Valuations.localizedCompletionModuleFinite vK hvK w
  let : IsAbelianGalois vK.Completion E :=
    LocalClassFieldTheory.localizedCompletion_isAbelianGalois
      vK hvK w
  let : NontriviallyNormedField vK.Completion :=
    absoluteValueExtension_completionNontriviallyNormedField
      vK hvK
  let : LocallyCompactSpace vK.Completion :=
    AbsoluteValue.Completion.locallyCompactSpace
      (finitePlaceCompletionBaseMap_isometry v)
  let : IsUltrametricDist vK.Completion :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (AbsoluteValue.completionAbsoluteValue_isNonarchimedean
        vK
        (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv
          K v))
  let : Valued vK.Completion ℝ≥0 :=
    NormedField.toValued
  let vC : Valuation vK.Completion ℝ≥0 :=
    Valued.v
  let : vC.IsNontrivial :=
    (inferInstance :
      (NormedField.valuation
        (K := vK.Completion)).IsNontrivial)
  let : ValuativeRel vK.Completion :=
    ValuativeRel.ofValuation vC
  let : vC.Compatible :=
    Valuation.Compatible.ofValuation vC
  let : ValuativeRel.IsNontrivial vK.Completion :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vC).2
      inferInstance
  let : IsValuativeTopology vK.Completion :=
    isValuativeTopology_of_valued_ofValuation
      vK.Completion ℝ≥0
  let : IsNonarchimedeanLocalField vK.Completion :=
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }
  let eD :
      absoluteValueDecompositionGroup K w.1 ≃*
        (E ≃ₐ[vK.Completion] E) :=
    decompositionGroupEquivAlgebraicLocalizationAut
      vK hvK w
  let eK :
      vK.Completionˣ ≃* (v.adicCompletion K)ˣ :=
    finitePlaceCompletionUnitsContinuousMulEquiv v
  let localArtin :=
    LocalClassFieldTheory.abelianLocalArtinMonoidHom
      vK.Completion E
  change
    MonoidHom.ker
        ((absoluteValueDecompositionGroup K w.1).subtype.comp
          (eD.symm.toMonoidHom.comp
            (localArtin.comp eK.symm.toMonoidHom))) =
      (localNormSubgroup vK.Completion E).map
        eK.toMonoidHom
  apply SetLike.ext
  intro x
  constructor
  · intro hx
    change
      (absoluteValueDecompositionGroup K w.1).subtype
          (eD.symm (localArtin (eK.symm x))) = 1 at hx
    have hxSubgroup :
        eD.symm (localArtin (eK.symm x)) = 1 := by
      apply Subtype.coe_injective
      exact hx
    have hxLocal :
        localArtin (eK.symm x) = 1 := by
      apply eD.symm.injective
      simpa only [map_one] using hxSubgroup
    have hxKer :
        eK.symm x ∈ MonoidHom.ker localArtin :=
      hxLocal
    have hxNorm :
        eK.symm x ∈ localNormSubgroup vK.Completion E := by
      rw [
        LocalClassFieldTheory.abelianLocalArtinMonoidHom_ker
      ] at hxKer
      exact hxKer
    exact
      ⟨eK.symm x, hxNorm, eK.apply_symm_apply x⟩
  · rintro ⟨y, hy, rfl⟩
    have hyKer :
        y ∈ MonoidHom.ker localArtin := by
      rw [
        LocalClassFieldTheory.abelianLocalArtinMonoidHom_ker
      ]
      exact hy
    have hyArtin : localArtin y = 1 := hyKer
    change
      (absoluteValueDecompositionGroup K w.1).subtype
          (eD.symm (localArtin (eK.symm (eK y)))) = 1
    simp only [eK.symm_apply_apply, hyArtin, map_one]

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FiniteIdeleArtin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceGlobalArtinMonoidHom_finitePlaceIdele _root_.IdeleGroup.extension_finiteComponent _root_.IdeleGroup.extension_principalIdele _root_.IdeleGroup.extension_self _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk _root_.IdeleGroup.idealClass_classRepresentative _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleClassCongr_ideleClassNorm _root_.ideleClassCongr_mk _root_.ideleClassCongr_refl _root_.ideleClassExtension_mk _root_.ideleClassExtension_self _root_.ideleCongr_finiteComponent _root_.ideleCongr_principalIdele _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe _root_.intermediateClassNormQuotientBaseChangeMulEquiv_mk _root_.ordinaryIdeleClassNormQuotientCongrOfAlgEquiv_mk _root_.ordinaryIdeleClassNorm_relativeIdeleClassBaseChange _root_.relativeIdeleClassBaseChangeMulEquiv_classInclusion _root_.relativeIdeleClassBaseChangeMulEquiv_congrOfAlgEquiv _root_.relativeIdeleClassBaseChangeMulEquiv_mk _root_.relativeIdeleClassCongrOfAlgEquiv_ideleClassNorm _root_.relativeIdeleClassCongr_ideleClassNorm _root_.relativeIdeleCongr_norm _root_.towerRelativeIdeleViaOrdinaryMulEquiv_apply
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

/-- The finite local Artin factors of an idele have finite multiplicative
support.  This is the support input for applying homomorphisms to the
finite-place global Artin product. -/
theorem finitePlaceArtinFactors_hasFiniteMulSupport
    (a : IdeleGroup K) :
    HasFiniteMulSupport
      (fun v : HeightOneSpectrum (𝓞 K) =>
        chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v
          (IdeleGroup.finiteComponent v a)) := by
  let S : Set (HeightOneSpectrum (𝓞 K)) :=
    {v | a.2 v ∉ (v.adicCompletionIntegers K).units}
  let T : Set (HeightOneSpectrum (𝓞 K)) :=
    {v | ∃ W : HeightOneSpectrum (𝓞 L),
      W.asIdeal.LiesOver v.asIdeal ∧
        ¬ Algebra.IsUnramifiedAt (𝓞 K) W.asIdeal}
  have hS : S.Finite :=
    Filter.eventually_cofinite.mp
      (FiniteIdeleGroup.eventually_mem_localUnits a.2)
  have hT : T.Finite :=
    AlgebraicNumberTheory.Ramification.finite_ramified_base_heightOne_primes
      (𝓞 K) (𝓞 L)
  rw [HasFiniteMulSupport]
  apply (hS.union hT).subset
  rw [mulSupport_subset_iff']
  intro v hv
  have hvS : v ∉ S := by
    intro hvS
    exact hv (Set.mem_union_left T hvS)
  have hvT : v ∉ T := by
    intro hvT
    exact hv (Set.mem_union_right S hvT)
  have hNorm :
      IdeleGroup.finiteComponent v a ∈
        chosenFinitePlaceLocalNormSubgroup
          (K := K) (L := L) v := by
    apply
      adicCompletionIntegerUnits_le_chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v
        (chosenFinitePlaceIsUnramified_of_isUnramifiedAt
          (K := K) (L := L) v (by
            by_contra hram
            apply hvT
            change
              ∃ W : HeightOneSpectrum (𝓞 L),
                W.asIdeal.LiesOver v.asIdeal ∧
                  ¬ Algebra.IsUnramifiedAt
                    (𝓞 K) W.asIdeal
            exact
              ⟨finitePlaceExtensionCentre
                  (K := K) (L := L) v
                  (chosenFinitePlaceExtension
                    (L := L) v),
                finitePlaceExtensionCentre_liesOver
                  (K := K) (L := L) v
                  (chosenFinitePlaceExtension
                    (L := L) v),
                hram⟩))
    simpa only [S, Set.mem_ofPred_eq, not_not,
      IdeleGroup.finiteComponent_apply] using hvS
  rw [← chosenFinitePlaceArtinMonoidHom_ker
    (K := K) (L := L) v] at hNorm
  exact MonoidHom.mem_ker.mp hNorm

/-- At an unramified finite place, the chosen local Artin map kills
integral idele components. -/
theorem chosenFinitePlaceArtinMonoidHom_eq_one_of_integral_of_unramifiedAt
    (v : HeightOneSpectrum (𝓞 K))
    (a : IdeleGroup K)
    (ha :
      IdeleGroup.finiteComponent v a ∈
        (v.adicCompletionIntegers K).units)
    (hunram :
      Algebra.IsUnramifiedAt (𝓞 K)
        (finitePlaceExtensionCentre
          (K := K) (L := L) v
          (chosenFinitePlaceExtension
            (L := L) v)).asIdeal) :
    chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v
        (IdeleGroup.finiteComponent v a) = 1 := by
  have hNorm :
      IdeleGroup.finiteComponent v a ∈
        chosenFinitePlaceLocalNormSubgroup
          (K := K) (L := L) v := by
    apply
      adicCompletionIntegerUnits_le_chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v
        (chosenFinitePlaceIsUnramified_of_isUnramifiedAt
          (K := K) (L := L) v hunram)
    exact ha
  rw [← chosenFinitePlaceArtinMonoidHom_ker
    (K := K) (L := L) v] at hNorm
  exact MonoidHom.mem_ker.mp hNorm

theorem chosenFinitePlaceArtinMonoidHom_eq_one_of_mem_localNorm
    (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ)
    (hx : x ∈ chosenFinitePlaceLocalNormSubgroup
      (K := K) (L := L) v) :
    chosenFinitePlaceArtinMonoidHom (K := K) (L := L) v x = 1 := by
  rw [← chosenFinitePlaceArtinMonoidHom_ker
    (K := K) (L := L) v] at hx
  exact MonoidHom.mem_ker.mp hx

/-- The product over all finite places of the actual local Artin
homomorphisms.  Its value on an idele is a finite product because the
idele is locally integral almost everywhere and the extension is
unramified away from a finite set. -/
noncomputable def finitePlaceGlobalArtinMonoidHom :
    IdeleGroup K →* (L ≃ₐ[K] L) where
  toFun a :=
    ∏ᶠ v : HeightOneSpectrum (𝓞 K),
      chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v
        (IdeleGroup.finiteComponent v a)
  map_one' := by
    simp only [map_one]
    exact finprod_one
  map_mul' a b := by
    simp only [map_mul]
    exact
      finprod_mul_distrib
        (finitePlaceArtinFactors_hasFiniteMulSupport
          (K := K) (L := L) a)
        (finitePlaceArtinFactors_hasFiniteMulSupport
          (K := K) (L := L) b)

/-- The finite Artin product after an idele norm is the `finprod`, over
base finite places, of the products of the corresponding local norm
factors at all finite places upstairs. -/
theorem finitePlaceGlobalArtinMonoidHom_norm_eq_finprod_fibers
    {M : Type}
    [Field M] [NumberField M] [Algebra K M]
    (a : IdeleGroup M) :
    letI : ∀ v : HeightOneSpectrum (𝓞 K),
        Fintype {W : HeightOneSpectrum (𝓞 M) //
          finitePlaceBelow (K := K) W = v} :=
      fun v => by
        let vK := HeightOneSpectrum.adicAbv K v
        let hvK : vK.IsNontrivial :=
          RayClass.adicAbv_isNontrivial v
        letI :=
          completionTensorDecomposition_extensionFintype
            (K := K) (L := M) vK hvK
        exact
          Fintype.ofEquiv (AbsoluteValueExtension vK M)
            (finitePlaceExtensionEquivAbove
              (K := K) (L := M) v)
    letI : ∀ v : HeightOneSpectrum (𝓞 K),
        ∀ W : {W : HeightOneSpectrum (𝓞 M) //
          finitePlaceBelow (K := K) W = v},
          Algebra (v.adicCompletion K)
            (W.1.adicCompletion M) :=
      fun v W =>
        (finitePlaceAdicCompletionMap
          K M v W).toAlgebra
    finitePlaceGlobalArtinMonoidHom
        (K := K) (L := L)
        (IdeleGroup.norm K M a) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K),
        ∏ W : {W : HeightOneSpectrum (𝓞 M) //
            finitePlaceBelow (K := K) W = v},
          chosenFinitePlaceArtinMonoidHom
            (K := K) (L := L) v
            (LocalFieldTheory.normUnits
              (v.adicCompletion K)
              (W.1.adicCompletion M)
              (IdeleGroup.finiteComponent W.1 a)) := by
  classical
  let : ∀ v : HeightOneSpectrum (𝓞 K),
      Fintype {W : HeightOneSpectrum (𝓞 M) //
        finitePlaceBelow (K := K) W = v} :=
    fun v => by
      let vK := HeightOneSpectrum.adicAbv K v
      let hvK : vK.IsNontrivial :=
        RayClass.adicAbv_isNontrivial v
      letI :=
        completionTensorDecomposition_extensionFintype
          (K := K) (L := M) vK hvK
      exact
        Fintype.ofEquiv (AbsoluteValueExtension vK M)
          (finitePlaceExtensionEquivAbove
            (K := K) (L := M) v)
  let : ∀ v : HeightOneSpectrum (𝓞 K),
      ∀ W : {W : HeightOneSpectrum (𝓞 M) //
        finitePlaceBelow (K := K) W = v},
        Algebra (v.adicCompletion K)
          (W.1.adicCompletion M) :=
    fun v W =>
      (finitePlaceAdicCompletionMap
        K M v W).toAlgebra
  rw [finitePlaceGlobalArtinMonoidHom]
  apply finprod_congr
  intro v
  rw [IdeleGroup.finiteComponent_norm_eq_prod]
  rw [map_prod]

theorem finitePlaceNormArtinFactor_eq_one_of_component_unit_of_unramified
    {M : Type}
    [Field M] [NumberField M] [Algebra K M]
    (a : IdeleGroup M)
    (W : HeightOneSpectrum (𝓞 M))
    (hComponentUnit :
      IdeleGroup.finiteComponent W a ∈
        (W.adicCompletionIntegers M).units)
    (hunram : ChosenFinitePlaceIsUnramified
      (K := K) (L := L) (finitePlaceBelow (K := K) W)) :
    let v := finitePlaceBelow (K := K) W
    letI : Algebra (v.adicCompletion K) (W.adicCompletion M) :=
      (finitePlaceAdicCompletionMap K M v ⟨W, rfl⟩).toAlgebra
    chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v
        (LocalFieldTheory.normUnits
          (v.adicCompletion K)
          (W.adicCompletion M)
          (IdeleGroup.finiteComponent W a)) = 1 := by
  let v := finitePlaceBelow (K := K) W
  let Wv :
      {Q : HeightOneSpectrum (𝓞 M) //
        finitePlaceBelow (K := K) Q = v} :=
    ⟨W, rfl⟩
  let z : (W.adicCompletionIntegers M).units :=
    ⟨IdeleGroup.finiteComponent W a, hComponentUnit⟩
  let : Algebra (v.adicCompletion K) (W.adicCompletion M) :=
    (finitePlaceAdicCompletionMap K M v Wv).toAlgebra
  have hNormUnit :
      LocalFieldTheory.normUnits
          (v.adicCompletion K)
          (W.adicCompletion M)
          (IdeleGroup.finiteComponent W a) ∈
        (v.adicCompletionIntegers K).units := by
    simpa only [z, Subgroup.coe_subtype] using
      IdeleGroup.finitePlace_normUnits_mem_integerUnits
        (K := K) (L := M) v Wv z
  apply
    chosenFinitePlaceArtinMonoidHom_eq_one_of_mem_localNorm
      (K := K) (L := L) v
  apply
    adicCompletionIntegerUnits_le_chosenFinitePlaceLocalNormSubgroup
      (K := K) (L := L) v hunram
  exact hNormUnit

/-- On an idele supported at one finite place, the finite global product
is exactly that local Artin factor. -/
@[simp]
theorem finitePlaceGlobalArtinMonoidHom_finitePlaceIdele
    (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    finitePlaceGlobalArtinMonoidHom
        (K := K) (L := L)
        (finitePlaceIdele v x) =
      chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v x := by
  change
    (∏ᶠ w : HeightOneSpectrum (𝓞 K),
      chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) w
        (IdeleGroup.finiteComponent w (finitePlaceIdele v x))) =
      chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v x
  rw [finprod_eq_single _ v]
  · rw [finitePlaceIdele_finiteComponent_same]
  · intro w hw
    rw [finitePlaceIdele_finiteComponent_of_ne v w x hw,
      map_one]

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_GlobalArtin
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# The preliminary global Artin homomorphism

For a finite abelian extension `L / K`, the global norm-residue symbol
on ideles is the product of its archimedean and finite-place local
Artin factors.
-/

open scoped BigOperators Classical IsMulCommutative NumberField
  NumberField.LiesOver
open NumberField IsDedekindDomain
open IdeleGroup RelativeIdeleGroup

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]

/-- The preliminary global Artin homomorphism
`[·, L / K] : I_K → Gal(L / K)`, defined as the product of all local
Artin homomorphisms. -/
noncomputable def globalArtinMonoidHom :
    IdeleGroup K →* (L ≃ₐ[K] L) :=
  infinitePlaceGlobalArtinMonoidHom
      (K := K) (L := L) *
    finitePlaceGlobalArtinMonoidHom
      (K := K) (L := L)

/-- The preliminary global Artin symbol is the product of its actual
archimedean and finite local factors. -/
theorem globalArtinMonoidHom_apply
    (a : IdeleGroup K) :
    globalArtinMonoidHom (K := K) (L := L) a =
      (∏ v : InfinitePlace K,
        chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L) v
          (IdeleGroup.infiniteComponent v a)) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K),
        chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v
          (IdeleGroup.finiteComponent v a) := by
  change
    infinitePlaceGlobalArtinMonoidHom
          (K := K) (L := L) a *
        finitePlaceGlobalArtinMonoidHom
          (K := K) (L := L) a = _
  unfold infinitePlaceGlobalArtinMonoidHom
  rw [MonoidHom.finsetProd_apply]
  rfl

/-- The preliminary global Artin homomorphism of `L / K` kills every
actual relative-idele norm from `L`.  At each finite and infinite place
this is exactly the corresponding local reciprocity kernel theorem. -/
@[simp]
theorem globalArtinMonoidHom_relativeIdeleNorm_eq_one
    (z : RelativeIdeleGroup K L) :
    globalArtinMonoidHom
        (K := K) (L := L)
        (RelativeIdeleGroup.norm K L z) =
      1 := by
  rw [globalArtinMonoidHom_apply]
  have hnorm :
      RelativeIdeleGroup.norm K L z ∈
        (RelativeIdeleGroup.norm K L).range :=
    ⟨z, rfl⟩
  have hinfinite :
      (∏ v : InfinitePlace K,
        chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L) v
          (IdeleGroup.infiniteComponent v
            (RelativeIdeleGroup.norm K L z))) =
        1 := by
    apply Finset.prod_eq_one
    intro v _
    apply MonoidHom.mem_ker.mp
    rw [chosenInfinitePlaceArtinMonoidHom_ker
      (K := K) (L := L) v]
    exact
      _root_.infiniteComponent_mem_infiniteTensorNormSubgroup_of_mem_relativeNorm_range
          (K := K) (L := L)
          (RelativeIdeleGroup.norm K L z) hnorm v
  have hfinite :
      (∏ᶠ v : HeightOneSpectrum (𝓞 K),
        chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v
          (IdeleGroup.finiteComponent v
            (RelativeIdeleGroup.norm K L z))) =
        1 := by
    apply finprod_eq_one_of_forall_eq_one
    intro v
    apply MonoidHom.mem_ker.mp
    rw [chosenFinitePlaceArtinMonoidHom_ker
      (K := K) (L := L) v]
    exact
      _root_.relativeIdeleNorm_finiteComponent_mem_chosenLocalNormSubgroup
          (K := K) (L := L) v z
  rw [hinfinite, hfinite, mul_one]

/-- The preliminary global Artin homomorphism kills the ordinary idele
norm `N_{L/K} : I_L → I_K`.  This is the relative-idele kernel theorem
above, transported by the canonical scalar-extension equivalence used in
the definition of `IdeleGroup.norm`. -/
@[simp]
theorem globalArtinMonoidHom_ideleNorm_eq_one
    (a : IdeleGroup L) :
    globalArtinMonoidHom
        (K := K) (L := L)
        (IdeleGroup.norm K L a) =
      1 := by
  change
    globalArtinMonoidHom
        (K := K) (L := L)
        (RelativeIdeleGroup.norm K L
          ((relativeIdeleBaseChangeMulEquiv
            (K := K) (L := L)).symm a)) =
      1
  exact
    globalArtinMonoidHom_relativeIdeleNorm_eq_one
      (K := K) (L := L)
      ((relativeIdeleBaseChangeMulEquiv
        (K := K) (L := L)).symm a)

/-- The global Artin symbol of an archimedean one-place idele is its
local infinite-place Artin symbol. -/
@[simp]
theorem globalArtinMonoidHom_infinitePlaceIdele
    (v : InfinitePlace K)
    (x : v.Completionˣ) :
    globalArtinMonoidHom
        (K := K) (L := L)
        (infinitePlaceIdele v x) =
      chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := L) v x := by
  classical
  change
    infinitePlaceGlobalArtinMonoidHom
          (K := K) (L := L) (infinitePlaceIdele v x) *
        finitePlaceGlobalArtinMonoidHom
          (K := K) (L := L) (infinitePlaceIdele v x) =
      chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := L) v x
  have hinfinite :
      infinitePlaceGlobalArtinMonoidHom
          (K := K) (L := L) (infinitePlaceIdele v x) =
        chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L) v x := by
    unfold infinitePlaceGlobalArtinMonoidHom
    rw [MonoidHom.finsetProd_apply, Finset.prod_eq_single v]
    · rw [MonoidHom.comp_apply,
        infinitePlaceIdele_infiniteComponent_same]
    · intro w _ hwv
      rw [MonoidHom.comp_apply,
        infinitePlaceIdele_infiniteComponent_of_ne v w x hwv,
        map_one]
    · intro hv
      exact (hv (Finset.mem_univ v)).elim
  have hfinite :
      finitePlaceGlobalArtinMonoidHom
          (K := K) (L := L) (infinitePlaceIdele v x) =
        1 := by
    change
      (∏ᶠ w : HeightOneSpectrum (𝓞 K),
        chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) w
          (IdeleGroup.finiteComponent w
            (infinitePlaceIdele v x))) = 1
    apply finprod_eq_one_of_forall_eq_one
    intro w
    rw [infinitePlaceIdele_finiteComponent, map_one]
  rw [hinfinite, hfinite, mul_one]

/-- The global Artin symbol of a finite one-place idele is its local
finite-place Artin symbol. -/
@[simp]
theorem globalArtinMonoidHom_finitePlaceIdele
    (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    globalArtinMonoidHom
        (K := K) (L := L)
        (finitePlaceIdele v x) =
      chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v x := by
  change
    infinitePlaceGlobalArtinMonoidHom
          (K := K) (L := L) (finitePlaceIdele v x) *
        finitePlaceGlobalArtinMonoidHom
          (K := K) (L := L) (finitePlaceIdele v x) =
      chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v x
  rw [infinitePlaceGlobalArtinMonoidHom_finitePlaceIdele,
    finitePlaceGlobalArtinMonoidHom_finitePlaceIdele, one_mul]

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_ChangedUniformizerIntertwiner_IntertwinerConstruction
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextFieldAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadicTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateUnitParameter_commGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

theorem padicChangedUniformizerIntertwiner_coeff_eq_approximation
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    (q a : ℕ) (hq : q < a + 2) :
    PowerSeries.coeff q
        (padicChangedUniformizerIntertwiner p u) =
      PowerSeries.coeff q
        (padicChangedUniformizerApproximation p u a).series := by
  rw [padicChangedUniformizerIntertwiner_coeff]
  by_cases hqa : q ≤ a
  · exact
      (padicChangedUniformizerApproximation_coeff_eq_of_le
        p u q (a := q) (b := a) hqa (by omega)).symm
  · have haq : a + 1 = q := by omega
    subst q
    rw [padicChangedUniformizerApproximation_coeff_succ_eq_of_lt
      p u a (a + 1) (by omega)]

end LubinTate

end
end


