-- Prove2me | Definitions.Def_OAIQ244Duke088
-- name    : OAIQ244Duke088
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-14T00:38:23.626625+00:00
-- url     : https://prove2.me/theorems/fb487660-7bb6-42ed-9636-36175201d0de
-- title:
--   Definitions bundle OAIQ244Duke088 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 16 declarations of OpenAI's Lean: 2 definitions, 2 instances and 12 theorems. The definitions and types are `GlobalClassFieldTheory.Reciprocity.cyclotomicZHatIntersectionDegree`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleValue`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `GlobalClassFieldTheory_Reciprocity_CyclotomicIdeleValue`, `GlobalClassFieldTheory_Reciprocity_CyclotomicZHatBaseChange`, `GlobalClassFieldTheory_Reciprocity_FiniteIdeleArtin`, `GlobalClassFieldTheory_Reciprocity_InfiniteGlobalArtin`, `LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_AmbientNormResidue`, `LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_AmbientPrimeComparison`, `LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_AmbientPrimeWitnessComparison`, `LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_NormRestriction`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke084` and `OAIQ244Duke085` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke093` and `OAIQ244Duke117`.
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
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Hom.Instances
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
import Mathlib.Data.ZMod.QuotientRing
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
import Mathlib.FieldTheory.Galois.Notation
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic
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
import Mathlib.GroupTheory.Torsion
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
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
import Mathlib.NumberTheory.NumberField.Completion.Ramification
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
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
import Definitions.Def_OAIQ244Duke084
import Definitions.Def_OAIQ244Duke085

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicZHatBaseChange
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option synthInstance.maxHeartbeats 400000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Base change of the rational cyclotomic `ZHat`-extension

The rational cyclotomic `ZHat`-extension lives inside the fixed separable
closure of `ℚ`.  To form its compositum with an arbitrary number field, we first
embed that number field into the same separable closure.  The
intersection degree below is the normalization integer

`f_K = [K ∩ ℚ̃ : ℚ]`.

All fields in this file are the actual mathlib intermediate fields in
`SeparableClosure ℚ`; no abstract copy of the compositum or of its
Galois group is introduced.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open scoped Topology
open AlgebraicNumberTheory
open ClassFormation
open KummerTheory

variable (K : Type*) [Field K] [NumberField K]

/-- The cyclotomic intersection degree
`f_K = [K ∩ ℚ̃ : ℚ]`. -/
noncomputable def cyclotomicZHatIntersectionDegree : ℕ :=
  Module.finrank ℚ (numberFieldCyclotomicZHatIntersection K)

/-- The intersection degree divides the absolute degree of the number
field. -/
theorem cyclotomicZHatIntersectionDegree_dvd_finrank :
    cyclotomicZHatIntersectionDegree K ∣
      Module.finrank ℚ K := by
  have h :
      Module.finrank ℚ
          (numberFieldCyclotomicZHatIntersection K) ∣
        Module.finrank ℚ
          (numberFieldInRationalSeparableClosure K) :=
    IntermediateField.finrank_dvd_of_le_right
      (show
        numberFieldCyclotomicZHatIntersection K ≤
          numberFieldInRationalSeparableClosure K from
        inf_le_left)
  rw [numberFieldInRationalSeparableClosure] at h
  rw [←
    ((numberFieldSeparableClosureEmbedding K).equivFieldRange.toLinearEquiv).finrank_eq] at h
  simpa only [cyclotomicZHatIntersectionDegree] using h

instance
    numberFieldCyclotomicZHatFiniteLayerInCompositum_scalarTower
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsScalarTower ℚ K
      (numberFieldCyclotomicZHatFiniteLayerInCompositum K E) := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  apply Subtype.ext
  change algebraMap ℚ (numberFieldCyclotomicZHatCompositum K) x =
    algebraMap K (numberFieldCyclotomicZHatCompositum K)
      (algebraMap ℚ K x)
  exact
    IsScalarTower.algebraMap_apply
      ℚ K (numberFieldCyclotomicZHatCompositum K) x

instance
    rationalCyclotomicZHatFiniteLayerInCompositum_scalarTower
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsScalarTower ℚ E
      (numberFieldCyclotomicZHatFiniteLayerInCompositum K E) :=
  IsScalarTower.of_algebraMap_eq'
    (AlgHom.comp_algebraMap
      (rationalCyclotomicZHatFiniteLayerInCompositumEmbedding K E)).symm

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_AmbientNormResidue
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalClosedSubgroupQuotientFintype _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerInCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
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

namespace AmbientEmbeddedFixedFieldPresentation

/-- The presentation-level evaluation formula for the ambient norm-residue
value.  It exposes only the actual finite quotient equivalences carried by
the presentation. -/
theorem normResidueAbelianElement_apply
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
    (a : Fˣ) :
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
    P.normResidueAbelianElement a =
      P.quotientEquiv.abelianizationCongr
        (P.fixedFieldQuotientEquiv.abelianizationCongr.symm
          (Additive.toMul
            (abstractFixedFieldNormResidueSymbol
              K (SeparableClosure K)
              (localResidueDatum K)
              (localHenselianValuation K)
              (separableClosureUnits_isClassFormation K)
              P.base.field P.extension.field P.extension.below
              (Additive.ofMul
                (Units.mapEquiv P.baseEquiv.toMulEquiv a))))) :=
  rfl

end AmbientEmbeddedFixedFieldPresentation

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_AmbientPrimeWitnessComparison
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalClosedSubgroupQuotientFintype _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerInCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerInCompositum_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteUnramifiedNormQuotient _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.Padic.padicUnitFiniteFactor_finite _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.RayClass.Modulus.congruenceSubgroup_normal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.ideleGroupIsTopologicalGroup _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
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

/-- The chosen ambient prime witness maps to the prescribed abelianized
Galois element under the concrete local Artin map. -/
theorem
    ambientEmbeddedPrimeWitness_local
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
    localArtinMonoidHom F E
        (ambientEmbeddedPrimeWitness K F E j e z) =
      z := by
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
  let SF :=
    (localResidueDatum F).frobeniusFixedField
      RF EI.field EI.below sigma
  let hSFB :=
    (localResidueDatum F).frobeniusFixedField_le
      RF EI.field EI.below sigma
  let hSFabsolute :=
    (localResidueDatum F).frobeniusFixedField_absoluteFinite
      (intrinsicFiniteAbstractBase F) EI.field EI.below sigma
  let hSFfinite :=
    (localResidueDatum F).frobeniusFixedField_finite
      RF EI.field EI.below sigma
  let _hSFFinite : Finite
      ((intrinsicAbstractBase F).toSubgroup ⧸
        extensionSubgroup
          (intrinsicAbstractBase F) SF hSFB) := by
    change Finite
      (RF.field.toSubgroup ⧸
        extensionSubgroup RF.field SF hSFB)
    exact hSFfinite
  let SigmaF : FiniteAbstractField
      Gal(SeparableClosure F / F) :=
    ⟨SF, hSFabsolute⟩
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
  let : FiniteDimensional F
      (abstractFixedField F (SeparableClosure F) SF) :=
    abstractFixedField_finiteDimensional
      F (SeparableClosure F) SF hSFabsolute
  let : NontriviallyNormedField
      (abstractFixedField F (SeparableClosure F) SF) :=
    finiteExtensionSpectralNormedField
      F (abstractFixedField F (SeparableClosure F) SF)
  let : ValuativeRel
      (abstractFixedField F (SeparableClosure F) SF) :=
    finiteExtensionSpectralValuativeRel
      F (abstractFixedField F (SeparableClosure F) SF)
  let : IsNonarchimedeanLocalField
      (abstractFixedField F (SeparableClosure F) SF) :=
    finiteExtensionSpectralIsNonarchimedeanLocalField
      F (abstractFixedField F (SeparableClosure F) SF)
  let : Valuation.HasExtension
      (ValuativeRel.valuation F)
      (ValuativeRel.valuation
        (abstractFixedField F (SeparableClosure F) SF)) :=
    finiteExtensionSpectralValuation_hasExtension
      F (abstractFixedField F (SeparableClosure F) SF)
  let : FiniteDimensional K LH :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) SH hSHabsolute
  let iH : LH →ₐ[K] SeparableClosure K :=
    LH.val.restrictScalars K
  let : Algebra.IsSeparable K LH := by
    let : IsScalarTower K LH (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq' (by
        apply RingHom.ext
        intro x
        exact (iH.commutes x).symm)
    exact
      Algebra.isSeparable_tower_bot_of_isSeparable
        K LH (SeparableClosure K)
  let : NontriviallyNormedField LH :=
    finiteExtensionSpectralNormedField K LH
  let : ValuativeRel LH :=
    finiteExtensionSpectralValuativeRel K LH
  let : IsNonarchimedeanLocalField LH :=
    finiteExtensionSpectralIsNonarchimedeanLocalField K LH
  let : Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation LH) :=
    finiteExtensionSpectralValuation_hasExtension K LH
  have hsourceRing :
      (localSeparableValuationSubring F).comap LF.val.toRingHom =
        (ValuativeRel.valuation LF).valuationSubring :=
    localSeparableValuationSubring_comap_embedding F LF LF.val
  have htargetRing :
      (localSeparableValuationSubring K).comap iH.toRingHom =
        (ValuativeRel.valuation LH).valuationSubring :=
    localSeparableValuationSubring_comap_embedding K LH iH
  have hmem (x : LF) :
      x ∈ (ValuativeRel.valuation LF).valuationSubring ↔
        phi x ∈ (ValuativeRel.valuation LH).valuationSubring := by
    rw [← hsourceRing, ← htargetRing]
    change
      (x : SeparableClosure F) ∈ localSeparableValuationSubring F ↔
        ((phi x : LH) : SeparableClosure K) ∈
          localSeparableValuationSubring K
    rw [hphi x]
    have hvaluation :=
      localSeparableValuationSubring_eq_comap_finiteExtensionEquiv
        K F i e
    rw [hvaluation]
    rfl
  let pF :=
    chosenValuationOneUnitOfRingEquiv LF LH phi hmem
  have hpFvalue :=
    chosenValuationOneUnitOfRingEquiv_source LF LH phi hmem
  let piF : ambientFixedAddSubgroup
      (intrinsicAbsoluteUnits F) SF :=
    abstractFixedFieldUnitsEquivGaloisFixed
      F (SeparableClosure F) SF
        (Additive.ofMul pF)
  have hpiF :
      (localHenselianValuation F).IsPrimeElement SigmaF piF := by
    exact
      localHenselianValuation_isPrimeElement_abstractFixedField
        F SigmaF pF hpFvalue
  let xPrime : Fˣ :=
    normUnits F LF pF
  have hnormF :
      relativeNorm (intrinsicAbsoluteUnits F)
          (intrinsicAbstractBase F) SF hSFB piF =
        baseUnitsEquivGaloisAmbientFixed F (SeparableClosure F)
          (Additive.ofMul xPrime) := by
    exact
      relativeNorm_intrinsicAbstractBase_abstractFixedFieldUnit
        F SF hSFB pF
  have hconcretePrime :
      concreteNormResidueSymbolOfEmbedding
          F E jI
          (localResidueDatum F)
          (localHenselianValuation F)
          (separableClosureUnits_isClassFormation F) xPrime =
        Abelianization.of (qF q) := by
    have hprime :=
      concreteNormResidueSymbolOfEmbedding_apply_primeNorm
        F E jI
        (localResidueDatum F)
        (localHenselianValuation F)
        (separableClosureUnits_isClassFormation F)
        q sigma hsigma piF hpiF xPrime
        (by
          simpa only [RF, SF, hSFB] using hnormF.symm)
    exact hprime
  have hqz :
      qF.abelianizationCongr (Abelianization.of q) = z := by
    calc
      qF.abelianizationCongr (Abelianization.of q) =
          qF.abelianizationCongr zF :=
        congrArg qF.abelianizationCongr hq
      _ = z :=
        qF.abelianizationCongr.apply_symm_apply z
  have hconcretePrimeZ :
      concreteNormResidueSymbolOfEmbedding
          F E jI
          (localResidueDatum F)
          (localHenselianValuation F)
          (separableClosureUnits_isClassFormation F) xPrime = z := by
    rw [hconcretePrime, ← hqz]
    exact (abelianizationCongr_of qF q).symm
  have hxWitness :
      ambientEmbeddedPrimeWitness K F E j e z = xPrime := by
    rfl
  rw [hxWitness]
  exact
    (DFunLike.congr_fun
      (localArtinMonoidHom_eq_of_embedding F E jI) xPrime).trans
      hconcretePrimeZ

/-- The chosen prime witness satisfies the ambient fixed-field
norm-residue symbol formula. -/
theorem
    ambientEmbeddedPrimeWitness_symbol
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
    ambientEmbeddedPrimeSymbolProperty K F E j e z := by
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
  let F₀ :=
    abstractFixedField K (SeparableClosure K) H₀
  have hfixed :
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
  let hSHfinite :=
    (localResidueDatum K).frobeniusFixedField_finite
      RH J₀ hJH sigmaH
  let _hSHFinite : Finite
      (H₀.toSubgroup ⧸
        extensionSubgroup H₀ SH hSHH) := by
    change Finite
      (RH.field.toSubgroup ⧸
        extensionSubgroup RH.field SH hSHH)
    exact hSHfinite
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
  have hphiComm :
      RingHom.comp (algebraMap F₀ LH) phiF.toRingEquiv.toRingHom =
        RingHom.comp phi.toRingHom
          (algebraMap F LF) := by
    let : Algebra F LH := iLH.toRingHom.toAlgebra
    let phiAlg :=
      intrinsicFrobeniusFixedFieldEquivAmbientEmbeddedField
        K F E j e sigma
    apply RingHom.ext
    intro x
    change
      algebraMap F₀ LH (phiF x) =
        phiAlg (algebraMap F LF x)
    calc
      algebraMap F₀ LH (phiF x) =
          algebraMap F LH x := by
        apply LH.val.injective
        rfl
      _ = phiAlg (algebraMap F LF x) :=
        (phiAlg.commutes x).symm
  let : FiniteDimensional F LF :=
    abstractFixedField_finiteDimensional
      F (SeparableClosure F) SF hSFabsolute
  let : NontriviallyNormedField LF :=
    finiteExtensionSpectralNormedField F LF
  let : ValuativeRel LF :=
    finiteExtensionSpectralValuativeRel F LF
  let : IsNonarchimedeanLocalField LF :=
    finiteExtensionSpectralIsNonarchimedeanLocalField F LF
  let : Valuation.HasExtension
      (ValuativeRel.valuation F) (ValuativeRel.valuation LF) :=
    finiteExtensionSpectralValuation_hasExtension F LF
  let : FiniteDimensional K LH :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) SH hSHabsolute
  let : FiniteDimensional K F₀ :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) H₀ hHabsolute
  let hF₀LHFinite : FiniteDimensional F₀ LH :=
    abstractRelativeFixedField_finiteDimensional
      K (SeparableClosure K) H₀ SH hSHH hHabsolute _hSHFinite
  let iH : LH →ₐ[K] SeparableClosure K :=
    LH.val.restrictScalars K
  let : Algebra.IsSeparable K LH := by
    let : IsScalarTower K LH (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq' (by
        apply RingHom.ext
        intro x
        exact (iH.commutes x).symm)
    exact
      Algebra.isSeparable_tower_bot_of_isSeparable
        K LH (SeparableClosure K)
  let hLHNorm : NontriviallyNormedField LH :=
    finiteExtensionSpectralNormedField K LH
  let hLHVal : ValuativeRel LH :=
    finiteExtensionSpectralValuativeRel K LH
  let hLHLocal : IsNonarchimedeanLocalField LH :=
    finiteExtensionSpectralIsNonarchimedeanLocalField K LH
  let : Valuation.HasExtension
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
  let xPrime : Fˣ :=
    normUnits F LF pF
  let xPrime0 : F₀ˣ :=
    Units.mapEquiv phiF.toMulEquiv xPrime
  have hxWitness :
      ambientEmbeddedPrimeWitness K F E j e z = xPrime := by
    rfl
  have hpHvalue :=
    chosenValuationOneUnitOfRingEquiv_target LF LH phi hmem
  let pH : LHˣ :=
    Units.mapEquiv phi.toMulEquiv pF
  change
    IsNonarchimedeanLocalField.valuationMap LH
      (Additive.ofMul pH) = 1 at hpHvalue
  let SigmaH : FiniteAbstractField
      Gal(SeparableClosure K / K) :=
    ⟨SH, hSHabsolute⟩
  let piH : ambientFixedAddSubgroup
      (galoisAmbientUnitsRep K (SeparableClosure K)) SH :=
    abstractRelativeFixedFieldUnitsEquivGaloisFixed
      K (SeparableClosure K) H₀ SH hSHH
        (Additive.ofMul pH)
  have hpiH :
      (localHenselianValuation K).IsPrimeElement SigmaH piH := by
    exact
      localHenselianValuation_isPrimeElement_abstractFixedField
        K SigmaH pH hpHvalue
  have hambientPrime :
      abstractFixedFieldNormResidueSymbol
          K (SeparableClosure K)
          (localResidueDatum K)
          (localHenselianValuation K)
          (separableClosureUnits_isClassFormation K)
          H₀ J₀ hJH (Additive.ofMul xPrime0) =
        Additive.ofMul
          (q₀.abelianizationCongr
            (Abelianization.of qAmbient)) := by
    exact
      abstractFixedFieldNormResidueSymbol_eq_of_transportedValuationOneUnit
        K F LF H J₀ hJH sigmaH
          (_hLHNorm := hLHNorm)
          (_hLHVal := hLHVal)
          (_hLHLocal := hLHLocal)
          (_hF₀LHFinite := hF₀LHFinite)
          phiF.toRingEquiv phi hphiComm hmem hpiH
  have hxPrime0 :
      Units.mapEquiv phiF.toMulEquiv
          (ambientEmbeddedPrimeWitness K F E j e z) =
        xPrime0 := by
    exact congrArg
      (Units.mapEquiv phiF.toMulEquiv) hxWitness
  have hsymbolWitness :
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
            (Abelianization.of qAmbient)) := by
    exact
      (congrArg
        (fun y : F₀ˣ =>
          abstractFixedFieldNormResidueSymbol
            K (SeparableClosure K)
            (localResidueDatum K)
            (localHenselianValuation K)
            (separableClosureUnits_isClassFormation K)
            H₀ J₀ hJH (Additive.ofMul y))
        hxPrime0).trans hambientPrime
  unfold ambientEmbeddedPrimeSymbolProperty
  exact hsymbolWitness

/-- The transported ambient symbol of the chosen prime witness equals
its ambient Frobenius target. -/
theorem
    ambientEmbeddedPrimeTransportValue_eq_target
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
    ambientEmbeddedPrimeTransportValue K F E j e z =
      ambientEmbeddedPrimeTarget K F E j e z := by
  have hsymbol :=
    ambientEmbeddedPrimeWitness_symbol K F E j e z
  unfold ambientEmbeddedPrimeSymbolProperty at hsymbol
  exact
    (ambientEmbeddedPrimeTransportValue_eq_target_of_symbol
      K F E j e z hsymbol)

/-- The ambient norm-residue value of the chosen prime witness is the
prescribed abelianized Galois element. -/
theorem
    ambientEmbeddedPrimeWitness_ambient
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
    ambientEmbeddedNormResidueAbelianElement K F E j e
        (ambientEmbeddedPrimeWitness K F E j e z) =
      z := by
  calc
    ambientEmbeddedNormResidueAbelianElement K F E j e
        (ambientEmbeddedPrimeWitness K F E j e z) =
        ambientEmbeddedPrimeTransportValue K F E j e z := rfl
    _ = ambientEmbeddedPrimeTarget K F E j e z :=
      ambientEmbeddedPrimeTransportValue_eq_target K F E j e z
    _ = z :=
      ambientEmbeddedPrimeTarget_eq K F E j e z

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_AmbientPrimeComparison
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.realComplexNormQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
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

/-- Every abelianized Galois element is simultaneously represented by the local
Artin map and by the ambient embedded norm-residue construction. -/
theorem
    exists_localArtin_ambientEmbedded_prime
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
    ∃ x : Fˣ,
      localArtinMonoidHom F E x = z ∧
        ambientEmbeddedNormResidueAbelianElement K F E j e x = z := by
  exact
    ⟨ambientEmbeddedPrimeWitness K F E j e z,
      ambientEmbeddedPrimeWitness_local K F E j e z,
      ambientEmbeddedPrimeWitness_ambient K F E j e z⟩

/-- For an embedded finite abelian local extension, the abelian local Artin
map agrees pointwise with the ambient norm-residue element transported through
a separable-closure equivalence. -/
theorem
    abelianLocalArtin_eq_ambientEmbeddedNormResidueSymbol_of_equiv
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
    (a : Fˣ) :
    abelianLocalArtinMonoidHom F E a =
      ambientEmbeddedNormResidueElement K F E j e a := by
  obtain ⟨x, hxLocal, hxAmbient⟩ :=
    exists_localArtin_ambientEmbedded_prime K F E j e
      (localArtinMonoidHom F E a)
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  let : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  let jF : E →ₐ[F] SeparableClosure K :=
    { j with commutes' := fun y => rfl }
  let jI : E →ₐ[F] SeparableClosure F :=
    e.symm.toAlgHom.comp jF
  have hnormClass :
      normClass F E a = normClass F E x := by
    apply
      (concreteReciprocityEquivOfEmbedding
        F E jI
        (localResidueDatum F)
        (localHenselianValuation F)
        (separableClosureUnits_isClassFormation F)).symm.injective
    change
      concreteNormResidueSymbolOfEmbedding
          F E jI
          (localResidueDatum F)
          (localHenselianValuation F)
          (separableClosureUnits_isClassFormation F) a =
        concreteNormResidueSymbolOfEmbedding
          F E jI
          (localResidueDatum F)
          (localHenselianValuation F)
          (separableClosureUnits_isClassFormation F) x
    have ha :=
      DFunLike.congr_fun
        (localArtinMonoidHom_eq_of_embedding F E jI) a
    have hx :=
      DFunLike.congr_fun
        (localArtinMonoidHom_eq_of_embedding F E jI) x
    rw [← ha, ← hx]
    exact hxLocal.symm
  have hxNormResidue :=
    ambientEmbeddedNormResidueAbelianElement_eq_of_normClass_eq
      K F E j e a x hnormClass
  change
    (Abelianization.equivOfComm (H := Gal(E / F))).symm
        (localArtinMonoidHom F E a) =
      (Abelianization.equivOfComm (H := Gal(E / F))).symm
        (ambientEmbeddedNormResidueAbelianElement K F E j e a)
  apply congrArg (Abelianization.equivOfComm (H := Gal(E / F))).symm
  calc
    localArtinMonoidHom F E a =
        ambientEmbeddedNormResidueAbelianElement K F E j e x :=
      hxAmbient.symm
    _ = ambientEmbeddedNormResidueAbelianElement K F E j e a :=
      hxNormResidue.symm

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_NormRestriction
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalClosedSubgroupQuotientFintype _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerInCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.padicCompletedLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RayClass.Modulus.congruenceSubgroup_normal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup _root_.scaledRelativeIntegerLatticeQuotientFinite
attribute [-simp] _root_.ClassFormation.DegreeData.finiteUnramifiedDegreeEquiv_unramifiedFrobenius _root_.ClassFormation.DegreeData.finiteUnramifiedDegreeHom_mk _root_.ClassFormation.DegreeData.finiteUnramifiedRestriction_frobenius _root_.ClassFormation.DegreeData.finiteUnramifiedRestriction_mk _root_.ClassFormation.DegreeData.maximalUnramifiedRestriction_frobenius _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.FiniteGaloisSubextension.intermediateFiniteAbelianOfCommutatorLe_field _root_.ClassFormation.ValuationData.maximalUnramifiedNormResidue_degree _root_.ClassFormation.mem_normFilterBasis_iff _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
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

/-- A compatible restriction of concrete embedded Galois actions induces the
corresponding restriction map on ambient finite quotient representatives. -/
theorem AmbientEmbeddedFixedFieldPresentation.quotientRestriction
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
    (restrictActual : Gal(L' / K') →* Gal(L / K))
    (hbase : ∀ x : L,
      jUpper (algebraMap L L' x) = jLower x)
    (hcompat : ∀ (τ : Gal(L' / K')) (x : L),
      jLower (restrictActual τ x) =
        jUpper (τ (algebraMap L L' x)))
    (z : Abelianization
      (upper.base.field.toSubgroup ⧸
        extensionSubgroup upper.base.field upper.extension.field
          upper.extension.below)) :
    restrictActual
        ((Abelianization.equivOfComm (H := Gal(L' / K'))).symm
          ((upper.extension.extensionQuotientMulEquiv.symm.trans
            upper.quotientEquiv).abelianizationCongr z)) =
      (Abelianization.equivOfComm (H := Gal(L / K))).symm
        ((lower.extension.extensionQuotientMulEquiv.symm.trans
          lower.quotientEquiv).abelianizationCongr
          (normResidueNaturalityAbelianizedRestriction
            lower.base.field upper.base.field
            lower.extension.field upper.extension.field
            lower.extension.below upper.extension.below
            hH'H hJ'J z)) := by
  let qLower :=
    lower.extension.extensionQuotientMulEquiv.symm.trans
      lower.quotientEquiv
  let qUpper :=
    upper.extension.extensionQuotientMulEquiv.symm.trans
      upper.quotientEquiv
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective z
  obtain ⟨sigma, rfl⟩ := QuotientGroup.mk_surjective q
  change
    restrictActual
        ((Abelianization.equivOfComm (H := Gal(L' / K'))).symm
          (qUpper.abelianizationCongr
            (Abelianization.of (QuotientGroup.mk sigma)))) =
      (Abelianization.equivOfComm (H := Gal(L / K))).symm
        (qLower.abelianizationCongr
          (normResidueNaturalityAbelianizedRestriction
            lower.base.field upper.base.field
            lower.extension.field upper.extension.field
            lower.extension.below upper.extension.below
            hH'H hJ'J (Abelianization.of (QuotientGroup.mk sigma))))
  rw [normResidueNaturalityAbelianizedRestriction_of_mk,
    abelianizationCongr_of, abelianizationCongr_of]
  change
    restrictActual (qUpper (QuotientGroup.mk sigma)) =
      qLower (QuotientGroup.mk (Subgroup.inclusion hH'H sigma))
  have hqUpper_mk :
      qUpper (QuotientGroup.mk sigma) =
        upper.quotientEquiv
          (upper.extension.extensionQuotientMk sigma) := by
    dsimp [qUpper]
    have hmk :
        upper.extension.extensionQuotientMulEquiv.symm
            (QuotientGroup.mk sigma) =
          upper.extension.extensionQuotientMk sigma := by
      exact
        upper.extension.extensionQuotientMulEquiv.symm_apply_eq.mpr
          (upper.extension.extensionQuotientMk_apply sigma).symm
    rw [hmk]
  have hqLower_mk :
      qLower (QuotientGroup.mk (Subgroup.inclusion hH'H sigma)) =
        lower.quotientEquiv
          (lower.extension.extensionQuotientMk
            (Subgroup.inclusion hH'H sigma)) := by
    dsimp [qLower]
    have hmk :
        lower.extension.extensionQuotientMulEquiv.symm
            (QuotientGroup.mk (Subgroup.inclusion hH'H sigma)) =
          lower.extension.extensionQuotientMk
            (Subgroup.inclusion hH'H sigma) := by
      exact
        lower.extension.extensionQuotientMulEquiv.symm_apply_eq.mpr
          (lower.extension.extensionQuotientMk_apply
            (Subgroup.inclusion hH'H sigma)).symm
    rw [hmk]
  apply AlgEquiv.ext
  intro x
  apply jLower.injective
  calc
    jLower
        (restrictActual
          (qUpper (QuotientGroup.mk sigma)) x) =
        jUpper
          ((qUpper (QuotientGroup.mk sigma))
            (algebraMap L L' x)) :=
      hcompat (qUpper (QuotientGroup.mk sigma)) x
    _ = jUpper
          (upper.quotientEquiv
            (upper.extension.extensionQuotientMk sigma)
            (algebraMap L L' x)) := by
      rw [hqUpper_mk]
    _ = sigma.1.1
        (jUpper (algebraMap L L' x)) :=
      upper.quotientEquiv_mk_apply sigma (algebraMap L L' x)
    _ = (Subgroup.inclusion hH'H sigma).1.1
        (jLower x) := by
      rw [hbase x]
      change sigma.1.1 (jLower x) = sigma.1.1 (jLower x)
      rfl
    _ = jLower
        (lower.quotientEquiv
          (lower.extension.extensionQuotientMk
            (Subgroup.inclusion hH'H sigma)) x) :=
      (lower.quotientEquiv_mk_apply
        (Subgroup.inclusion hH'H sigma) x).symm
    _ = jLower
        (qLower (QuotientGroup.mk
          (Subgroup.inclusion hH'H sigma)) x) := by
      rw [hqLower_mk]

/-- Canonical ambient fixed-field norm-residue values commute with restriction
and norm in an arbitrary finite square of nonarchimedean local fields. -/
theorem ambientEmbeddedNormResidueElement_norm_restriction
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
    (j : L' →ₐ[K] SeparableClosure K)
    (eLower :
      @AlgEquiv K (SeparableClosure K) (SeparableClosure K)
        _ _ _
        (separableClosure K (AlgebraicClosure K)).algebra
        (((j.comp (IsScalarTower.toAlgHom K L L')).comp
          (IsScalarTower.toAlgHom K K L)).toRingHom.toAlgebra))
    (eUpper :
      letI : Algebra K' (SeparableClosure K) :=
        (j.comp (IsScalarTower.toAlgHom K K' L')).toRingHom.toAlgebra
      SeparableClosure K' ≃ₐ[K'] SeparableClosure K)
    (a : K'ˣ) :
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K))
        (ambientEmbeddedNormResidueElement K K' L' j eUpper a) =
      ambientEmbeddedNormResidueElement K K L
        (j.comp (IsScalarTower.toAlgHom K L L')) eLower
        (normUnits K K' a) := by
  let : FiniteDimensional K L' :=
    FiniteDimensional.trans K K' L'
  let : Algebra.IsSeparable K L' :=
    Algebra.IsSeparable.trans K K' L'
  let iUpper : K' →ₐ[K] SeparableClosure K :=
    j.comp (IsScalarTower.toAlgHom K K' L')
  let jLower : L →ₐ[K] SeparableClosure K :=
    j.comp (IsScalarTower.toAlgHom K L L')
  let iLower : K →ₐ[K] SeparableClosure K :=
    jLower.comp (IsScalarTower.toAlgHom K K L)
  let lower :=
    ambientEmbeddedFixedFieldPresentation K K L jLower eLower
  let upper :=
    ambientEmbeddedFixedFieldPresentation K K' L' j eUpper
  let H := lower.base.field
  let H' := upper.base.field
  let J := lower.extension.field
  let J' := upper.extension.field
  have hRangeHH :
      AlgHom.fieldRange iLower ≤
        AlgHom.fieldRange iUpper := by
    intro x hx
    rcases hx with ⟨y, rfl⟩
    refine ⟨algebraMap K K' y, ?_⟩
    change
      j (algebraMap K' L' (algebraMap K K' y)) =
        j (algebraMap L L' (algebraMap K L y))
    rw [← IsScalarTower.algebraMap_apply K K' L',
      ← IsScalarTower.algebraMap_apply K L L']
  let hH'H : H'.toSubgroup ≤ H.toSubgroup := by
    change upper.base.field.toSubgroup ≤ lower.base.field.toSubgroup
    rw [lower.base_field_eq, upper.base_field_eq,
      lower.baseEmbedding_eq, upper.baseEmbedding_eq]
    change
      (AlgHom.fieldRange iUpper).fixingSubgroup ≤
        (AlgHom.fieldRange iLower).fixingSubgroup
    exact
      (AlgHom.fieldRange iLower).fixingSubgroup_le
        hRangeHH
  have hRangeJJ :
      AlgHom.fieldRange jLower ≤
        AlgHom.fieldRange j := by
    intro x hx
    rcases hx with ⟨y, rfl⟩
    exact ⟨algebraMap L L' y, rfl⟩
  let hJ'J : J'.toSubgroup ≤ J.toSubgroup := by
    change upper.extension.field.toSubgroup ≤ lower.extension.field.toSubgroup
    rw [lower.extension_field_eq, upper.extension_field_eq]
    change
      (AlgHom.fieldRange j).fixingSubgroup ≤
        (AlgHom.fieldRange jLower).fixingSubgroup
    exact
      (AlgHom.fieldRange jLower).fixingSubgroup_le
        hRangeJJ
  let hJH : J.toSubgroup ≤ H.toSubgroup := lower.extension.below
  let hJ'H' : J'.toSubgroup ≤ H'.toSubgroup := upper.extension.below
  let hJnormal :
      (extensionSubgroup H J hJH).Normal :=
    lower.extension.normal
  let hJfinite : Finite
      (H.toSubgroup ⧸ extensionSubgroup H J hJH) :=
    lower.extension.finite
  let hJ'normal :
      (extensionSubgroup H' J' hJ'H').Normal :=
    upper.extension.normal
  let hJ'finite : Finite
      (H'.toSubgroup ⧸ extensionSubgroup H' J' hJ'H') :=
    upper.extension.finite
  let hHabsolute : Finite
      ((baseField
        Gal(SeparableClosure K / K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          H (le_baseField H)) :=
    lower.base.finite
  let hH'absolute : Finite
      ((baseField
        Gal(SeparableClosure K / K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          H' (le_baseField H')) :=
    upper.base.finite
  let hH'finite : Finite
      (H.toSubgroup ⧸ extensionSubgroup H H' hH'H) := by
    let inclusion :=
      Subgroup.quotientSubgroupOfEmbeddingOfLE
        H'.toSubgroup (le_baseField H)
    exact Finite.of_injective inclusion inclusion.injective
  let FLower :=
    abstractFixedField K (SeparableClosure K) H
  let phiLower : K ≃ₐ[K] FLower :=
    lower.baseEquiv
  let FUpper :=
    abstractFixedField K (SeparableClosure K) H'
  let phiUpper : K' ≃ₐ[K] FUpper :=
    upper.baseEquiv
  let restrictActual :
      Gal(L' / K') →* Gal(L / K) :=
    (AlgEquiv.restrictNormalHom L).comp
      (AlgEquiv.restrictScalarsHom K)
  have hcompat : ∀ (τ : Gal(L' / K')) (x : L),
      jLower (restrictActual τ x) =
        j (τ (algebraMap L L' x)) := by
    intro τ x
    exact congrArg j
      (AlgEquiv.restrictNormal_commutes
        ((AlgEquiv.restrictScalarsHom K) τ) L x)
  have hbase : ∀ x : L,
      j (algebraMap L L' x) = jLower x := by
    intro x
    rfl
  let aUpper : FUpperˣ :=
    Units.mapEquiv phiUpper.toMulEquiv a
  let aNorm : Kˣ :=
    normUnits K K' a
  let aLower : FLowerˣ :=
    Units.mapEquiv phiLower.toMulEquiv aNorm
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
  let upperSymbolValue :=
    Additive.toMul
      (symbolUpper (Additive.ofMul aUpper))
  let lowerSymbolValue :=
    Additive.toMul
      (symbolLower (Additive.ofMul aLower))
  let upperQuotientValue :=
    upper.fixedFieldQuotientEquiv.abelianizationCongr.symm
      upperSymbolValue
  let lowerQuotientValue :=
    lower.fixedFieldQuotientEquiv.abelianizationCongr.symm
      lowerSymbolValue
  have hraw :
      normResidueNaturalityAbelianizedRestriction
          H H' J J' hJH hJ'H' hH'H hJ'J
          ((upper.extension.extensionQuotientMulEquiv.symm.trans
            upper.fixedFieldQuotientEquiv).abelianizationCongr.symm
            upperSymbolValue) =
        (lower.extension.extensionQuotientMulEquiv.symm.trans
          lower.fixedFieldQuotientEquiv).abelianizationCongr.symm
          lowerSymbolValue := by
    simpa only [H, H', J, J', hJH, hJ'H',
      aUpper, aLower, aNorm, symbolUpper, symbolLower,
      upperSymbolValue, lowerSymbolValue] using
      AmbientEmbeddedFixedFieldPresentation.fixedFieldNormResidueTransport
        K K' L L' lower upper hH'H hJ'J
        hbase a
  have htarget
      (z : Abelianization upper.extension.extensionQuotient) :
      restrictActual
          ((Abelianization.equivOfComm (H := Gal(L' / K'))).symm
            (upper.quotientEquiv.abelianizationCongr z)) =
        (Abelianization.equivOfComm (H := Gal(L / K))).symm
          (lower.quotientEquiv.abelianizationCongr
            (lower.extension.extensionQuotientMulEquiv.abelianizationCongr.symm
              (normResidueNaturalityAbelianizedRestriction
                H H' J J' hJH hJ'H' hH'H hJ'J
                (upper.extension.extensionQuotientMulEquiv.abelianizationCongr
                  z)))) := by
    simpa only [← abelianizationCongr_trans,
      ← abelianizationCongr_symm,
      MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply] using
      AmbientEmbeddedFixedFieldPresentation.quotientRestriction
        K K' L L' lower upper hH'H hJ'J restrictActual hbase hcompat
        (upper.extension.extensionQuotientMulEquiv.abelianizationCongr z)
  have hambient :
      lower.extension.extensionQuotientMulEquiv.abelianizationCongr.symm
          (normResidueNaturalityAbelianizedRestriction
            H H' J J' hJH hJ'H' hH'H hJ'J
            (upper.extension.extensionQuotientMulEquiv.abelianizationCongr
              upperQuotientValue)) =
        lowerQuotientValue := by
    refine
      lower.extension.extensionQuotientMulEquiv.abelianizationCongr.symm_apply_eq.mpr ?_
    calc
      normResidueNaturalityAbelianizedRestriction
          H H' J J' hJH hJ'H' hH'H hJ'J
          (upper.extension.extensionQuotientMulEquiv.abelianizationCongr
            upperQuotientValue) =
          normResidueNaturalityAbelianizedRestriction
            H H' J J' hJH hJ'H' hH'H hJ'J
            ((upper.extension.extensionQuotientMulEquiv.symm.trans
              upper.fixedFieldQuotientEquiv).abelianizationCongr.symm
              upperSymbolValue) := by
        simp only [← abelianizationCongr_trans,
          ← abelianizationCongr_symm, MulEquiv.symm_trans_apply,
          MulEquiv.symm_symm, upperQuotientValue]
      _ = (lower.extension.extensionQuotientMulEquiv.symm.trans
            lower.fixedFieldQuotientEquiv).abelianizationCongr.symm
            lowerSymbolValue := hraw
      _ = lower.extension.extensionQuotientMulEquiv.abelianizationCongr
            lowerQuotientValue := by
        simp only [← abelianizationCongr_trans,
          ← abelianizationCongr_symm, MulEquiv.symm_trans_apply,
          MulEquiv.symm_symm, lowerQuotientValue]
  have hupperEval :
      upper.normResidueAbelianElement a =
        upper.quotientEquiv.abelianizationCongr
          upperQuotientValue := by
    exact upper.normResidueAbelianElement_apply a
  have hlowerEval :
      lower.normResidueAbelianElement aNorm =
        lower.quotientEquiv.abelianizationCongr
          lowerQuotientValue := by
    exact lower.normResidueAbelianElement_apply aNorm
  let ambientUpper : Gal(L' / K') :=
    ambientEmbeddedNormResidueElement K K' L' j eUpper a
  let ambientLower : Gal(L / K) :=
    ambientEmbeddedNormResidueElement K K L jLower eLower aNorm
  have htransport :
      restrictActual ambientUpper = ambientLower := by
    dsimp only [ambientUpper, ambientLower,
      ambientEmbeddedNormResidueElement,
      ambientEmbeddedNormResidueAbelianElement]
    change
      restrictActual
          ((Abelianization.equivOfComm (H := Gal(L' / K'))).symm
            (upper.normResidueAbelianElement a)) =
        (Abelianization.equivOfComm (H := Gal(L / K))).symm
          (lower.normResidueAbelianElement aNorm)
    rw [hupperEval, hlowerEval]
    calc
      restrictActual
          ((Abelianization.equivOfComm (H := Gal(L' / K'))).symm
            (upper.quotientEquiv.abelianizationCongr
              upperQuotientValue)) =
        (Abelianization.equivOfComm (H := Gal(L / K))).symm
            (lower.quotientEquiv.abelianizationCongr
              (lower.extension.extensionQuotientMulEquiv.abelianizationCongr.symm
                (normResidueNaturalityAbelianizedRestriction
                  H H' J J' hJH hJ'H' hH'H hJ'J
                  (upper.extension.extensionQuotientMulEquiv.abelianizationCongr
                    upperQuotientValue)))) :=
        htarget upperQuotientValue
      _ = (Abelianization.equivOfComm (H := Gal(L / K))).symm
            (lower.quotientEquiv.abelianizationCongr
              lowerQuotientValue) :=
        congrArg
          (fun z =>
            (Abelianization.equivOfComm (H := Gal(L / K))).symm
              (lower.quotientEquiv.abelianizationCongr z))
          hambient
  change
    restrictActual ambientUpper = ambientLower
  exact htransport

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FiniteIdeleArtin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.relativeUnrestrictedSPlaceFactorCommGroup
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

/-- The finite Artin product after an idele norm, indexed directly by
the actual finite places upstairs.  This is the flattened finite-place
form of the local norm--restriction identity used in the global square. -/
theorem finitePlaceGlobalArtinMonoidHom_norm_eq_finprod
    {M : Type}
    [Field M] [NumberField M] [Algebra K M]
    (a : IdeleGroup M) :
    letI : ∀ W : HeightOneSpectrum (𝓞 M),
        Algebra
          ((finitePlaceBelow
            (K := K) W).adicCompletion K)
          (W.adicCompletion M) :=
      fun W =>
        (finitePlaceAdicCompletionMap
          K M
          (finitePlaceBelow (K := K) W)
          ⟨W, rfl⟩).toAlgebra
    finitePlaceGlobalArtinMonoidHom
        (K := K) (L := L)
        (IdeleGroup.norm K M a) =
      ∏ᶠ W : HeightOneSpectrum (𝓞 M),
        chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L)
          (finitePlaceBelow (K := K) W)
          (LocalFieldTheory.normUnits
            ((finitePlaceBelow
              (K := K) W).adicCompletion K)
            (W.adicCompletion M)
            (IdeleGroup.finiteComponent W a)) := by
  classical
  let : ∀ W : HeightOneSpectrum (𝓞 M),
      Algebra
        ((finitePlaceBelow
          (K := K) W).adicCompletion K)
        (W.adicCompletion M) :=
    fun W =>
      (finitePlaceAdicCompletionMap
        K M
        (finitePlaceBelow (K := K) W)
        ⟨W, rfl⟩).toAlgebra
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
  let g :
      HeightOneSpectrum (𝓞 M) →
        HeightOneSpectrum (𝓞 K) :=
    finitePlaceBelow (K := K)
  let f :
      HeightOneSpectrum (𝓞 M) →
        (L ≃ₐ[K] L) :=
    fun W =>
      chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) (g W)
        (LocalFieldTheory.normUnits
          ((g W).adicCompletion K)
          (W.adicCompletion M)
          (IdeleGroup.finiteComponent W a))
  have hf : HasFiniteMulSupport f := by
    simpa only [f, g] using
      finitePlaceNormArtinFactors_hasFiniteMulSupport
        (K := K) (L := L) a
  calc
    finitePlaceGlobalArtinMonoidHom
        (K := K) (L := L)
        (IdeleGroup.norm K M a) =
        ∏ᶠ v : HeightOneSpectrum (𝓞 K),
          ∏ W : {W : HeightOneSpectrum (𝓞 M) //
              g W = v},
            chosenFinitePlaceArtinMonoidHom
              (K := K) (L := L) v
              (LocalFieldTheory.normUnits
                (v.adicCompletion K)
                (W.1.adicCompletion M)
                (IdeleGroup.finiteComponent W.1 a)) := by
      simpa only [g] using
        finitePlaceGlobalArtinMonoidHom_norm_eq_finprod_fibers
          (K := K) (L := L) a
    _ = ∏ᶠ v : HeightOneSpectrum (𝓞 K),
          ∏ᶠ W : {W : HeightOneSpectrum (𝓞 M) //
              g W = v},
            f W.1 := by
      apply finprod_congr
      intro v
      rw [finprod_eq_prod_of_fintype]
      apply Finset.prod_congr rfl
      intro W _
      rcases W with ⟨W, hW⟩
      subst v
      simp only [f, g]
    _ = ∏ᶠ W : HeightOneSpectrum (𝓞 M), f W :=
      finprod_fibers_eq_sigma g f hf
    _ = ∏ᶠ W : HeightOneSpectrum (𝓞 M),
          chosenFinitePlaceArtinMonoidHom
            (K := K) (L := L)
            (finitePlaceBelow (K := K) W)
            (LocalFieldTheory.normUnits
              ((finitePlaceBelow (K := K) W).adicCompletion K)
              (W.adicCompletion M)
              (IdeleGroup.finiteComponent W a)) := by
      apply finprod_congr
      intro W
      simp only [f, g]

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_InfiniteGlobalArtin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateIdeleClassEquivGaloisFixed_coe _root_.IdeleClassGroup.normOneNorm_apply _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.fractionalIdeal_finitePrimeIdele _root_.IdeleGroup.idealClass_finitePrimeIdele _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# The infinite global Artin homomorphism

This file assembles the finite global Artin homomorphisms in the
`FiniteGaloisIntermediateField` inverse limit supplied by mathlib.  The
first target is the actual `ZHat`-extension of `ℚ` constructed in
`CyclotomicZHatBaseChange`.

The positive archimedean section below is the cyclotomic normalization device:
multiplying an idele by the section of its absolute
norm produces a norm-one idele without changing its Artin symbol.
-/

open scoped Classical IsMulCommutative NNReal NumberField Topology
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open CategoryTheory Opposite
open FiniteGaloisIntermediateField ProfiniteGrp

/-!
## Assembly in the finite-Galois inverse limit

The following construction is the global analogue of LCFT's
`residueFrobeniusToLimit`: its coordinates are the actual finite global
Artin homomorphisms, and compatibility is restriction in a finite
abelian tower.
-/

/-- The infinite global Artin homomorphism, like each of its finite
coordinates, kills the positive archimedean section. -/
@[simp]
theorem
    rationalCyclotomicZHatGlobalArtin_rationalPositiveArchimedeanIdele
    (r : ℝ≥0ˣ) :
    rationalCyclotomicZHatGlobalArtin
        (rationalPositiveArchimedeanIdele r) =
      1 := by
  let
      (E :
        FiniteGaloisIntermediateField
          ℚ rationalCyclotomicZHatField) :
      NumberField E :=
    NumberField.of_module_finite ℚ E
  let
      (E :
        FiniteGaloisIntermediateField
          ℚ rationalCyclotomicZHatField) :
      IsAbelianGalois ℚ E :=
    IsAbelianGalois.of_algHom E.toIntermediateField.val
  apply
    (InfiniteGalois.continuousMulEquivToLimit
      ℚ rationalCyclotomicZHatField).injective
  rw [
    continuousMulEquivToLimit_rationalCyclotomicZHatGlobalArtin_apply,
    map_one]
  apply Subtype.ext
  funext E
  exact
    globalArtinMonoidHom_rationalPositiveArchimedeanIdele
      (L := E.unop) r

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicIdeleValue
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The normalized cyclotomic idele value

For a number field `K`, the actual cyclotomic `ZHat`-extension is the
compositum of the embedded copy of `K` with the rational cyclotomic
`ZHat`-extension.  Its normalization factor is the actual intersection degree

`f_K = [K ∩ ℚ̃ : ℚ]`,

constructed in `CyclotomicZHatBaseChange`.

This file first constructs the idele-level map

`(1 / f_K) v_ℚ ∘ N_{K/ℚ} : I_K → ZHat`.

The factor `f_K` is removed only after proving that the unnormalized
value lies in the actual subgroup `f_K ZHat`.  This file stops at that
idele-level construction.  Descent from `I_K` to `C_K`, together with
the resulting integer-value and norm-range identities, requires the
genuine cyclotomic principal-idele formula and is the next
source-producing frontier; no quotient projection or abstract valuation
hypothesis is substituted for it here.
-/

noncomputable section

open scoped Topology

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation

/-- The rational infinite Artin homomorphism in the canonical
`Multiplicative ZHat` coordinate supplied by the cyclotomic Galois equivalence. -/
noncomputable def rationalCyclotomicZHatIdeleValue :
    IdeleGroup ℚ →ₜ* Multiplicative ZHat :=
  (ContinuousMonoidHom.toContinuousMonoidHom
    rationalCyclotomicZHatFieldGalEquivZHat).comp
      rationalCyclotomicZHatGlobalArtin

end Reciprocity
end GlobalClassFieldTheory
end
end


