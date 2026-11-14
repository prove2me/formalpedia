-- Prove2me | Definitions.Def_OAIQ244Duke115
-- name    : OAIQ244Duke115
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T23:38:41.303164+00:00
-- url     : https://prove2.me/theorems/aac7a685-9712-4da2-93ac-0348bfd0e951
-- title:
--   Definitions bundle OAIQ244Duke115 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 15 declarations of OpenAI's Lean: 5 definitions and 10 theorems. The definitions and types are `GlobalClassFieldTheory.Reciprocity.infiniteGlobalArtinLimitPoint`, `GlobalClassFieldTheory.Reciprocity.infiniteGlobalArtinMonoidHom`, `GlobalClassFieldTheory.Reciprocity.infiniteGlobalArtinToLimit`, `GlobalClassFieldTheory.Reciprocity.rationalPositiveArchimedeanIdele`, `GlobalClassFieldTheory.Reciprocity.rationalPositiveArchimedeanInfinitePart`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `GlobalClassFieldTheory_Reciprocity_FiniteIdeleArtin`, `GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_TowerRestriction`, `GlobalClassFieldTheory_Reciprocity_GlobalArtin`, `GlobalClassFieldTheory_Reciprocity_InfiniteGlobalArtin`.
--
--   **Imports.** It imports the bundle `OAIQ244Duke080` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ244Duke085`.
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
import Definitions.Def_OAIQ244Duke080

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_TowerRestriction
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionIsAlgebraic _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceExtensionCompletionAlgebra _root_.chosenFinitePlaceExtensionCompletionSMul _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsUltrametricDist _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Restriction in a finite-place Artin tower

This module restricts finite-place extensions through an intermediate field and proves restriction naturality for the corresponding global Artin homomorphisms.
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

/-- Local Artin maps on localized completions commute with restriction
through an abelian intermediate field. -/
theorem finitePlaceLocalArtinMonoidHom_restrict_tower
    {E : Type}
    [Field E] [Algebra K E] [Algebra E L]
    [IsScalarTower K E L]
    [FiniteDimensional K E] [IsAbelianGalois K E]
    (v : HeightOneSpectrum (𝓞 K))
    (wL : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L) :
    (finitePlaceLocalRestrictionMonoidHom
        (K := K) (L := L) (E := E) v wL).comp
        (finitePlaceLocalArtinMonoidHom
          (K := K) (L := L) v wL) =
      finitePlaceLocalArtinMonoidHom
        (K := K) (L := E) v
        (restrictFinitePlaceExtension
          (K := K) (L := L) (E := E) v wL) := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let wE :=
    restrictFinitePlaceExtension
      (K := K) (L := L) (E := E) v wL
  let EL := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wE
  let LL := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wL
  let : Algebra vK.Completion EL :=
    finitePlaceLocalArtinLocalizedAlgebra (K := K) (L := E) v wE
  let : Algebra vK.Completion LL :=
    finitePlaceLocalArtinLocalizedAlgebra (K := K) (L := L) v wL
  let localizationAlgHom :=
    finitePlaceRestrictedLocalizedCompletionAlgHom
      (K := K) (L := L) (E := E) v wL
  let hELL : Algebra EL LL :=
    localizationAlgHom.toRingHom.toAlgebra
  let : SMul EL LL := hELL.toSMul
  let : IsScalarTower vK.Completion EL LL :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro x
      exact (localizationAlgHom.commutes x).symm)
  let : FiniteDimensional vK.Completion EL :=
    finitePlaceLocalArtinFiniteDimensional (K := K) (L := E) v wE
  let : IsAbelianGalois vK.Completion EL :=
    finitePlaceLocalArtinIsAbelianGalois (K := K) (L := E) v wE
      (inferInstance : FiniteDimensional K E)
  let hGaloisEL : IsGalois vK.Completion EL :=
    (inferInstance :
      IsAbelianGalois vK.Completion EL).toIsGalois
  let : Normal vK.Completion EL :=
    hGaloisEL.to_normal
  let : FiniteDimensional vK.Completion LL :=
    finitePlaceLocalArtinFiniteDimensional (K := K) (L := L) v wL
  let : IsAbelianGalois vK.Completion LL :=
    finitePlaceLocalArtinIsAbelianGalois (K := K) (L := L) v wL
      (inferInstance : FiniteDimensional K L)
  let : ValuativeRel vK.Completion :=
    finitePlaceLocalArtinCompletionValuativeRel v
  let : IsNonarchimedeanLocalField vK.Completion :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let eK :
      vK.Completionˣ ≃* (v.adicCompletion K)ˣ :=
    finitePlaceCompletionUnitsContinuousMulEquiv v
  change
    (AlgEquiv.restrictNormalHom EL).comp
        ((LocalClassFieldTheory.abelianLocalArtinMonoidHom
          vK.Completion LL).comp eK.symm.toMonoidHom) =
      (LocalClassFieldTheory.abelianLocalArtinMonoidHom
        vK.Completion EL).comp eK.symm.toMonoidHom
  apply MonoidHom.ext
  intro x
  exact
    DFunLike.congr_fun
      (LocalClassFieldTheory.abelianLocalArtinMonoidHom_restrict_tower
        vK.Completion EL LL)
      (eK.symm x)


/-- Finite-place Artin homomorphisms attached to specified place
extensions commute with restriction through an abelian tower. -/
theorem finitePlaceArtinMonoidHomOfExtension_restrict_tower
    {E : Type}
    [Field E] [Algebra K E] [Algebra E L]
    [IsScalarTower K E L]
    [FiniteDimensional K E] [IsAbelianGalois K E]
    (v : HeightOneSpectrum (𝓞 K))
    (wL : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L) :
    (AlgEquiv.restrictNormalHom E).comp
        (finitePlaceArtinMonoidHomOfExtension
          (K := K) (L := L) v wL) =
      finitePlaceArtinMonoidHomOfExtension
        (K := K) (L := E) v
        (restrictFinitePlaceExtension
          (K := K) (L := L) (E := E) v wL) := by
  let wE :=
    restrictFinitePlaceExtension
      (K := K) (L := L) (E := E) v wL
  calc
    (AlgEquiv.restrictNormalHom E).comp
        (finitePlaceArtinMonoidHomOfExtension
          (K := K) (L := L) v wL) =
      (AlgEquiv.restrictNormalHom E).comp
        ((finitePlaceLocalToGlobalMonoidHom
          (K := K) (L := L) v wL).comp
          (finitePlaceLocalArtinMonoidHom
            (K := K) (L := L) v wL)) :=
      congrArg
        (fun f => (AlgEquiv.restrictNormalHom E).comp f)
        (finitePlaceArtinMonoidHomOfExtension_factor
          (K := K) (L := L) v wL)
    _ =
        ((AlgEquiv.restrictNormalHom E).comp
          (finitePlaceLocalToGlobalMonoidHom
            (K := K) (L := L) v wL)).comp
          (finitePlaceLocalArtinMonoidHom
            (K := K) (L := L) v wL) := by
      rfl
    _ =
        ((finitePlaceLocalToGlobalMonoidHom
          (K := K) (L := E) v wE).comp
          (finitePlaceLocalRestrictionMonoidHom
            (K := K) (L := L) (E := E) v wL)).comp
          (finitePlaceLocalArtinMonoidHom
            (K := K) (L := L) v wL) :=
      congrArg
        (fun f => f.comp
          (finitePlaceLocalArtinMonoidHom
            (K := K) (L := L) v wL))
        (finitePlaceDecompositionTransport_restrict_tower
          (K := K) (L := L) (E := E) v wL)
    _ =
        (finitePlaceLocalToGlobalMonoidHom
          (K := K) (L := E) v wE).comp
          ((finitePlaceLocalRestrictionMonoidHom
            (K := K) (L := L) (E := E) v wL).comp
            (finitePlaceLocalArtinMonoidHom
              (K := K) (L := L) v wL)) := by
      rfl
    _ =
        (finitePlaceLocalToGlobalMonoidHom
          (K := K) (L := E) v wE).comp
          (finitePlaceLocalArtinMonoidHom
            (K := K) (L := E) v wE) :=
      congrArg
        (fun f => (finitePlaceLocalToGlobalMonoidHom
          (K := K) (L := E) v wE).comp f)
        (finitePlaceLocalArtinMonoidHom_restrict_tower
          (K := K) (L := L) (E := E) v wL)
    _ =
        finitePlaceArtinMonoidHomOfExtension
          (K := K) (L := E) v wE :=
      (finitePlaceArtinMonoidHomOfExtension_factor
        (K := K) (L := E) v wE).symm

/-- Finite local factors commute with restriction in an abelian
number-field tower. -/
theorem chosenFinitePlaceArtinMonoidHom_restrict_tower
    {E : Type}
    [Field E] [Algebra K E] [Algebra E L]
    [IsScalarTower K E L]
    [FiniteDimensional K E] [IsAbelianGalois K E]
    (v : HeightOneSpectrum (𝓞 K)) :
    (AlgEquiv.restrictNormalHom E).comp
        (chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v) =
      chosenFinitePlaceArtinMonoidHom
        (K := K) (L := E) v := by
  let wL :=
    chosenFinitePlaceExtension
      (L := L) v
  let wE :=
    restrictFinitePlaceExtension
      (K := K) (L := L) (E := E) v wL
  calc
    (AlgEquiv.restrictNormalHom E).comp
        (chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v) =
      finitePlaceArtinMonoidHomOfExtension
        (K := K) (L := E) v wE :=
      finitePlaceArtinMonoidHomOfExtension_restrict_tower
        (K := K) (L := L) (E := E) v wL
    _ = chosenFinitePlaceArtinMonoidHom
        (K := K) (L := E) v :=
      finitePlaceArtinMonoidHomOfExtension_eq
        (K := K) (L := E) v wE
        (chosenFinitePlaceExtension
          (L := E) v)

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FiniteIdeleArtin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.Reciprocity.globalArtinMonoidHom_finitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.globalArtinMonoidHom_ideleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.globalArtinMonoidHom_infinitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.globalArtinMonoidHom_relativeIdeleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceGlobalArtinMonoidHom_finitePlaceIdele _root_.IdeleGroup.extension_finiteComponent _root_.IdeleGroup.extension_principalIdele _root_.IdeleGroup.extension_self _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk _root_.IdeleGroup.idealClass_classRepresentative _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleClassCongr_ideleClassNorm _root_.ideleClassCongr_mk _root_.ideleClassCongr_refl _root_.ideleClassExtension_mk _root_.ideleClassExtension_self _root_.ideleCongr_finiteComponent _root_.ideleCongr_principalIdele _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe _root_.intermediateClassNormQuotientBaseChangeMulEquiv_mk _root_.ordinaryIdeleClassNormQuotientCongrOfAlgEquiv_mk _root_.ordinaryIdeleClassNorm_relativeIdeleClassBaseChange _root_.relativeIdeleClassBaseChangeMulEquiv_classInclusion _root_.relativeIdeleClassBaseChangeMulEquiv_congrOfAlgEquiv _root_.relativeIdeleClassBaseChangeMulEquiv_mk _root_.relativeIdeleClassCongrOfAlgEquiv_ideleClassNorm _root_.relativeIdeleClassCongr_ideleClassNorm _root_.relativeIdeleCongr_norm _root_.towerRelativeIdeleViaOrdinaryMulEquiv_apply
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

/-- The finite-place global Artin homomorphism is continuous for the
restricted-product topology on ideles and the finite Krull topology on
the Galois group. -/
theorem finitePlaceGlobalArtinMonoidHom_continuous :
    Continuous
      (finitePlaceGlobalArtinMonoidHom
        (K := K) (L := L)) := by
  classical
  let T : Set (HeightOneSpectrum (𝓞 K)) :=
    {v | ∃ W : HeightOneSpectrum (𝓞 L),
      W.asIdeal.LiesOver v.asIdeal ∧
        ¬ Algebra.IsUnramifiedAt (𝓞 K) W.asIdeal}
  have hT : T.Finite :=
    AlgebraicNumberTheory.Ramification.finite_ramified_base_heightOne_primes
      (𝓞 K) (𝓞 L)
  let S : Finset (HeightOneSpectrum (𝓞 K)) :=
    hT.toFinset
  let U : Set (IdeleGroup K) :=
    (IdeleGroup.supportedAt (K := K) (S : Set _) : Set _) ∩
      {a | ∀ v ∈ S,
        IdeleGroup.finiteComponent v a ∈
          chosenFinitePlaceLocalNormSubgroup
            (K := K) (L := L) v}
  have hUopen : IsOpen U := by
    have hLocalOpen : IsOpen
        {a : IdeleGroup K | ∀ v ∈ S,
          IdeleGroup.finiteComponent v a ∈
            chosenFinitePlaceLocalNormSubgroup
              (K := K) (L := L) v} := by
      rw [show
        {a : IdeleGroup K | ∀ v ∈ S,
          IdeleGroup.finiteComponent v a ∈
            chosenFinitePlaceLocalNormSubgroup
              (K := K) (L := L) v} =
          ⋂ v ∈ S,
            (IdeleGroup.finiteComponent v) ⁻¹'
              (chosenFinitePlaceLocalNormSubgroup
                (K := K) (L := L) v : Set _) by
        ext a
        simp]
      exact isOpen_biInter_finset fun v _ =>
        (chosenFinitePlaceLocalNormSubgroup_isOpen
          (K := K) (L := L) v).preimage
            (IdeleGroup.finiteComponentContinuous v).continuous
    exact (IdeleGroup.isOpen_supportedAt S).inter hLocalOpen
  have hUone : (1 : IdeleGroup K) ∈ U := by
    constructor
    · exact (IdeleGroup.supportedAt
        (K := K) (S : Set _)).one_mem
    · intro v _
      rw [map_one]
      exact
        (chosenFinitePlaceLocalNormSubgroup
          (K := K) (L := L) v).one_mem
  have hUker :
      U ⊆
        (finitePlaceGlobalArtinMonoidHom
          (K := K) (L := L)) ⁻¹' {1} := by
    intro a ha
    change finitePlaceGlobalArtinMonoidHom
        (K := K) (L := L) a = 1
    apply finprod_eq_one_of_forall_eq_one
    intro v
    by_cases hv : v ∈ S
    · have hvNorm := ha.2 v hv
      rw [← chosenFinitePlaceArtinMonoidHom_ker
        (K := K) (L := L) v] at hvNorm
      exact MonoidHom.mem_ker.mp hvNorm
    · have hvT : v ∉ T := by
        simp only [S, Set.Finite.mem_toFinset] at hv
        exact hv
      have haIntegral :
          IdeleGroup.finiteComponent v a ∈
            (v.adicCompletionIntegers K).units := by
        exact
          (IdeleGroup.mem_supportedAt_iff
            (K := K) (S : Set _) a).mp ha.1 v hv
      apply
        chosenFinitePlaceArtinMonoidHom_eq_one_of_integral_of_unramifiedAt
          (K := K) (L := L) v a haIntegral
      by_contra hram
      apply hvT
      exact
        ⟨finitePlaceExtensionCentre
            (K := K) (L := L) v
            (chosenFinitePlaceExtension
              (L := L) v),
          finitePlaceExtensionCentre_liesOver
            (K := K) (L := L) v
            (chosenFinitePlaceExtension
              (L := L) v),
          hram⟩
  apply continuous_of_continuousAt_one _
  rw [continuousAt_def, map_one]
  intro V hV
  apply Filter.mem_of_superset (hUopen.mem_nhds hUone)
  intro a ha
  have hmap : finitePlaceGlobalArtinMonoidHom
      (K := K) (L := L) a = 1 :=
    Set.mem_preimage.mp (hUker ha)
  change finitePlaceGlobalArtinMonoidHom
      (K := K) (L := L) a ∈ V
  simpa only [hmap] using mem_of_mem_nhds hV

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_GlobalArtin
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
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

/-- The preliminary global Artin homomorphism is continuous. -/
theorem globalArtinMonoidHom_continuous :
    Continuous
      (globalArtinMonoidHom
        (K := K) (L := L)) :=
  (infinitePlaceGlobalArtinMonoidHom_continuous
    (K := K) (L := L)).mul
      (finitePlaceGlobalArtinMonoidHom_continuous
        (K := K) (L := L))

/-- For an abelian tower with fixed base field, the global Artin map
commutes with the genuine restriction homomorphism. -/
theorem globalArtinMonoidHom_restrict_tower
    {E : Type}
    [Field E] [NumberField E]
    [Algebra K E] [Algebra E L]
    [IsScalarTower K E L]
    [IsAbelianGalois K E] :
    (AlgEquiv.restrictNormalHom E).comp
        (globalArtinMonoidHom
          (K := K) (L := L)) =
      globalArtinMonoidHom
        (K := K) (L := E) := by
  apply MonoidHom.ext
  intro a
  change
    AlgEquiv.restrictNormalHom E
        (infinitePlaceGlobalArtinMonoidHom
            (K := K) (L := L) a *
          finitePlaceGlobalArtinMonoidHom
            (K := K) (L := L) a) =
      infinitePlaceGlobalArtinMonoidHom
          (K := K) (L := E) a *
        finitePlaceGlobalArtinMonoidHom
          (K := K) (L := E) a
  rw [map_mul]
  congr 1
  · simp only [infinitePlaceGlobalArtinMonoidHom,
      MonoidHom.finsetProd_apply, MonoidHom.comp_apply]
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro v _
    exact DFunLike.congr_fun
      (chosenInfinitePlaceArtinMonoidHom_restrict_tower
        (K := K) (L := L) (E := E) v)
      (IdeleGroup.infiniteComponent v a)
  · change
      AlgEquiv.restrictNormalHom E
          (∏ᶠ v : HeightOneSpectrum (𝓞 K),
            chosenFinitePlaceArtinMonoidHom
              (K := K) (L := L) v
              (IdeleGroup.finiteComponent v a)) =
        ∏ᶠ v : HeightOneSpectrum (𝓞 K),
          chosenFinitePlaceArtinMonoidHom
            (K := K) (L := E) v
            (IdeleGroup.finiteComponent v a)
    rw [MonoidHom.map_finprod
      (AlgEquiv.restrictNormalHom E)
      (finitePlaceArtinFactors_hasFiniteMulSupport
        (K := K) (L := L) a)]
    apply finprod_congr
    intro v
    exact DFunLike.congr_fun
      (chosenFinitePlaceArtinMonoidHom_restrict_tower
        (K := K) (L := L) (E := E) v)
      (IdeleGroup.finiteComponent v a)

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_InfiniteGlobalArtin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceBaseFourthRootField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceEmbeddedExtensionField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.cyclicPrimeDegreeIntermediate_isGalois
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk
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

noncomputable def rationalPositiveArchimedeanInfinitePart :
    ℝ≥0ˣ →* InfiniteIdeleGroup ℚ :=
  ContinuousMulEquiv.piUnits.symm.toMonoidHom.comp
    (MonoidHom.pi rationalPositiveArchimedeanLocalComponent)

theorem rationalPositiveArchimedeanInfinitePart_component
    (r : ℝ≥0ˣ) (v : InfinitePlace ℚ) :
    ContinuousMulEquiv.piUnits
        (rationalPositiveArchimedeanInfinitePart r) v =
      rationalPositiveArchimedeanLocalComponent v r := by
  change
    ContinuousMulEquiv.piUnits
        (ContinuousMulEquiv.piUnits.symm
          ((MonoidHom.pi rationalPositiveArchimedeanLocalComponent) r)) v =
      rationalPositiveArchimedeanLocalComponent v r
  exact congrFun
    (ContinuousMulEquiv.piUnits.apply_symm_apply
      ((MonoidHom.pi rationalPositiveArchimedeanLocalComponent) r)) v

/-- The positive archimedean section
`ℝ₊ˣ → I_ℚ`.  Its finite component is one, and at the unique infinite
place it is the positive real unit supplied by the input. -/
noncomputable def rationalPositiveArchimedeanIdele :
    ℝ≥0ˣ →* IdeleGroup ℚ := by
  exact
    { toFun := fun r =>
        (rationalPositiveArchimedeanInfinitePart r, 1)
      map_one' := by simp
      map_mul' := by simp }

/-- The positive archimedean section has trivial finite component at
every finite place of `ℚ`. -/
@[simp]
theorem rationalPositiveArchimedeanIdele_finiteComponent
    (r : ℝ≥0ˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    IdeleGroup.finiteComponent v
        (rationalPositiveArchimedeanIdele r) =
      1 :=
  rfl

/-- At the unique rational infinite place, the positive section becomes
the original positive real unit under mathlib's canonical completion
equivalence. -/
theorem rationalPositiveArchimedeanIdele_infiniteComponent
    (r : ℝ≥0ˣ) :
    Units.mapEquiv
        (InfinitePlace.Completion.ringEquivRealOfIsReal
          Rat.isReal_infinitePlace).toMulEquiv
        (IdeleGroup.infiniteComponent Rat.infinitePlace
          (rationalPositiveArchimedeanIdele r)) =
      Units.map NNReal.toRealHom.toMonoidHom r := by
  change
    Units.mapEquiv
        (InfinitePlace.Completion.ringEquivRealOfIsReal
          Rat.isReal_infinitePlace).toMulEquiv
        (ContinuousMulEquiv.piUnits
          (rationalPositiveArchimedeanInfinitePart r)
          Rat.infinitePlace) =
      Units.map NNReal.toRealHom.toMonoidHom r
  rw [rationalPositiveArchimedeanInfinitePart_component]
  let e :=
    (InfinitePlace.Completion.ringEquivRealOfIsReal
      Rat.isReal_infinitePlace).toMulEquiv
  change
    Units.mapEquiv e
        (Units.mapEquiv e.symm
          (Units.map NNReal.toRealHom.toMonoidHom r)) =
      Units.map NNReal.toRealHom.toMonoidHom r
  rw [← Units.mapEquiv_symm]
  exact
    (Units.mapEquiv e).apply_symm_apply
      (Units.map NNReal.toRealHom.toMonoidHom r)

/-- Every finite abelian global Artin homomorphism kills the positive
archimedean section over `ℚ`. -/
theorem globalArtinMonoidHom_rationalPositiveArchimedeanIdele
    {L : Type}
    [Field L] [NumberField L] [Algebra ℚ L]
    [IsAbelianGalois ℚ L]
    (r : ℝ≥0ˣ) :
    globalArtinMonoidHom
        (K := ℚ) (L := L)
        (rationalPositiveArchimedeanIdele r) =
      1 := by
  have hcomponent :=
    congrArg Units.val
      (rationalPositiveArchimedeanIdele_infiniteComponent r)
  have hpos :
      0 <
        InfinitePlace.Completion.ringEquivRealOfIsReal
          Rat.isReal_infinitePlace
          ((IdeleGroup.infiniteComponent Rat.infinitePlace
            (rationalPositiveArchimedeanIdele r) :
              Rat.infinitePlace.Completionˣ) :
            Rat.infinitePlace.Completion) := by
    have hvalue :
        InfinitePlace.Completion.ringEquivRealOfIsReal
            Rat.isReal_infinitePlace
            ((IdeleGroup.infiniteComponent Rat.infinitePlace
              (rationalPositiveArchimedeanIdele r) :
                Rat.infinitePlace.Completionˣ) :
              Rat.infinitePlace.Completion) =
          ((r : ℝ≥0ˣ) : ℝ) := by
      simpa using hcomponent
    rw [hvalue]
    exact
      NNReal.coe_pos.mpr
        (pos_iff_ne_zero.mpr (Units.ne_zero r))
  rw [globalArtinMonoidHom_apply]
  have hinfinite :
      (∏ v : InfinitePlace ℚ,
        chosenInfinitePlaceArtinMonoidHom
          (K := ℚ) (L := L) v
          (IdeleGroup.infiniteComponent v
            (rationalPositiveArchimedeanIdele r))) =
        1 := by
    rw [Fintype.prod_unique,
      show
        (default : InfinitePlace ℚ) = Rat.infinitePlace by
          exact Subsingleton.elim _ _]
    exact
      chosenInfinitePlaceArtinMonoidHom_eq_one_of_real_pos
        (K := ℚ) (L := L)
        Rat.infinitePlace Rat.isReal_infinitePlace _ hpos
  have hfinite :
      (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
        chosenFinitePlaceArtinMonoidHom
          (K := ℚ) (L := L) v
          (IdeleGroup.finiteComponent v
            (rationalPositiveArchimedeanIdele r))) =
        1 := by
    apply finprod_eq_one_of_forall_eq_one
    intro v
    rw [rationalPositiveArchimedeanIdele_finiteComponent,
      map_one]
  rw [hinfinite, hfinite, mul_one]

/-!
## Assembly in the finite-Galois inverse limit

The following construction is the global analogue of LCFT's
`residueFrobeniusToLimit`: its coordinates are the actual finite global
Artin homomorphisms, and compatibility is restriction in a finite
abelian tower.
-/

/-- The compatible family of finite global Artin symbols attached to
an idele, regarded as a point of the finite-Galois inverse limit. -/
noncomputable def infiniteGlobalArtinLimitPoint
    (K Ω : Type) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K) :
    limit
      (InfiniteGalois.asProfiniteGaloisGroupFunctor
        K Ω) := by
  letI (E :
      FiniteGaloisIntermediateField
        K Ω) :
      NumberField E :=
    NumberField.of_module_finite K E
  exact
    { val := fun E =>
        globalArtinMonoidHom
          (K := K) (L := E.unop) a
      property := by
        intro E F f
        algebraize [Subsemiring.inclusion <| leOfHom f.1]
        have : IsScalarTower K F.unop E.unop :=
          IsScalarTower.of_algebraMap_eq (congrFun rfl)
        change
          AlgEquiv.restrictNormalHom F.unop
              (globalArtinMonoidHom
                (K := K) (L := E.unop) a) =
            globalArtinMonoidHom
              (K := K) (L := F.unop) a
        exact
          DFunLike.congr_fun
            (globalArtinMonoidHom_restrict_tower
              (K := K) (E := F.unop) (L := E.unop)) a }

/-- The continuous global Artin homomorphism into the finite-Galois
inverse limit, before transport to the Krull-topological Galois group. -/
noncomputable def infiniteGlobalArtinToLimit
    (K Ω : Type) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω] :
    IdeleGroup K →ₜ*
      limit
        (InfiniteGalois.asProfiniteGaloisGroupFunctor
          K Ω) := by
  letI
      (E :
        FiniteGaloisIntermediateField
          K Ω) :
      NumberField E :=
    NumberField.of_module_finite K E
  exact
    { toFun := infiniteGlobalArtinLimitPoint K Ω
      map_one' := by
        apply Subtype.ext
        funext E
        exact
          (globalArtinMonoidHom
            (K := K) (L := E.unop)).map_one
      map_mul' := by
        intro x y
        apply Subtype.ext
        funext E
        exact
          (globalArtinMonoidHom
            (K := K) (L := E.unop)).map_mul x y
      continuous_toFun := by
        have hcontinuous
            (E :
              (FiniteGaloisIntermediateField
                K Ω)ᵒᵖ) :
            @Continuous
              (IdeleGroup K) (E.unop ≃ₐ[K] E.unop)
              inferInstance (krullTopology K E.unop)
              (globalArtinMonoidHom
                (K := K) (L := E.unop)) :=
          globalArtinMonoidHom_continuous
            (K := K) (L := E.unop)
        let
            (E :
              (FiniteGaloisIntermediateField
                K Ω)ᵒᵖ) :
            TopologicalSpace (E.unop ≃ₐ[K] E.unop) :=
          ((InfiniteGalois.asProfiniteGaloisGroupFunctor
            K Ω).obj E).toProfinite.toTop.str
        apply Continuous.subtype_mk
        exact continuous_pi fun E => by
          change
            @Continuous
              (IdeleGroup K) (E.unop ≃ₐ[K] E.unop)
              inferInstance inferInstance
              (globalArtinMonoidHom
                (K := K) (L := E.unop))
          rw [show
            (inferInstance :
              TopologicalSpace (E.unop ≃ₐ[K] E.unop)) =
                krullTopology K E.unop by
            change
              (⊥ : TopologicalSpace
                (E.unop ≃ₐ[K] E.unop)) =
                  krullTopology K E.unop
            exact
              (@DiscreteTopology.eq_bot _
                (krullTopology K E.unop)
                inferInstance).symm]
          exact hcontinuous E }

/-- The continuous global Artin homomorphism of an arbitrary abelian
Galois extension of a number field.  Its finite coordinates are the
finite global Artin homomorphisms. -/
noncomputable def infiniteGlobalArtinMonoidHom
    (K Ω : Type) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω] :
    IdeleGroup K →ₜ* (Ω ≃ₐ[K] Ω) :=
  (ContinuousMonoidHom.toContinuousMonoidHom
    (InfiniteGalois.continuousMulEquivToLimit
      K Ω).symm).comp
    (infiniteGlobalArtinToLimit K Ω)

end Reciprocity
end GlobalClassFieldTheory
end
end


