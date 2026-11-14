-- Prove2me | Definitions.Def_OAIQ244Duke048
-- name    : OAIQ244Duke048
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:52:31.385528+00:00
-- url     : https://prove2.me/theorems/5ccc72c7-5e3f-4fa2-b18d-791d750482e6
-- title:
--   Definitions bundle OAIQ244Duke048 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 86 declarations of OpenAI's Lean: 29 definitions, 5 instances and 52 theorems. The definitions and types are `GlobalClassFieldTheory.ClassFieldAxiom.principalIdelePowerLocalUnitSubgroup`, `GlobalClassFieldTheory.ClassFieldAxiom.supportedIdelePowerClassMap`, `GlobalClassFieldTheory.ClassFieldAxiom.supportedIdelePowerLocalUnitSubgroup`, `GlobalClassFieldTheory.ClassFieldAxiom.supportedIdeleQuotientEquivLocalPowerClasses`, `IdeleGroup.modulusOfFinset`, `KummerTheory.chosenUnitFiniteSupport`, `KummerTheory.enlargeByFiniteKummerRadicalSupport`, `KummerTheory.finiteKummerRadicalSupport`, `LocalClassFieldTheory.localAbstractFixedResidueActionOverIntermediateField`, `LocalClassFieldTheory.localAbstractFixedResidueFiniteGaloisIntermediateField`, `LocalClassFieldTheory.localAbstractFixedResidueIntermediateField`, `LocalClassFieldTheory.localAbstractFixedResidueIntermediateFieldAlgebra`, `LocalClassFieldTheory.localAbstractFixedResidueIntermediateFieldModule`, `LocalClassFieldTheory.localBaseResidueEquivDecompositionResidue`, `LocalClassFieldTheory.localBaseValuationSubringEquivDecompositionField`, `LocalClassFieldTheory.localResidueDatum`, `LocalClassFieldTheory.localResidueDegree`, `LocalClassFieldTheory.localSelectedResidueLift`, `LocalClassFieldTheory.localSeparableResidueAlgAction`, `LocalClassFieldTheory.localSeparableValuationSubring`, `LocalClassFieldTheory.residueFieldEquivDecompositionResidueOfEqTop`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinateLinear`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsCoordinateLinear`, `chosenFinitePlaceDecompositionGroupEquivProvider`, `chosenFinitePlaceDecompositionGroupFintypeProvider`, `chosenFinitePlaceInducedIntegerUnitsAction`, `chosenFinitePlaceLocalPlaceBlockAction`, `chosenFinitePlaceLocalizedIntegerUnitsGaloisActionProvider`, `finitePlaceCompletionIntegerRingEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Completion_IntegerRingComparison`, `AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_ChosenPlace`, `AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_ChosenPlaceAction`, `AlgebraicNumberTheory_RayClass_Approximation`, `GlobalClassFieldTheory_ClassFieldAxiom_IdelePowerLocalUnitSubgroup`, `GlobalClassFieldTheory_ClassFieldAxiom_SupportedIdelePowerLocalUnitQuotient`, `GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_NormRestriction`, `KummerTheory_Concrete_SUnitPreparation_FiniteRadicalSupport`, `LocalClassFieldTheory_ClassFormation_FieldUnitsHerbrand`, `LocalClassFieldTheory_ClassFormation_IntegerUnitsHerbrand`, `LocalClassFieldTheory_ClassFormation_Main`, `LocalClassFieldTheory_ClassFormation_NormalBasisFiniteQuotient`, `LocalClassFieldTheory_ClassFormation_Valuation`, `LocalClassFieldTheory_ClassFormation_ValuationHerbrand`, `LocalClassFieldTheory_Finite_LocalReciprocity_FiniteExtensionClassFieldAxiom`, `LocalClassFieldTheory_Finite_LocalReciprocity_FiniteResidueFinrankTransfer`, `LocalClassFieldTheory_Finite_LocalReciprocity_FiniteSubgroupResidueDegree`, `LocalClassFieldTheory_Finite_LocalReciprocity_LocalResidueDatum`, `LocalClassFieldTheory_Finite_LocalReciprocity_SeparableUnitsNorm`, `LocalField_DiscreteValuationField_MixedCharacteristicQp`, `LocalField_DiscreteValuationField_MixedCharacteristicStructure_IntegralLattice`, `LocalField_DiscreteValuationField_PrincipalUnitPadicAction_AdicPadicModule`, `LocalField_DiscreteValuationField_PrincipalUnitPadicAction_ProdiscretePadicModule`, `LocalField_NonarchimedeanLocalField_ValuationExactSequence`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke037`, `OAIQ244Duke038`, `OAIQ244Duke039` and `OAIQ244Duke040` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke055`, `OAIQ244Duke056`, `OAIQ244Duke057`, `OAIQ244Duke058`, `OAIQ244Duke059`, `OAIQ244Duke060` and `OAIQ244Duke061`.
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
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
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
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.DedekindDomain.Factorization
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
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.Compact
import Mathlib.Topology.Algebra.Module.FiniteDimension
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
import Definitions.Def_OAIQ244Duke037
import Definitions.Def_OAIQ244Duke038
import Definitions.Def_OAIQ244Duke039
import Definitions.Def_OAIQ244Duke040

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_ValuationExactSequence
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-!
# The valuation exact sequence

Builds the normalized valuation map `Kˣ → ℤ` and proves exactness of the
sequence from valuation-ring units through field units to `ℤ`.
-/

namespace LocalFieldTheory

noncomputable section

universe u

namespace IsNonarchimedeanLocalField

open scoped ValuativeRel WithZero

/-- Every integer is the valuation of some field unit. -/
theorem valuationMap_surjective (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] :
    Function.Surjective (valuationMap K) :=
  v_surjective K

/-- A field unit comes from a valuation-ring unit exactly when its additive valuation is zero. -/
theorem integerUnitsToFieldUnits_mem_range_iff_valuationMap_eq_zero (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (x : Kˣ) :
    x ∈ MonoidHom.range (integerUnitsToFieldUnits K) ↔
      valuationMap K (Additive.ofMul x) = 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    rw [valuationMap_apply]
    exact v_integerUnitsToFieldUnits K u
  · intro hx
    exact ⟨integerUnitOfValuationMapZero K x hx,
      integerUnitOfValuationMapZero_spec K x hx⟩

end IsNonarchimedeanLocalField

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_Valuation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.CyclicCohomology.galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure_mk _root_.CyclicCohomology.mem_chosenBaseUniformizerPowSubmodule_iff _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.chosenNormalBasisIntegerLatticeMulPowLinearEquiv_apply _root_.LocalFieldTheory.galoisGroupResidueFieldEquivOfIsIntegralClosure_residue _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
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

/-- The inclusion `𝒪_Lˣ → Lˣ` is equivariant for the actual actions. -/
theorem integerUnitsToFieldUnits_galoisGroup_equivariant
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (σ : Gal(L / K)) (x : 𝒪[L]ˣ) :
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    letI := galoisGroupFieldUnitsMulDistribMulAction K L
    integerUnitsToFieldUnits L (σ • x) =
      σ • integerUnitsToFieldUnits L x := by
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  let := galoisGroupFieldUnitsMulDistribMulAction K L
  ext
  rfl

/-- A Galois automorphism preserves the normalized additive valuation.  The
proof uses only the actual integral-closure restriction to `𝒪_L`, the DVR
normalization of an irreducible uniformizer, and the unit--uniformizer
decomposition of `Lˣ`; no extension-invariant package is assumed. -/
theorem valuationMap_unitsMapEquiv_galoisGroup
    (K L : Type u) [Field K] [ValuativeRel K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (σ : Gal(L / K)) (x : Lˣ) :
    valuationMap L
        (Additive.ofMul (Units.mapEquiv σ.toMulEquiv x)) =
      valuationMap L (Additive.ofMul x) := by
  let e : 𝒪[L] ≃+* 𝒪[L] := galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ
  let πO : 𝒪[L] := chosenIntegerRingUniformizer L
  let π : Lˣ := integerRingUniformizerFieldUnit L
  let σπ : Lˣ := Units.mapEquiv σ.toMulEquiv π
  have heπO : Irreducible (e πO) :=
    (MulEquiv.irreducible_iff e.toMulEquiv).2
      (chosenIntegerRingUniformizer_irreducible L)
  have hσπ : (σπ : L) = ((e πO : 𝒪[L]) : L) := by
    rfl
  have hvσπ : v L (Additive.ofMul σπ) = -1 :=
    v_integerRingIrreducibleFieldUnit L (e πO) heπO σπ hσπ
  have hvσπinv : v L (Additive.ofMul σπ⁻¹) = 1 := by
    rw [v_inv, hvσπ]
    norm_num
  let ϖ : Lˣ := inverseIntegerRingUniformizerFieldUnit L
  have hmapϖ : Units.mapEquiv σ.toMulEquiv ϖ = σπ⁻¹ := by
    ext
    rfl
  have hvmapϖ :
      v L (Additive.ofMul (Units.mapEquiv σ.toMulEquiv ϖ)) = 1 := by
    rw [hmapϖ]
    exact hvσπinv
  have hϖ : valuationMap L (Additive.ofMul ϖ) = 1 := by
    exact v_inverseIntegerRingUniformizerFieldUnit L
  let n : Int := valuationMap L (Additive.ofMul x)
  let u : 𝒪[L]ˣ := uniformizerUnitFactor L ϖ hϖ x
  let σu : 𝒪[L]ˣ := Units.mapEquiv e.toMulEquiv u
  have hmapu :
      Units.mapEquiv σ.toMulEquiv (integerUnitsToFieldUnits L u) =
        integerUnitsToFieldUnits L σu := by
    ext
    rfl
  have hvmapu :
      v L (Additive.ofMul
        (Units.mapEquiv σ.toMulEquiv (integerUnitsToFieldUnits L u))) = 0 := by
    rw [hmapu]
    exact v_integerUnitsToFieldUnits L σu
  have hx : integerUnitsToFieldUnits L u * ϖ ^ n = x := by
    simp [u, n]
  have hxσ :
      Units.mapEquiv σ.toMulEquiv x =
        Units.mapEquiv σ.toMulEquiv (integerUnitsToFieldUnits L u) *
          (Units.mapEquiv σ.toMulEquiv ϖ) ^ n := by
    calc
      Units.mapEquiv σ.toMulEquiv x =
          Units.mapEquiv σ.toMulEquiv
            (integerUnitsToFieldUnits L u * ϖ ^ n) :=
        congrArg (Units.mapEquiv σ.toMulEquiv) hx.symm
      _ = Units.mapEquiv σ.toMulEquiv (integerUnitsToFieldUnits L u) *
          (Units.mapEquiv σ.toMulEquiv ϖ) ^ n := by
        simp only [map_mul, map_zpow]
  rw [valuationMap_apply, valuationMap_apply, hxσ, v_mul, v_zpow,
    hvmapu, hvmapϖ, mul_one, zero_add]
  rfl

/-- The normalized valuation on `Lˣ` is equivariant for the actual Galois
action and the trivial action on its value group. -/
theorem valuationUnitsMulHom_galoisGroup_equivariant
    (K L : Type u) [Field K] [ValuativeRel K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (σ : Gal(L / K)) (x : Lˣ) :
    letI := galoisGroupFieldUnitsMulDistribMulAction K L
    letI := galoisGroupValueGroupMulDistribMulAction K L
    valuationUnitsMulHom L (σ • x) =
      σ • valuationUnitsMulHom L x := by
  let := galoisGroupFieldUnitsMulDistribMulAction K L
  let := galoisGroupValueGroupMulDistribMulAction K L
  exact congrArg Multiplicative.ofAdd
    (valuationMap_unitsMapEquiv_galoisGroup K L σ x)

/-- Multiplicative and additive presentations of valuation-one/valuation-zero
agree for a field unit. -/
theorem valuationUnitsMulHom_eq_one_iff_valuationMap_eq_zero
    (L : Type u) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] (x : Lˣ) :
    valuationUnitsMulHom L x = 1 ↔
      valuationMap L (Additive.ofMul x) = 0 := by
  change valuationUnitsMulHom L x = 1 ↔
    Multiplicative.toAdd (valuationUnitsMulHom L x) = 0
  constructor
  · intro hx
    exact congrArg Multiplicative.toAdd hx
  · intro hx
    apply Multiplicative.toAdd.injective
    exact hx

/-- Exactness at `Lˣ`: the kernel of normalized valuation consists exactly
of the units of the valuation integer ring. -/
theorem valuationUnitsMulHom_eq_one_iff_exists_integerUnit
    (L : Type u) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] (x : Lˣ) :
    valuationUnitsMulHom L x = 1 ↔
      ∃ y : 𝒪[L]ˣ, integerUnitsToFieldUnits L y = x := by
  rw [valuationUnitsMulHom_eq_one_iff_valuationMap_eq_zero]
  constructor
  · intro hx
    exact
      (integerUnitsToFieldUnits_mem_range_iff_valuationMap_eq_zero L x).2 hx
  · rintro ⟨y, rfl⟩
    exact
      (integerUnitsToFieldUnits_mem_range_iff_valuationMap_eq_zero L
        (integerUnitsToFieldUnits L y)).1 ⟨y, rfl⟩

/-- The multiplicative normalized valuation `Lˣ → Multiplicative ℤ` is
surjective. -/
theorem valuationUnitsMulHom_surjective
    (L : Type u) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] :
    Function.Surjective (valuationUnitsMulHom L) := by
  intro n
  rcases valuationMap_surjective L (Multiplicative.toAdd n) with ⟨x, hx⟩
  refine ⟨Additive.toMul x, ?_⟩
  change Multiplicative.ofAdd (valuationMap L x) = n
  rw [hx]
  rfl

end
end LocalClassFieldTheory
end

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

/-- The full modulus whose finite part has exponent one exactly at the places
of a finite set and whose infinite part is empty.  It lets the ray-class
approximation space serve as an arbitrary finite-place approximation space. -/
noncomputable def modulusOfFinset
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    RayClass.Modulus K := by
  classical
  exact RayClass.Modulus.ofFinite
    (Finsupp.onFinset S
      (fun v => if v ∈ S then 1 else 0)
      (by
        intro v hv
        simpa using hv))

@[simp]
theorem modulusOfFinset_apply
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (v : HeightOneSpectrum (𝓞 K)) :
    (modulusOfFinset S).finitePart v = if v ∈ S then 1 else 0 := by
  classical
  rfl

end IdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_ValuationHerbrand
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
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
# The valuation sequence and Herbrand quotients

This file applies the Herbrand-quotient multiplicativity theorem to the actual
valuation sequence from integer units through field units to the value group.

All three actions are the concrete actions from `ValuationReal`: the Galois
action on integer and field units, and the trivial action on the value group.
-/

noncomputable section

open scoped ValuativeRel
open CyclicCohomology.ProfiniteCohomology.Herbrand
open IsNonarchimedeanLocalField

variable (K L : Type) [Field K] [ValuativeRel K]
  [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure (ValuativeRel.valuation L).integer
    (ValuativeRel.valuation K).integer L]

omit [FiniteDimensional K L] in
/-- The actual valuation sequence has equivariant maps, is exact at field
units, is injective on integer units, and is surjective onto the value group. -/
theorem valuationHerbrand_shortExact :
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    letI := galoisGroupFieldUnitsMulDistribMulAction K L
    letI := galoisGroupValueGroupMulDistribMulAction K L
    (∀ (σ : Gal(L / K)) (x : (ValuativeRel.valuation L).integerˣ),
        integerUnitsToFieldUnits L (σ • x) =
          σ • integerUnitsToFieldUnits L x) ∧
      (∀ (σ : Gal(L / K)) (x : Lˣ),
        valuationUnitsMulHom L (σ • x) =
          σ • valuationUnitsMulHom L x) ∧
      (∀ x : Lˣ, valuationUnitsMulHom L x = 1 ↔
        ∃ y : (ValuativeRel.valuation L).integerˣ,
          integerUnitsToFieldUnits L y = x) ∧
      Function.Injective (integerUnitsToFieldUnits L) ∧
      Function.Surjective (valuationUnitsMulHom L) := by
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  let := galoisGroupFieldUnitsMulDistribMulAction K L
  let := galoisGroupValueGroupMulDistribMulAction K L
  exact ⟨integerUnitsToFieldUnits_galoisGroup_equivariant K L,
    valuationUnitsMulHom_galoisGroup_equivariant K L,
    valuationUnitsMulHom_eq_one_iff_exists_integerUnit L,
    integerUnitsToFieldUnits_injective L,
    valuationUnitsMulHom_surjective L⟩

/-- Herbrand-quotient multiplicativity for the actual valuation sequence.  Once the
Herbrand quotient of the integer-unit term is defined, the value-group term
is already defined by `galoisGroupValueGroup_herbrandQuotientDefined`; hence the
field-unit quotient is defined and

`h(G,Lˣ) = h(G,(valuation integer ring of L)ˣ) * h(G,ℤ)`.

The only non-derived finiteness input is `hU`, the two finite low-degree
Herbrand quotients for the actual integer-unit action. -/
theorem valuationHerbrand_multiplicativity_of_integerUnits_defined
    (g : Gal(L / K))
    (hg : ∀ σ : Gal(L / K), σ ∈ Subgroup.zpowers g)
    (hU :
      letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
      HerbrandQuotientDefined (Gal(L / K))
        (ValuativeRel.valuation L).integerˣ g) :
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    letI := galoisGroupFieldUnitsMulDistribMulAction K L
    letI := galoisGroupValueGroupMulDistribMulAction K L
    let hZ : HerbrandQuotientDefined (Gal(L / K)) (Multiplicative Int) g :=
      galoisGroupValueGroup_herbrandQuotientDefined K L g
    ∃ hField : HerbrandQuotientDefined (Gal(L / K)) Lˣ g,
      @herbrandQuotient (Gal(L / K)) Lˣ _ _ _
          (galoisGroupFieldUnitsMulDistribMulAction K L) g hField.1 hField.2 =
        @herbrandQuotient (Gal(L / K))
            (ValuativeRel.valuation L).integerˣ _ _ _
            (galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L)
            g hU.1 hU.2 *
          @herbrandQuotient (Gal(L / K)) (Multiplicative Int) _ _ _
            (galoisGroupValueGroupMulDistribMulAction K L) g hZ.1 hZ.2 := by
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  let := galoisGroupFieldUnitsMulDistribMulAction K L
  let := galoisGroupValueGroupMulDistribMulAction K L
  let hZ : HerbrandQuotientDefined (Gal(L / K)) (Multiplicative Int) g :=
    galoisGroupValueGroup_herbrandQuotientDefined K L g
  let hseq := valuationHerbrand_shortExact K L
  let hField := herbrandQuotientDefined_middle_of_left_right
    (G := Gal(L / K))
    (A := (ValuativeRel.valuation L).integerˣ)
    (B := Lˣ) (C := Multiplicative Int)
    (integerUnitsToFieldUnits L) (valuationUnitsMulHom L)
    hseq.1 hseq.2.1 hseq.2.2.1 hseq.2.2.2.1 hseq.2.2.2.2
    g hg hU hZ
  refine ⟨hField, ?_⟩
  let : Finite
      (HerbrandH0 (Gal(L / K)) (ValuativeRel.valuation L).integerˣ) := hU.1
  let : Finite
      (HerbrandHMinusOne (Gal(L / K))
        (ValuativeRel.valuation L).integerˣ g) := hU.2
  let : Finite (HerbrandH0 (Gal(L / K)) Lˣ) := hField.1
  let : Finite (HerbrandHMinusOne (Gal(L / K)) Lˣ g) := hField.2
  let : Finite
      (HerbrandH0 (Gal(L / K)) (Multiplicative Int)) := hZ.1
  let : Finite
      (HerbrandHMinusOne (Gal(L / K)) (Multiplicative Int) g) := hZ.2
  exact herbrandQuotient_multiplicative_of_shortExact
    (G := Gal(L / K))
    (A := (ValuativeRel.valuation L).integerˣ)
    (B := Lˣ) (C := Multiplicative Int)
    (integerUnitsToFieldUnits L) (valuationUnitsMulHom L)
    hseq.1 hseq.2.1 hseq.2.2.1 hseq.2.2.2.1 hseq.2.2.2.2
    g hg

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_FieldUnitsHerbrand
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.herbrandH0EquivariantMulEquiv_mk _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction_smul _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroup_sigmaMinusOne_coe _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroup_tateNorm_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory
open CyclicCohomology

open LocalFieldTheory

/-!
# The field-unit calculation in the local class-field-axiom theorem

This file proves the final Herbrand-quotient calculation for the local
class-field axiom. Its only input beyond the local-field hypotheses is the
preceding normal-basis calculation `h(G, O_Lˣ) = 1` for the actual action on
integer units.
-/

noncomputable section

open scoped ValuativeRel
open CyclicCohomology.ProfiniteCohomology.Herbrand
open IsNonarchimedeanLocalField

variable (K L : Type) [Field K] [ValuativeRel K]
  [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
  [IsGalois K L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure (ValuativeRel.valuation L).integer
    (ValuativeRel.valuation K).integer L]

omit [IsGalois K L] in
/-- Finiteness of actual unit Tate `H⁰`, derived from the finite Herbrand
quotients in the valuation exact sequence and transported across the genuine
comparison equivalence. -/
theorem unitsTateH0FiniteOfIntegerUnitsHerbrand
    (g : Gal(L / K))
    (hg : ∀ σ : Gal(L / K), σ ∈ Subgroup.zpowers g)
    (hU :
      letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
      HerbrandQuotientDefined (Gal(L / K))
        (ValuativeRel.valuation L).integerˣ g) :
    Finite (tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0) := by
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  let := galoisGroupFieldUnitsMulDistribMulAction K L
  let := galoisGroupValueGroupMulDistribMulAction K L
  obtain ⟨hField, _⟩ :=
    valuationHerbrand_multiplicativity_of_integerUnits_defined K L g hg hU
  let : Finite (HerbrandH0 (Gal(L / K)) Lˣ) := hField.1
  exact Finite.of_equiv (HerbrandH0 (Gal(L / K)) Lˣ)
    (herbrandH0EquivTateCohomologyZero K L)

/-- Final Herbrand calculation for the local class-field axiom.  Multiplicativity for the
valuation sequence, the normal-basis result `h(G,O_Lˣ)=1`, the value-group
calculation, and Hilbert 90 imply the two asserted cardinalities for the
actual Tate cohomology of `Lˣ`. -/
theorem fieldUnits_tate_card_of_integerUnits_herbrand_eq_one
    (g : Gal(L / K))
    (hg : ∀ σ : Gal(L / K), σ ∈ Subgroup.zpowers g)
    (hU :
      letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
      HerbrandQuotientDefined (Gal(L / K))
        (ValuativeRel.valuation L).integerˣ g)
    (hU_one :
      letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
      @herbrandQuotient (Gal(L / K))
          (ValuativeRel.valuation L).integerˣ _ _ _
          (galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L)
          g hU.1 hU.2 = 1) :
    letI := unitsTateH0FiniteOfIntegerUnitsHerbrand K L g hg hU
    Nat.card (tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0) = Module.finrank K L ∧
      Nat.card (tateCohomology (Rep.ofAlgebraAutOnUnits K L) (-1)) = 1 := by
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  let := galoisGroupFieldUnitsMulDistribMulAction K L
  let := galoisGroupValueGroupMulDistribMulAction K L
  let hZ : HerbrandQuotientDefined
      (Gal(L / K)) (Multiplicative Int) g :=
    galoisGroupValueGroup_herbrandQuotientDefined K L g
  rcases valuationHerbrand_multiplicativity_of_integerUnits_defined
      K L g hg hU with ⟨hField, hmult⟩
  let : Finite (HerbrandH0 (Gal(L / K)) Lˣ) := hField.1
  let : Finite (HerbrandHMinusOne (Gal(L / K)) Lˣ g) := hField.2
  let : Finite
      (HerbrandH0 (Gal(L / K)) (Multiplicative Int)) := hZ.1
  let : Finite
      (HerbrandHMinusOne (Gal(L / K)) (Multiplicative Int) g) := hZ.2
  have hZ0 :
      Nat.card (HerbrandH0 (Gal(L / K)) (Multiplicative Int)) =
        Module.finrank K L :=
    galoisGroupValueGroup_herbrandH0_card_eq_finrank K L
  have hZm1 :
      Nat.card (HerbrandHMinusOne
        (Gal(L / K)) (Multiplicative Int) g) = 1 :=
    galoisGroupValueGroup_herbrandHMinusOne_card_eq_one K L g
  have hZ_one :
      @herbrandQuotient (Gal(L / K)) (Multiplicative Int) _ _ _
          (galoisGroupValueGroupMulDistribMulAction K L) g hZ.1 hZ.2 =
        (Module.finrank K L : ℚ) := by
    rw [herbrandQuotient_eq_card_ratio, hZ0, hZm1]
    simp
  have hm1_actual :
      Nat.card (tateCohomology (Rep.ofAlgebraAutOnUnits K L) (-1)) = 1 :=
    unitsTateHminusOne_card_eq_one K L g hg
  have hm1_field :
      Nat.card (HerbrandHMinusOne (Gal(L / K)) Lˣ g) = 1 := by
    exact (Nat.card_congr
      (herbrandHminusOneEquivUnitsTateHminusOne K L g hg)).trans hm1_actual
  have hField_quotient :
      @herbrandQuotient (Gal(L / K)) Lˣ _ _ _
          (galoisGroupFieldUnitsMulDistribMulAction K L)
          g hField.1 hField.2 = (Module.finrank K L : ℚ) := by
    rw [hmult, hU_one, hZ_one]
    simp
  have h0_field_rat :
      (Nat.card (HerbrandH0 (Gal(L / K)) Lˣ) : ℚ) =
        (Module.finrank K L : ℚ) := by
    rw [← hField_quotient, herbrandQuotient_eq_card_ratio, hm1_field]
    simp
  have h0_field :
      Nat.card (HerbrandH0 (Gal(L / K)) Lˣ) = Module.finrank K L := by
    exact_mod_cast h0_field_rat
  constructor
  · exact
      (Nat.card_congr (herbrandH0EquivTateCohomologyZero K L)).symm.trans h0_field
  · exact hm1_actual

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_NormalBasisFiniteQuotient
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-! Provides the public declarations in the `LocalClassFieldTheory.ClassFormation.NormalBasisFiniteQuotient` Lean module. -/

namespace LocalClassFieldTheory
open LocalFieldTheory

open CyclicCohomology

noncomputable section

universe u

open scoped ValuativeRel
open Filter IsNonarchimedeanLocalField

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [Module.Finite 𝒪[K] 𝒪[L]]

/-- A quotient by a subgroup containing an ordinary principal-unit level is
finite. -/
theorem finite_chosenNormalBasisIntegerUnitsQuotient_of_principalUnits_le
    (m : Nat) (V : Subgroup 𝒪[L]ˣ) (h : principalUnits L m ≤ V) :
    Finite (𝒪[L]ˣ ⧸ V) := by
  let : Finite (IntegerUnitsModPrincipalUnitsAtLevel L m) :=
    integerUnitsModPrincipalUnitsAtLevel_finite_of_isNonarchimedeanLocalField L m
  exact Finite.of_surjective
    (integerUnitsModPrincipalUnitsToSubgroupQuotient L m V h)
    (integerUnitsModPrincipalUnitsToSubgroupQuotient_surjective L m V h)

/-- Finite-index boundary for the local class-field axiom: for sufficiently large `n`, every
actual subgroup with carrier `V^n` has finite quotient in `𝒪_Lˣ`. -/
theorem exists_finite_chosenNormalBasisIntegerUnitsQuotient :
    ∃ c : Nat, ∀ n : Nat, c ≤ n →
      ∀ (V : Subgroup 𝒪[L]ˣ),
        (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n →
          Finite (𝒪[L]ˣ ⧸ V) := by
  rcases exists_principalUnits_le_chosenNormalBasisPrincipalUnitSet
      (K := K) (L := L) with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro n hcn V hV
  rcases hc n hcn with ⟨m, hm⟩
  have hle : principalUnits L m ≤ V := by
    intro a ha
    change (a : 𝒪[L]ˣ) ∈ (V : Set 𝒪[L]ˣ)
    rw [hV]
    exact hm ha
  exact finite_chosenNormalBasisIntegerUnitsQuotient_of_principalUnits_le
    (L := L) m V hle

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_IntegerUnitsHerbrand
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
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

variable [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Module.Finite 𝒪[K] 𝒪[L]]

/-- At all sufficiently deep chosen normal-basis levels:
`H⁰(G,V)=H⁻¹(G,V)=1` implies that the integer-unit Herbrand quotient is
defined and equals `1`. -/
theorem exists_integerUnits_herbrandQuotient_eq_one_of_large_chosenNormalBasisLevel :
    ∃ c : Nat, ∀ n : Nat, c ≤ n →
      ∀ (V : Subgroup 𝒪[L]ˣ)
        (hV : (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
        (g : Gal(L / K)),
        (∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g) →
        (letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV;
          Subsingleton (HerbrandH0 (Gal(L / K)) V)) →
        (letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV;
          Subsingleton (HerbrandHMinusOne (Gal(L / K)) V g)) →
        letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV
        letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
        letI := chosenNormalBasisIntegerUnitsQuotMulDistribMulAction K L n V hV
        ∃ hU : HerbrandQuotientDefined (Gal(L / K)) 𝒪[L]ˣ g,
          @herbrandQuotient (Gal(L / K)) 𝒪[L]ˣ _ _ _
            (galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L)
            g hU.1 hU.2 = 1 := by
  rcases exists_finite_chosenNormalBasisIntegerUnitsQuotient
      (K := K) (L := L) with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro n hcn V hV g hg hH0 hHminusOne
  exact integerUnits_herbrandQuotient_eq_one_of_chosenNormalBasis
    K L n V hV (hc n hcn V hV) g hg hH0 hHminusOne

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_Main
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory
open CyclicCohomology

open LocalFieldTheory

/-!
# The local class-field axiom

For a cyclic extension of nonarchimedean local fields, the actual Tate
cohomology of `Lˣ` has cardinalities `[L : K]` in degree zero and `1` in
degree minus one.
-/

noncomputable section

open scoped ValuativeRel
open IsNonarchimedeanLocalField
open CyclicCohomology.ProfiniteCohomology.Herbrand

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
  [IsNonarchimedeanLocalField L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]

/-- The integer-unit Herbrand witness used by the local class-field axiom,
including the proof that its Herbrand quotient is one. -/
theorem exists_localIntegerUnitsHerbrandDefinedAndEqOne
    (g : Gal(L / K))
    (hg : ∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g) :
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    ∃ hU : HerbrandQuotientDefined (Gal(L / K)) 𝒪[L]ˣ g,
      @herbrandQuotient (Gal(L / K)) 𝒪[L]ˣ _ _ _
        (galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L)
        g hU.1 hU.2 = 1 := by
  rcases exists_chosenNormalBasisPrincipalUnitSubgroup
      (K := K) (L := L) with ⟨cV, hcV⟩
  rcases exists_chosenNormalBasisPrincipalUnit_herbrand_subsingleton
      (K := K) (L := L) g hg with ⟨cH, hcH⟩
  rcases exists_integerUnits_herbrandQuotient_eq_one_of_large_chosenNormalBasisLevel
      (K := K) (L := L) with ⟨cU, hcU⟩
  let n : Nat := max cV (max cH cU)
  have hcVn : cV ≤ n := le_max_left cV (max cH cU)
  have hrest : max cH cU ≤ n := le_max_right cV (max cH cU)
  have hcHn : cH ≤ n := le_trans (le_max_left cH cU) hrest
  have hcUn : cU ≤ n := le_trans (le_max_right cH cU) hrest
  rcases hcV n hcVn with ⟨V, hV, _hVprincipal⟩
  let := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction
    K L n V hV
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  let := chosenNormalBasisIntegerUnitsQuotMulDistribMulAction K L n V hV
  have hcoh := hcH n hcHn V hV
  rcases hcU n hcUn V hV g hg hcoh.1 hcoh.2 with ⟨hU, hUone⟩
  exact ⟨hU, hUone⟩

/-- Canonical choice of the integer-unit finiteness witness constructed by
the local normal-basis argument. -/
theorem localIntegerUnitsHerbrandDefined
    (g : Gal(L / K))
    (hg : ∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g) :
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    HerbrandQuotientDefined (Gal(L / K)) 𝒪[L]ˣ g :=
  Classical.choose (exists_localIntegerUnitsHerbrandDefinedAndEqOne K L g hg)

theorem localIntegerUnitsHerbrandQuotient_eq_one
    (g : Gal(L / K))
    (hg : ∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g) :
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    @herbrandQuotient (Gal(L / K)) 𝒪[L]ˣ _ _ _
      (galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L) g
      (localIntegerUnitsHerbrandDefined K L g hg).1
      (localIntegerUnitsHerbrandDefined K L g hg).2 = 1 :=
  Classical.choose_spec (exists_localIntegerUnitsHerbrandDefinedAndEqOne K L g hg)

/-- Finiteness of actual unit Tate `H⁰`, produced from the same local
normal-basis witness as the cardinality theorem. -/
theorem localFieldUnitsTateH0FiniteOfGenerator
    (g : Gal(L / K))
    (hg : ∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g) :
    Finite (tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0) :=
  unitsTateH0FiniteOfIntegerUnitsHerbrand K L g hg
    (localIntegerUnitsHerbrandDefined K L g hg)

/-- The local class-field-axiom theorem for a specified generator of the cyclic Galois group. -/
theorem localFieldUnits_tate_card_of_generator
    (g : Gal(L / K))
    (hg : ∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g) :
    letI := localFieldUnitsTateH0FiniteOfGenerator K L g hg
    Nat.card (tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0) = Module.finrank K L ∧
      Nat.card (tateCohomology (Rep.ofAlgebraAutOnUnits K L) (-1)) = 1 := by
  exact fieldUnits_tate_card_of_integerUnits_herbrand_eq_one
    K L g hg (localIntegerUnitsHerbrandDefined K L g hg)
      (localIntegerUnitsHerbrandQuotient_eq_one K L g hg)

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FiniteExtensionClassFieldAxiom
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.gLocallyCompact _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseIsUltrametricDist _root_.chosenFinitePlaceBaseIsValuativeTopology _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.chosenFinitePlaceBaseValuationCompatible _root_.chosenFinitePlaceBaseValuationIsNontrivial _root_.chosenFinitePlaceBaseValuativeRelIsNontrivial _root_.chosenFinitePlaceBaseValued _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory

open LocalFieldTheory

open ValuationTheory

open CyclicCohomology

/-!
# Finite local reciprocity

The local class-field-axiom theorem on finite extensions of a local field.

Mathlib's local-field predicate is topology-first, while the local class-field-axiom theorem also
needs a compatible local-field structure on the finite extension.  This file
constructs that structure from the spectral norm.  In particular, the target
valuation ring is proved integral over the base valuation ring; no local-field
structure on the target is assumed.
-/

noncomputable section

open scoped NNReal ValuativeRel

/-- The local class-field-axiom theorem for an arbitrary finite Galois extension of a
nonarchimedean local field.  All local-field data on the extension is
constructed from the spectral norm. -/
theorem finiteExtensionUnits_tate_card_of_generator
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (g : Gal(L / K))
    (hg : ∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g) :
    UnitsTateCardinalityData K L := by
  let : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  let : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  let : (Valued.v : Valuation K (ValuativeRel.ValueGroupWithZero K)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K) |>.comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  let : NontriviallyNormedField K :=
    Valued.toNontriviallyNormedField
      (L := K) (Γ₀ := ValuativeRel.ValueGroupWithZero K)

  let : NontriviallyNormedField L :=
    spectralNorm.nontriviallyNormedField K L
  let : NormedSpace K L := spectralNorm.normedSpace K L
  let : CompleteSpace L := spectralNorm.completeSpace K L
  let : LocallyCompactSpace L :=
    LocallyCompactSpace.of_finiteDimensional_of_complete K L
  let : IsUltrametricDist L :=
    ⟨fun x y z => by
      change ‖x - z‖ ≤ max ‖x - y‖ ‖y - z‖
      rw [← sub_add_sub_cancel x y z]
      exact isNonarchimedean_spectralNorm
        (K := K) (L := L) (x - y) (y - z)⟩
  let : Valued L ℝ≥0 := NormedField.toValued
  let vL : Valuation L ℝ≥0 := Valued.v
  let : vL.IsNontrivial :=
    (inferInstance : (NormedField.valuation (K := L)).IsNontrivial)
  let : ValuativeRel L := ValuativeRel.ofValuation vL
  let : vL.Compatible := Valuation.Compatible.ofValuation vL
  let : ValuativeRel.IsNontrivial L :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vL).2 inferInstance
  let : IsValuativeTopology L :=
    isValuativeTopology_of_valued_ofValuation L ℝ≥0
  let : IsNonarchimedeanLocalField L :=
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }

  let : (ValuativeRel.valuation K).HasExtension
      (ValuativeRel.valuation L) := by
    apply Valuation.HasExtension.ofComapInteger
    ext x
    change ValuativeRel.valuation L (algebraMap K L x) ≤ 1 ↔
      ValuativeRel.valuation K x ≤ 1
    rw [← (ValuativeRel.valuation L).vle_one_iff, vL.vle_one_iff]
    change spectralNorm K L (algebraMap K L x) ≤ 1 ↔
      ValuativeRel.valuation K x ≤ 1
    rw [spectralNorm_extends]
    exact Valued.toNormedField.norm_le_one_iff

  let : Algebra.IsIntegral
      (ValuativeRel.valuation K).valuationSubring
      (ValuativeRel.valuation L).valuationSubring := by
    change Algebra.IsIntegral 𝒪[K] 𝒪[L]
    refine ⟨?_⟩
    intro y
    apply IsIntegral.tower_bot
      (R := 𝒪[K]) (A := 𝒪[L]) (B := L)
      (Subring.subtype_injective (ValuativeRel.valuation L).integer)
    have hyv : vL (y : L) ≤ 1 := by
      apply (vL.vle_one_iff).1
      apply ((ValuativeRel.valuation L).vle_one_iff).2
      exact y.property
    have hynorm : ‖(y : L)‖ ≤ 1 := by
      have hynormNN : ‖(y : L)‖₊ ≤ 1 := by
        simpa [vL, NormedField.valuation_apply] using hyv
      exact_mod_cast hynormNN
    change spectralNorm K L (y : L) ≤ 1 at hynorm
    have hcoeffNorm :
        ∀ n : ℕ, ‖(minpoly K (y : L)).coeff n‖ ≤ 1 :=
      (spectralValue_le_one_iff
        (minpoly.monic (Algebra.IsIntegral.isIntegral (y : L)))).1
        (by simpa [spectralNorm] using hynorm)
    have hcoeff :
        (↑(minpoly K (y : L)).coeffs : Set K) ⊆
          (ValuativeRel.valuation K).integer := by
      intro c hc
      obtain ⟨n, _hn, rfl⟩ := Polynomial.mem_coeffs_iff.mp hc
      exact ((ValuativeRel.valuation K).mem_integer_iff _).2
        (Valued.toNormedField.norm_le_one_iff.mp (hcoeffNorm n))
    let p : Polynomial 𝒪[K] :=
      (minpoly K (y : L)).toSubring
        (ValuativeRel.valuation K).integer hcoeff
    refine ⟨p, ?_, ?_⟩
    · exact (Polynomial.monic_toSubring
        (minpoly K (y : L)) (ValuativeRel.valuation K).integer hcoeff).2
          (minpoly.monic (Algebra.IsIntegral.isIntegral (y : L)))
    · have hmaproot :
          Polynomial.aeval (y : L)
            (p.map (algebraMap 𝒪[K] K)) = 0 := by
        dsimp only [p]
        rw [show algebraMap 𝒪[K] K =
          (ValuativeRel.valuation K).integer.subtype from rfl,
          Polynomial.map_toSubring]
        exact minpoly.aeval K (y : L)
      rwa [Polynomial.aeval_map_algebraMap K (y : L) p] at hmaproot
  let hIntegralClosure : IsIntegralClosure
      (ValuativeRel.valuation L).valuationSubring
      (ValuativeRel.valuation K).valuationSubring L :=
    DiscreteValuationField.Valuation.valuationSubring_isIntegralClosure_of_isIntegral
      (ValuativeRel.valuation K) (ValuativeRel.valuation L)
  let : IsIntegralClosure 𝒪[L] 𝒪[K] L := by
    change IsIntegralClosure
      (ValuativeRel.valuation L).valuationSubring
      (ValuativeRel.valuation K).valuationSubring L
    exact hIntegralClosure
  let : Module.Finite 𝒪[K] 𝒪[L] :=
    integerRing_moduleFinite_of_isIntegralClosure K L

  let : Finite (tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0) :=
    localFieldUnitsTateH0FiniteOfGenerator K L g hg
  have hcard := localFieldUnits_tate_card_of_generator K L g hg
  exact
    { finiteH0 := inferInstance
      cardH0 := hcard.1
      cardHminusOne := hcard.2 }

/-- Tower form of the local class-field-axiom theorem.  It is enough that the lower field of the
cyclic extension be finite over a nonarchimedean local field; its local-field
structure is again supplied by the spectral norm. -/
theorem finiteTowerUnits_tate_card_of_generator
    (k K L : Type) [Field k] [Field K] [Field L]
    [Algebra k K] [FiniteDimensional k K]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (g : Gal(L / K))
    (hg : ∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g) :
    UnitsTateCardinalityData K L := by
  let : UniformSpace k := IsTopologicalAddGroup.rightUniformSpace k
  let : IsUniformAddGroup k := isUniformAddGroup_of_addCommGroup
  let : (Valued.v : Valuation k (ValuativeRel.ValueGroupWithZero k)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := k) |>.comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  let : NontriviallyNormedField k :=
    Valued.toNontriviallyNormedField
      (L := k) (Γ₀ := ValuativeRel.ValueGroupWithZero k)

  let : NontriviallyNormedField K :=
    spectralNorm.nontriviallyNormedField k K
  let : NormedSpace k K := spectralNorm.normedSpace k K
  let : CompleteSpace K := spectralNorm.completeSpace k K
  let : LocallyCompactSpace K :=
    LocallyCompactSpace.of_finiteDimensional_of_complete k K
  let : IsUltrametricDist K :=
    ⟨fun x y z => by
      change ‖x - z‖ ≤ max ‖x - y‖ ‖y - z‖
      rw [← sub_add_sub_cancel x y z]
      exact isNonarchimedean_spectralNorm
        (K := k) (L := K) (x - y) (y - z)⟩
  let : Valued K ℝ≥0 := NormedField.toValued
  let vK : Valuation K ℝ≥0 := Valued.v
  let : vK.IsNontrivial :=
    (inferInstance : (NormedField.valuation (K := K)).IsNontrivial)
  let : ValuativeRel K := ValuativeRel.ofValuation vK
  let : vK.Compatible := Valuation.Compatible.ofValuation vK
  let : ValuativeRel.IsNontrivial K :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vK).2 inferInstance
  let : IsValuativeTopology K :=
    isValuativeTopology_of_valued_ofValuation K ℝ≥0
  let : IsNonarchimedeanLocalField K :=
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }

  exact finiteExtensionUnits_tate_card_of_generator K L g hg

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_SeparableUnitsNorm
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientRepresentedQuotientFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.baseAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.fieldAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.baseRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.fieldRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.relativeRepresentedQuotientFinite _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

/-- Under the base-field fixed-unit equivalence, the abstract finite norm
subgroup is exactly the ordinary field-norm subgroup. -/
theorem map_finiteNormSubgroup_eq_additiveNormSubgroup :
    (finiteNormSubgroup (galoisAmbientUnitsRep K Ω)
      (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
      (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)).map
        (baseUnitsEquivGaloisAmbientFixed K Ω).symm.toAddMonoidHom =
      additiveNormSubgroup K E := by
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    rcases ha with ⟨b, rfl⟩
    let u : Eˣ := Additive.toMul
      ((intermediateFieldUnitsEquivGaloisFixed K Ω E).symm b)
    have hb :
        intermediateFieldUnitsEquivGaloisFixed K Ω E
            (Additive.ofMul u) = b := by
      change intermediateFieldUnitsEquivGaloisFixed K Ω E
          ((intermediateFieldUnitsEquivGaloisFixed K Ω E).symm b) = b
      exact (intermediateFieldUnitsEquivGaloisFixed K Ω E).apply_symm_apply b
    rw [← hb, relativeNorm_intermediateFieldUnit]
    change (baseUnitsEquivGaloisAmbientFixed K Ω).symm
      (baseUnitsEquivGaloisAmbientFixed K Ω
        (Additive.ofMul (normUnits K E u))) ∈ additiveNormSubgroup K E
    rw [(baseUnitsEquivGaloisAmbientFixed K Ω).symm_apply_apply]
    exact ⟨u, rfl⟩
  · intro hy
    change Additive.toMul y ∈ localNormSubgroup K E at hy
    rcases hy with ⟨u, hu⟩
    refine ⟨baseUnitsEquivGaloisAmbientFixed K Ω
      (Additive.ofMul (normUnits K E u)), ?_, ?_⟩
    · refine ⟨intermediateFieldUnitsEquivGaloisFixed K Ω E
        (Additive.ofMul u), ?_⟩
      exact relativeNorm_intermediateFieldUnit K Ω E u
    · change (baseUnitsEquivGaloisAmbientFixed K Ω).symm
        (baseUnitsEquivGaloisAmbientFixed K Ω
          (Additive.ofMul (normUnits K E u))) = y
      rw [(baseUnitsEquivGaloisAmbientFixed K Ω).symm_apply_apply]
      exact congrArg Additive.ofMul hu

end FiniteGaloisIntermediate

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_LocalResidueDatum
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientQuotientFinite _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientRepresentedQuotientFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.baseAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.fieldAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.baseRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.fieldRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.relativeRepresentedQuotientFinite _root_.ClassFormation.DegreeData.extensionInertiaWithin_normal _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.DegreeData.frobeniusElementsMul _root_.ClassFormation.DegreeData.frobeniusElementsSemigroup _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientAddCommGroup _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_isGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.ideleGroupIsTopologicalGroup _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.DegreeData.chosenUnramifiedFrobeniusLift_exponent _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.DegreeData.extensionNormalizedDegree_frobenius_mul _root_.ClassFormation.DegreeData.extensionNormalizedDegree_mk _root_.ClassFormation.DegreeData.extensionRestriction_mk _root_.ClassFormation.DegreeData.fieldImageAdd_index _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_apply _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_zero _root_.ClassFormation.DegreeData.fixedFieldNormalizedDegree_generator _root_.ClassFormation.DegreeData.frobeniusActionConjugate_coe _root_.ClassFormation.DegreeData.frobeniusClosureDegreeInMulNatRange_coe _root_.ClassFormation.DegreeData.frobeniusClosureDegree_generator _root_.ClassFormation.DegreeData.frobeniusExponent_actionConjugate _root_.ClassFormation.DegreeData.frobeniusExponent_chosenDegreeOneFrobeniusElement _root_.ClassFormation.DegreeData.frobeniusExponent_mul _root_.ClassFormation.DegreeData.frobeniusExponent_powerOfDegreeOne _root_.ClassFormation.DegreeData.frobeniusFixedFieldAction_coe _root_.ClassFormation.DegreeData.frobeniusFixedFieldQuotientEquiv_mk _root_.ClassFormation.DegreeData.frobeniusFixedFieldToClosure_apply _root_.ClassFormation.DegreeData.frobeniusFixedField_normalizedDegreeEquiv_apply _root_.ClassFormation.DegreeData.frobeniusLiftDifference_coe _root_.ClassFormation.DegreeData.frobeniusMul_coe _root_.ClassFormation.DegreeData.frobeniusPowerOfDegreeOne_coe _root_.ClassFormation.DegreeData.frobeniusPowerSum_coe _root_.ClassFormation.DegreeData.frobeniusQuotientAction_mk _root_.ClassFormation.DegreeData.frobeniusQuotientRepresentation_apply _root_.ClassFormation.DegreeData.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift _root_.ClassFormation.DegreeData.frobeniusRestriction_mul _root_.ClassFormation.DegreeData.maximalUnramifiedDegreeEquiv_frobenius _root_.ClassFormation.DegreeData.maximalUnramifiedDegreeEquiv_mk _root_.ClassFormation.DegreeData.maximalUnramifiedNormClass_eq_zero_iff _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientInfiniteEquiv_maximalUnramifiedNormClass _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientLift_maximalUnramifiedNormClass _root_.ClassFormation.DegreeData.maximalUnramifiedRestriction_mk _root_.ClassFormation.DegreeData.maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClass _root_.ClassFormation.DegreeData.mem_frobeniusFixedField_iff _root_.ClassFormation.DegreeData.mem_frobeniusFixedSubgroupWithin_iff _root_.ClassFormation.DegreeData.mem_maximalUnramifiedField_iff _root_.ClassFormation.DegreeData.mem_maximalUnramifiedNormSubgroup_iff _root_.ClassFormation.DegreeData.normalizedDegree_apply_toAdd _root_.ClassFormation.DegreeData.restrictedDegreeInMulNatRange_coe _root_.ClassFormation.FiniteGaloisSubextension.toGaloisSubextension_isTotallyRamified_iff _root_.ClassFormation.FiniteGaloisSubextension.toGaloisSubextension_isUnramified_iff _root_.ClassFormation.ValuationData.canonicalUnramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.canonicalValueQuotientHom_mk _root_.ClassFormation.ValuationData.canonicalValueReduction_one _root_.ClassFormation.ValuationData.mem_infiniteUnitAddSubgroup_iff _root_.ClassFormation.ValuationData.mem_infiniteUnitNormSubgroup_iff _root_.ClassFormation.ValuationData.mem_unitAddSubgroup_iff _root_.ClassFormation.ValuationData.oneValue_coe _root_.ClassFormation.ValuationData.unitRepresentation_quotient_mk_apply _root_.ClassFormation.ValuationData.unramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.unramifiedReciprocity_equiv_of_generator_apply _root_.ClassFormation.ValuationData.valuationAt_chosenPrimeElement _root_.ClassFormation.ValuationData.valuationAt_coe _root_.ClassFormation.ValuationData.valueModulo_apply _root_.ClassFormation.canonicalValueQuotientMap_mk _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.mem_nsmulImage_iff _root_.ClassFormation.nsmulImage_top _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatPowNat_apply_toAdd _root_.ClassFormation.zHatPowNat_one _root_.ClassFormation.zHatReductionMul_apply_toAdd _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.torsionQuotientEquivOfZHatMulDecomposition_mk _root_.KummerTheory.zHatUnitsContinuousMulEquivPrimeProduct_rationalCyclotomicCharacter _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.ClassFormation.DegreeData.inertiaConjugationCosetEquiv_mk _root_.infinitePlace_mult_smul
set_option synthInstance.maxHeartbeats 400000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory

open ClassFormation

open ValuationTheory RamificationTheory LocalFieldTheory

/-!
# Finite local reciprocity: the local residue degree datum

For a nonarchimedean local field `K`, this file makes the choices implicit in
the construction explicit.  The canonical local valuation is packaged as a complete
DVF, Chevalley's theorem chooses an extension to `AlgebraicClosure K`, and
that valuation is pulled back to `SeparableClosure K`.  Finite-separable
uniqueness shows that its decomposition subgroup is the whole Galois group.
The residue field of the decomposition field is then identified with the
finite residue field of `K`.

The remaining step is topological: the reduction action is shown continuous
for the two Krull topologies and is composed with the intrinsic finite-field
degree map from `ResidueAlgebraicClosureDegree`.  The selected residue field
is algebraically closed because its extension to the residue of
`AlgebraicClosure K` is purely inseparable and the selected residue field is
perfect over the finite base residue field.
-/

noncomputable section

open scoped Pointwise ValuativeRel
open _root_.RamificationTheory.HilbertRamification.ValuationSubring
open Field.absoluteGaloisGroup

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-! ## The canonical complete discrete valuation and its absolute extension -/

attribute [local instance] LocalClassFieldTheory.localSeparableClosureAlgebra
local instance localSeparableClosureScalarTower_re721a1_1 :
    IsScalarTower K (SeparableClosure K) (AlgebraicClosure K) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl
/-- The chosen absolute valuation ring pulls back to the canonical valuation
ring of `K`. -/
theorem localAbsoluteValuationSubring_pullback (x : K) :
    algebraMap K (AlgebraicClosure K) x ∈
        localAbsoluteValuationSubring K ↔
      x ∈ (localCompleteDVF K).valuation.valuationSubring := by
  rcases Classical.choose_spec
      (ValuationTheory.DiscreteValuationField.Valuation.exists_extension_valuationSubring
        (L := AlgebraicClosure K) (localCompleteDVF K).valuation) with
    ⟨_hmap, _hlocal, hpullback⟩
  exact hpullback x

/-- The valuation ring on the separable closure used in finite local reciprocity.
We choose it
as the pullback of the auxiliary valuation ring on the algebraic closure. -/
noncomputable def localSeparableValuationSubring :
    ValuationSubring (SeparableClosure K) :=
  (localAbsoluteValuationSubring K).comap
    (algebraMap (SeparableClosure K) (AlgebraicClosure K))

/-- Pulling the separable valuation subring back to `K` recovers the base valuation ring. -/
theorem localSeparableValuationSubring_pullback (x : K) :
    algebraMap K (SeparableClosure K) x ∈
        localSeparableValuationSubring K ↔
      x ∈ (localCompleteDVF K).valuation.valuationSubring := by
  change algebraMap (SeparableClosure K) (AlgebraicClosure K)
      (algebraMap K (SeparableClosure K) x) ∈
        localAbsoluteValuationSubring K ↔ _
  rw [← IsScalarTower.algebraMap_apply K (SeparableClosure K)
    (AlgebraicClosure K)]
  exact localAbsoluteValuationSubring_pullback K x

/-- The valuation on the separable closure extends the base discrete valuation. -/
noncomputable instance localSeparableValuationHasExtension :
    (localCompleteDVF K).valuation.HasExtension
      (localSeparableValuationSubring K).valuation :=
  ValuationTheory.DiscreteValuationField.Valuation.hasExtension_valuation_of_valuationSubring_pullback
    (localCompleteDVF K).valuation (localSeparableValuationSubring K)
      (localSeparableValuationSubring_pullback K)

/-- The extension valuation on the separable closure is independent of the
auxiliary Chevalley choice.  Equality is checked at the finite separable
field generated by one element and follows there from Henselian uniqueness. -/
theorem localSeparableValuationSubring_eq_of_hasExtension
    (B : ValuationSubring (SeparableClosure K))
    [(localCompleteDVF K).valuation.HasExtension B.valuation] :
    localSeparableValuationSubring K = B := by
  ext z
  let E : IntermediateField K (SeparableClosure K) :=
    IntermediateField.adjoin K ({z} : Set (SeparableClosure K))
  let : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional
      (Algebra.IsIntegral.isIntegral z)
  let : Algebra.IsSeparable K E := inferInstance
  obtain ⟨target, hExt, _hIntegralClosure, _hFundamental⟩ :=
    ValuationTheory.DiscreteValuationField.ValuedExtension.exists_integralClosure_standard_fundamental_identity
      (K := K) (L := E) (localCompleteDVF K)
  let : (localCompleteDVF K).valuation.HasExtension target.valuation := hExt
  let : IsScalarTower (localCompleteDVF K).valuationSubring
      target.valuationSubring E :=
    ValuationTheory.DiscreteValuationField.Valuation.valuationSubring_isScalarTower_of_hasExtension
      (localCompleteDVF K).valuation target.valuation
  let Ares := (localSeparableValuationSubring K).restrictIntermediateField E
  let Bres := B.restrictIntermediateField E
  let : (localCompleteDVF K).valuation.HasExtension Ares.valuation :=
    RamificationTheory.ValuationSubring.restrictIntermediateField_hasExtension
      (localCompleteDVF K).valuation (localSeparableValuationSubring K) E
  let : (localCompleteDVF K).valuation.HasExtension Bres.valuation :=
    RamificationTheory.ValuationSubring.restrictIntermediateField_hasExtension
      (localCompleteDVF K).valuation B E
  have hA : target.valuation.valuationSubring = Ares :=
    ValuationTheory.DiscreteValuationField.ValuedExtension.target_valuationSubring_eq_of_finite_separable
      (localCompleteDVF K) target Ares
  have hB : target.valuation.valuationSubring = Bres :=
    ValuationTheory.DiscreteValuationField.ValuedExtension.target_valuationSubring_eq_of_finite_separable
      (localCompleteDVF K) target Bres
  have hAB : Ares = Bres := hA.symm.trans hB
  let zE : E :=
    ⟨z, IntermediateField.subset_adjoin (F := K)
      (S := ({z} : Set (SeparableClosure K))) (by simp)⟩
  change zE ∈ Ares ↔ zE ∈ Bres
  rw [hAB]

/-- Every automorphism of the separable closure preserves the unique
extension of the Henselian local valuation. -/
theorem localSeparableDecompositionGroup_eq_top :
    decompositionGroup K (localSeparableValuationSubring K) = ⊤ := by
  apply top_unique
  intro sigma _hsigma
  change sigma • localSeparableValuationSubring K =
    localSeparableValuationSubring K
  let : (localCompleteDVF K).valuation.HasExtension
      (sigma • localSeparableValuationSubring K).valuation :=
    RamificationTheory.ValuationSubring.smul_hasExtension
      (localCompleteDVF K).valuation (localSeparableValuationSubring K) sigma
  exact (localSeparableValuationSubring_eq_of_hasExtension K
    (sigma • localSeparableValuationSubring K)).symm

/-! ## Identification of the finite base residue field -/

/-- When the decomposition subgroup is top, the valuation ring on the
decomposition field is the original local valuation ring. -/
noncomputable def localBaseValuationSubringEquivDecompositionField :
    (localCompleteDVF K).valuationSubring ≃+*
      decompositionFieldValuationSubring K
        (localSeparableValuationSubring K) := by
  let A := localSeparableValuationSubring K
  let Z := decompositionField K A
  have hZ : Z = ⊥ := by
    change IntermediateField.fixedField (decompositionGroup K A) = ⊥
    rw [localSeparableDecompositionGroup_eq_top K]
    simpa using
      (InfiniteGalois.fixedField_fixingSubgroup
        (⊥ : IntermediateField K (SeparableClosure K)))
  let eKZ : K ≃ₐ[K] Z :=
    (IntermediateField.botEquiv K (SeparableClosure K)).symm.trans
      (IntermediateField.equivOfEq hZ.symm)
  refine
    { toFun := fun x => ⟨eKZ (x : K), ?_⟩
      invFun := fun z => ⟨eKZ.symm (z : Z), ?_⟩
      left_inv := fun x => by
        apply Subtype.ext
        exact eKZ.symm_apply_apply (x : K)
      right_inv := fun z => by
        apply Subtype.ext
        exact eKZ.apply_symm_apply (z : Z)
      map_add' := fun x y => by
        apply Subtype.ext
        exact map_add eKZ (x : K) (y : K)
      map_mul' := fun x y => by
        apply Subtype.ext
        exact map_mul eKZ (x : K) (y : K) }
  · change ((eKZ x : Z) : SeparableClosure K) ∈ A
    have he : ((eKZ x : Z) : SeparableClosure K) =
        algebraMap K (SeparableClosure K) (x : K) := by
      rfl
    rw [he]
    exact (localSeparableValuationSubring_pullback K (x : K)).2 x.property
  · change eKZ.symm (z : Z) ∈
      (localCompleteDVF K).valuation.valuationSubring
    apply (localSeparableValuationSubring_pullback K (eKZ.symm (z : Z))).1
    have he : algebraMap K (SeparableClosure K) (eKZ.symm (z : Z)) =
        ((z : Z) : SeparableClosure K) := by
      exact congrArg Subtype.val (eKZ.apply_symm_apply (z : Z))
    rw [he]
    exact z.property

/-- The residue field in the residue-action exact sequence is canonically the finite residue
field of the original local field. -/
noncomputable def localBaseResidueEquivDecompositionResidue :
    (localCompleteDVF K).residueField ≃+*
      decompositionResidueField K (localSeparableValuationSubring K) :=
  (IsLocalRing.ResidueField.mapEquiv
      (localBaseValuationSubringEquivDecompositionField K)).trans
    (decompositionFieldResidueEquiv (K := K)
      (localSeparableValuationSubring K))

/-- Naturality of the base-residue comparison with the literal reduction
map into the selected residue field.  This is the scalar square used when
transporting residue degrees from the residue-action presentation back
to the canonical residue fields of local extensions. -/
theorem localBaseResidueEquivDecompositionResidue_algebraMap
    (x : (localCompleteDVF K).valuationSubring) :
    algebraMap
        (decompositionResidueField K (localSeparableValuationSubring K))
        (selectedResidueField (localSeparableValuationSubring K))
        (localBaseResidueEquivDecompositionResidue K
          (IsLocalRing.residue (localCompleteDVF K).valuationSubring x)) =
      IsLocalRing.residue (localSeparableValuationSubring K)
        (⟨algebraMap K (SeparableClosure K) (x : K),
          (localSeparableValuationSubring_pullback K (x : K)).2
            x.property⟩ : localSeparableValuationSubring K) := by
  rfl

/-- The residue field attached to the local decomposition datum is finite. -/
noncomputable instance localDecompositionResidueFinite :
    Finite (decompositionResidueField K
      (localSeparableValuationSubring K)) := by
  have : Finite (localCompleteDVF K).residueField := by
    change Finite 𝓀[K]
    infer_instance
  exact Finite.of_equiv (localCompleteDVF K).residueField
    (localBaseResidueEquivDecompositionResidue K).toEquiv

/-- The finite local decomposition residue field has a canonical finite enumeration. -/
noncomputable instance localDecompositionResidueFintype :
    Fintype (decompositionResidueField K
      (localSeparableValuationSubring K)) :=
  Fintype.ofFinite _

/-- The selected residue field of the separable valuation is algebraically closed. -/
instance localSelectedResidueIsAlgClosed :
    IsAlgClosed (selectedResidueField
      (localSeparableValuationSubring K)) := by
  let A := localAbsoluteValuationSubring K
  let B := localSeparableValuationSubring K
  let barI := valuationSubringComapResidueMap
    (F := SeparableClosure K) A
  let : Algebra (selectedResidueField B) (selectedResidueField A) :=
    barI.toAlgebra
  let : IsPurelyInseparable (SeparableClosure K) (AlgebraicClosure K) :=
    separableClosure.isPurelyInseparable K (AlgebraicClosure K)
  let : IsPurelyInseparable (selectedResidueField B)
      (selectedResidueField A) :=
    valuationSubring_comap_residueField_isPurelyInseparable
      (F := SeparableClosure K) A
  let : PerfectField (decompositionResidueField K B) := inferInstance
  let : Algebra.IsAlgebraic (decompositionResidueField K B)
      (selectedResidueField B) := inferInstance
  let : PerfectField (selectedResidueField B) :=
    Algebra.IsAlgebraic.perfectField
      (K := decompositionResidueField K B)
      (L := selectedResidueField B)
  let : Algebra.IsSeparable (selectedResidueField B)
      (selectedResidueField A) := inferInstance
  have hsurjective : Function.Surjective barI :=
    IsPurelyInseparable.surjective_algebraMap_of_isSeparable
      (selectedResidueField B) (selectedResidueField A)
  let e : selectedResidueField B ≃+* selectedResidueField A :=
    RingEquiv.ofBijective barI ⟨barI.injective, hsurjective⟩
  let : IsAlgClosed (selectedResidueField A) :=
    valuationSubring_residueField_isAlgClosed A
  exact IsAlgClosed.of_ringEquiv (selectedResidueField A)
    (selectedResidueField B) e.symm

/-! ## Continuity of reduction and the local degree map -/

/-- A fixed representative in the chosen valuation ring of a residue class. -/
noncomputable def localSelectedResidueLift
    (x : selectedResidueField (localSeparableValuationSubring K)) :
    localSeparableValuationSubring K :=
  Classical.choose (IsLocalRing.residue_surjective x)

@[simp]
theorem localSelectedResidueLift_residue
    (x : selectedResidueField (localSeparableValuationSubring K)) :
    IsLocalRing.residue (localSeparableValuationSubring K)
        (localSelectedResidueLift K x) = x :=
  Classical.choose_spec (IsLocalRing.residue_surjective x)

/-- Reduction from the absolute Galois group to the absolute Galois group of
the residue field is continuous for the Krull topologies.  A finite residue
subextension is controlled by adjoining to `K` one lift of each of its
finitely many elements. -/
theorem localSeparableResidueAlgAction_continuous :
    Continuous
      (residueAlgActionOfEqTop K
        (localSeparableValuationSubring K)
        (localSeparableDecompositionGroup_eq_top K)) := by
  classical
  let A := localSeparableValuationSubring K
  let k : Type := decompositionResidueField K A
  let Omega : Type := selectedResidueField A
  let hA := localSeparableDecompositionGroup_eq_top K
  let rho := residueAlgActionOfEqTop K A hA
  refine continuous_of_continuousAt_one rho ?_
  rw [ContinuousAt, MonoidHom.map_one, Filter.Tendsto]
  intro s hs
  rw [Filter.mem_map]
  rcases (krullTopology_mem_nhds_one_iff k Omega s).1 hs with
    ⟨E, hE, hEs⟩
  let : Algebra k E := E.algebra
  let : FiniteDimensional k E := hE
  let : Finite E := Module.finite_of_finite
    (decompositionResidueField K (localSeparableValuationSubring K))
  let : Fintype E := Fintype.ofFinite E
  let lifts : Finset (SeparableClosure K) :=
    Finset.univ.image (fun x : E =>
      ((localSelectedResidueLift K (x : Omega) : A) : SeparableClosure K))
  let F : IntermediateField K (SeparableClosure K) :=
    IntermediateField.adjoin K (lifts : Set (SeparableClosure K))
  let : FiniteDimensional K F :=
    IntermediateField.finiteDimensional_adjoin (fun x _hx =>
      Algebra.IsIntegral.isIntegral x)
  refine (krullTopology_mem_nhds_one_iff K (SeparableClosure K)
    (rho ⁻¹' s)).2 ?_
  refine ⟨F, inferInstance, ?_⟩
  intro sigma hsigma
  apply hEs
  change rho sigma ∈ E.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  let y : E := ⟨x, hx⟩
  let a : A := localSelectedResidueLift K (y : Omega)
  have ha_lifts : (a : SeparableClosure K) ∈ lifts := by
    apply Finset.mem_image.mpr
    exact ⟨y, Finset.mem_univ y, rfl⟩
  have haF : (a : SeparableClosure K) ∈ F :=
    IntermediateField.subset_adjoin (F := K)
      (S := (lifts : Set (SeparableClosure K))) ha_lifts
  have hfix : sigma (a : SeparableClosure K) = (a : SeparableClosure K) :=
    (IntermediateField.mem_fixingSubgroup_iff F sigma).mp hsigma
      (a : SeparableClosure K) haF
  change rho sigma (y : Omega) = (y : Omega)
  rw [← localSelectedResidueLift_residue K (y : Omega)]
  change IsLocalRing.residue A
      ((toDecompositionGroupOfEqTop
        K A hA sigma) • a) = IsLocalRing.residue A a
  congr 1
  apply Subtype.ext
  exact hfix

/-- The continuous residue action on the chosen residue algebraic closure. -/
noncomputable def localSeparableResidueAlgAction :
    Gal(SeparableClosure K / K) →ₜ*
      (selectedResidueField (localSeparableValuationSubring K) ≃ₐ[
        decompositionResidueField K (localSeparableValuationSubring K)]
          selectedResidueField (localSeparableValuationSubring K)) where
  toMonoidHom :=
    residueAlgActionOfEqTop K
      (localSeparableValuationSubring K)
      (localSeparableDecompositionGroup_eq_top K)
  continuous_toFun := localSeparableResidueAlgAction_continuous K

/-- Every automorphism of the selected residue extension lifts to the separable Galois group. -/
theorem localSeparableResidueAlgAction_surjective :
    Function.Surjective (localSeparableResidueAlgAction K) :=
  residueAlgActionOfEqTop_surjective K
    (localSeparableValuationSubring K)
    (localSeparableDecompositionGroup_eq_top K)

/-- **Finite local reciprocity, local degree map.**  The residue Frobenius degree,
defined directly on the separable-closure model used by the local reciprocity
formalization. -/
noncomputable def localResidueDegree :
    Gal(SeparableClosure K / K) →ₜ* ZHatMul where
  toMonoidHom :=
    (residueAbsoluteDegreeIn
      (decompositionResidueField K (localSeparableValuationSubring K))
      (selectedResidueField (localSeparableValuationSubring K))).toMonoidHom.comp
        (localSeparableResidueAlgAction K).toMonoidHom
  continuous_toFun :=
    (residueAbsoluteDegreeIn
      (decompositionResidueField K (localSeparableValuationSubring K))
      (selectedResidueField
        (localSeparableValuationSubring K))).continuous_toFun.comp
      (localSeparableResidueAlgAction K).continuous_toFun

/-- The local residue-degree map onto the profinite integers is surjective. -/
theorem localResidueDegree_surjective :
    Function.Surjective (localResidueDegree K) := by
  intro z
  obtain ⟨tau, htau⟩ :=
    (residueDatumIn
      (decompositionResidueField K (localSeparableValuationSubring K))
      (selectedResidueField
        (localSeparableValuationSubring K))).degree_surjective z
  obtain ⟨sigma, hsigma⟩ :=
    localSeparableResidueAlgAction_surjective K tau
  refine ⟨sigma, ?_⟩
  change residueAbsoluteDegreeIn
      (decompositionResidueField K (localSeparableValuationSubring K))
      (selectedResidueField (localSeparableValuationSubring K))
        (localSeparableResidueAlgAction K sigma) = z
  rw [hsigma]
  simpa [residueDatumIn] using htau

/-- **Finite local reciprocity.**  The actual abstract class-formation datum
`d : G_K -> ZHat` furnished by the residue action of a local field. -/
noncomputable def localResidueDatum :
    DegreeData (Gal(SeparableClosure K / K)) where
  degree := localResidueDegree K
  degree_surjective := localResidueDegree_surjective K

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FiniteSubgroupResidueDegree
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientQuotientFinite _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientRepresentedQuotientFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.baseAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.fieldAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.baseRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.fieldRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.relativeRepresentedQuotientFinite _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.DegreeData.frobeniusElementsMul _root_.ClassFormation.DegreeData.frobeniusElementsSemigroup _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.conjugateExtension_normal _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.HilbertRamification.Dedekind.basePrime_isPrime _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_isGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeDegreeIntermediate_top_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.ideleGroupIsTopologicalGroup _root_.primeOrderFixedField_isGalois _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory
open CyclicCohomology RamificationTheory ClassFormation

open LocalFieldTheory

/-!
# Finite local reciprocity: residue degree of a finite abstract field

This file compares the residue action used by localResidueDatum with the
same residue action after changing the ground field to the fixed field of a
closed subgroup.  The comparison is made on the common selected
residue field, so it also applies when the fixed field is not normal over the
original local field.
-/

noncomputable section

open scoped Pointwise ValuativeRel
open _root_.RamificationTheory.HilbertRamification.ValuationSubring
open Field.absoluteGaloisGroup

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The residue subfield inside the selected residue algebraic closure which
is generated by the residue field attached to the fixed field of `H`.

We use `adjoin` rather than imposing a scalar-tower instance between the two
intrinsic residue-action quotient presentations. -/
noncomputable def localAbstractFixedResidueIntermediateField
    (H : ClosedSubgroup (Gal(SeparableClosure K / K))) :
    IntermediateField
      (decompositionResidueField K (localSeparableValuationSubring K))
      (selectedResidueField (localSeparableValuationSubring K)) := by
  let E := abstractFixedField K (SeparableClosure K) H
  let A := localSeparableValuationSubring K
  let k := decompositionResidueField K A
  let Omega := selectedResidueField A
  let kE := decompositionResidueField E A
  exact IntermediateField.adjoin k
    (Set.range (algebraMap kE Omega))

/-- The canonical scalar structure on the selected fixed residue field.
Naming these instances keeps typeclass search from unfolding the fixed-field
and residue-action constructions in finite-dimensionality statements. -/
noncomputable local instance localAbstractFixedResidueIntermediateFieldAlgebra
    (H : ClosedSubgroup (Gal(SeparableClosure K / K))) :
    Algebra
      (decompositionResidueField K (localSeparableValuationSubring K))
      (localAbstractFixedResidueIntermediateField K H) :=
  (localAbstractFixedResidueIntermediateField K H).algebra

noncomputable local instance localAbstractFixedResidueIntermediateFieldSMul_re721a1_1
    (H : ClosedSubgroup (Gal(SeparableClosure K / K))) :
    SMul
      (decompositionResidueField K (localSeparableValuationSubring K))
      (localAbstractFixedResidueIntermediateField K H) :=
  @Algebra.toSMul _ _ _ _
    (localAbstractFixedResidueIntermediateFieldAlgebra K H)
noncomputable local instance localAbstractFixedResidueIntermediateFieldModule
    (H : ClosedSubgroup (Gal(SeparableClosure K / K))) :
    Module
      (decompositionResidueField K (localSeparableValuationSubring K))
      (localAbstractFixedResidueIntermediateField K H) :=
  @Algebra.toModule _ _ _ _
    (localAbstractFixedResidueIntermediateFieldAlgebra K H)

/-- Every automorphism over the fixed field preserves the selected extension
valuation.  This is the base-change form of the full decomposition-group
statement proved for `K`. -/
theorem localAbstractFixedDecompositionGroup_eq_top
    (H : ClosedSubgroup (Gal(SeparableClosure K / K))) :
    decompositionGroup (abstractFixedField K (SeparableClosure K) H)
      (localSeparableValuationSubring K) = ⊤ := by
  let E := abstractFixedField K (SeparableClosure K) H
  let A := localSeparableValuationSubring K
  apply top_unique
  intro tau _htau
  let sigma : Gal(SeparableClosure K / K) := tau.restrictScalars K
  have hsigma : sigma • A = A := by
    change sigma ∈ decompositionGroup K A
    rw [localSeparableDecompositionGroup_eq_top K]
    exact Subgroup.mem_top sigma
  change tau • A = A
  exact hsigma

/-- Restricting the local residue action to `H` gives the same underlying
automorphism of the selected residue field as applying the residue-action map
over the fixed field of `H`. -/
theorem localAbstractFixedResidueAction_apply
    (H : ClosedSubgroup (Gal(SeparableClosure K / K)))
    (sigma : H.toSubgroup)
    (x : selectedResidueField (localSeparableValuationSubring K)) :
    localSeparableResidueAlgAction K sigma.1 x =
      residueAlgActionOfEqTop
        (abstractFixedField K (SeparableClosure K) H)
        (localSeparableValuationSubring K)
        (localAbstractFixedDecompositionGroup_eq_top K H)
        (abstractSubgroupEquivGaloisGroup K (SeparableClosure K) H sigma) x := by
  let A := localSeparableValuationSubring K
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  change IsLocalRing.residue A
      ((toDecompositionGroupOfEqTop K A
        (localSeparableDecompositionGroup_eq_top K) sigma.1) • a) =
    IsLocalRing.residue A
      ((toDecompositionGroupOfEqTop
        (abstractFixedField K (SeparableClosure K) H) A
        (localAbstractFixedDecompositionGroup_eq_top K H)
        (abstractSubgroupEquivGaloisGroup K (SeparableClosure K) H sigma)) • a)
  congr 1

/-- The image of `H` under the local residue action is exactly the subgroup
fixing the residue subfield of its fixed field.  The reverse inclusion is the
surjectivity of the residue-action map after changing the base to that
fixed field. -/
theorem localAbstractFixedResidueAction_map_eq_fixingSubgroup
    (H : ClosedSubgroup (Gal(SeparableClosure K / K))) :
    H.toSubgroup.map (localSeparableResidueAlgAction K).toMonoidHom =
      (localAbstractFixedResidueIntermediateField K H).fixingSubgroup := by
  let E := abstractFixedField K (SeparableClosure K) H
  let A := localSeparableValuationSubring K
  let k := decompositionResidueField K A
  let Omega := selectedResidueField A
  let kE := decompositionResidueField E A
  let rhoK := localSeparableResidueAlgAction K
  let hE := localAbstractFixedDecompositionGroup_eq_top K H
  let rhoE := residueAlgActionOfEqTop E A hE
  let F := localAbstractFixedResidueIntermediateField K H
  ext tau
  constructor
  · rintro ⟨sigma, hsigma, rfl⟩
    let sigmaH : H.toSubgroup := ⟨sigma, hsigma⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    let T : IntermediateField k Omega :=
      { carrier := {y | rhoK sigma y = y}
        zero_mem' := by simp
        one_mem' := by simp
        add_mem' := by
          intro y z hy hz
          change rhoK sigma y = y at hy
          change rhoK sigma z = z at hz
          change rhoK sigma (y + z) = y + z
          rw [map_add]
          exact congrArg₂ (fun a b : Omega => a + b) hy hz
        mul_mem' := by
          intro y z hy hz
          change rhoK sigma y = y at hy
          change rhoK sigma z = z at hz
          change rhoK sigma (y * z) = y * z
          rw [map_mul]
          exact congrArg₂ (fun a b : Omega => a * b) hy hz
        algebraMap_mem' := fun y => (rhoK sigma).commutes y
        inv_mem' := by
          intro y hy
          change rhoK sigma y = y at hy
          simp [hy] }
    have hrange : Set.range (algebraMap kE Omega) ⊆ T := by
      rintro y ⟨z, rfl⟩
      have hbase : rhoK sigma (algebraMap kE Omega z) =
          algebraMap kE Omega z := by
        rw [localAbstractFixedResidueAction_apply K H sigmaH]
        exact (rhoE (abstractSubgroupEquivGaloisGroup
          K (SeparableClosure K) H sigmaH)).commutes z
      change rhoK sigma (algebraMap kE Omega z) =
        algebraMap kE Omega z
      exact hbase
    have hFT : F ≤ T := by
      apply IntermediateField.adjoin_le_iff.mpr
      exact hrange
    have hxT : x ∈ T := hFT hx
    change rhoK sigma x = x
    change rhoK sigma x = x at hxT
    exact hxT
  · intro htau
    let tauE : Omega ≃ₐ[kE] Omega :=
      { tau.toRingEquiv with
        commutes' := fun z => by
          have hzF : algebraMap kE Omega z ∈ F := by
            apply IntermediateField.subset_adjoin
            exact ⟨z, rfl⟩
          exact (IntermediateField.mem_fixingSubgroup_iff F tau).mp
            htau (algebraMap kE Omega z) hzF }
    obtain ⟨sigmaE, hsigmaE⟩ :=
      residueAlgActionOfEqTop_surjective E A hE tauE
    let sigmaH : H.toSubgroup :=
      (abstractSubgroupEquivGaloisGroup K (SeparableClosure K) H).symm sigmaE
    refine ⟨sigmaH.1, sigmaH.2, ?_⟩
    apply AlgEquiv.ext
    intro x
    change localSeparableResidueAlgAction K sigmaH.1 x = tau x
    rw [localAbstractFixedResidueAction_apply K H sigmaH]
    have hsigmaH : abstractSubgroupEquivGaloisGroup
        K (SeparableClosure K) H sigmaH = sigmaE :=
      (abstractSubgroupEquivGaloisGroup
        K (SeparableClosure K) H).apply_symm_apply sigmaE
    rw [hsigmaH, hsigmaE]
    rfl

/-- The residue action of an element of `H` fixes the finite residue
subfield attached to the fixed field of `H`. -/
theorem localAbstractFixedResidueAction_mem_fixingSubgroup
    (H : ClosedSubgroup (Gal(SeparableClosure K / K)))
    (sigma : H.toSubgroup) :
    localSeparableResidueAlgAction K sigma.1 ∈
      (localAbstractFixedResidueIntermediateField K H).fixingSubgroup := by
  rw [← localAbstractFixedResidueAction_map_eq_fixingSubgroup K H]
  exact ⟨sigma.1, sigma.2, rfl⟩

/-- The residue action of `H`, with scalars restricted to the actual finite
residue subfield selected by `H` inside the common residue algebraic
closure. -/
noncomputable def localAbstractFixedResidueActionOverIntermediateField
    (H : ClosedSubgroup (Gal(SeparableClosure K / K))) :
    H.toSubgroup →*
      (selectedResidueField (localSeparableValuationSubring K) ≃ₐ[
        localAbstractFixedResidueIntermediateField K H]
        selectedResidueField (localSeparableValuationSubring K)) := by
  let F := localAbstractFixedResidueIntermediateField K H
  let rhoH : H.toSubgroup →*
      (selectedResidueField (localSeparableValuationSubring K) ≃ₐ[
        decompositionResidueField K (localSeparableValuationSubring K)]
        selectedResidueField (localSeparableValuationSubring K)) :=
    (localSeparableResidueAlgAction K).toMonoidHom.comp H.toSubgroup.subtype
  let rhoF : H.toSubgroup →* F.fixingSubgroup :=
    rhoH.codRestrict F.fixingSubgroup
      (localAbstractFixedResidueAction_mem_fixingSubgroup K H)
  exact
    (IntermediateField.fixingSubgroupEquiv F).toMonoidHom.comp rhoF

/-- Restricting residue scalars changes only the scalar-linearity proof,
not the underlying automorphism of the selected residue field. -/
@[simp]
theorem localAbstractFixedResidueActionOverIntermediateField_apply
    (H : ClosedSubgroup (Gal(SeparableClosure K / K)))
    (sigma : H.toSubgroup)
    (x : selectedResidueField (localSeparableValuationSubring K)) :
    localAbstractFixedResidueActionOverIntermediateField K H sigma x =
      localSeparableResidueAlgAction K sigma.1 x := by
  rfl

/-- A finite abstract field has a genuinely finite residue subfield inside
the selected residue algebraic closure.  Finiteness is deduced from the
finite index of `H`: surjectivity of the absolute residue action makes the
index of its image divide the index of `H`. -/
theorem localAbstractFixedResidueIntermediateField_finiteDimensional
    (H : ClosedSubgroup (Gal(SeparableClosure K / K)))
    [Finite
      ((baseField (Gal(SeparableClosure K / K))).toSubgroup ⧸
        extensionSubgroup
          (baseField (Gal(SeparableClosure K / K))) H
          (le_baseField H))] :
    FiniteDimensional
      (decompositionResidueField K (localSeparableValuationSubring K))
      (localAbstractFixedResidueIntermediateField K H) := by
  let G := Gal(SeparableClosure K / K)
  let A := localSeparableValuationSubring K
  let k := decompositionResidueField K A
  let Omega := selectedResidueField A
  let rho := (localSeparableResidueAlgAction K).toMonoidHom
  let F := localAbstractFixedResidueIntermediateField K H
  let : Finite (G ⧸ H.toSubgroup) :=
    ambientQuotientFiniteOfAbstractFinite
      K (SeparableClosure K) H inferInstance
  have hHindex : H.toSubgroup.index ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  have hmapIndex : (H.toSubgroup.map rho).index ≠ 0 := by
    intro hzero
    have hdiv : (H.toSubgroup.map rho).index ∣ H.toSubgroup.index :=
      H.toSubgroup.index_map_dvd (localSeparableResidueAlgAction_surjective K)
    rw [hzero] at hdiv
    exact hHindex (eq_zero_of_zero_dvd hdiv)
  let : Finite
      ((Omega ≃ₐ[k] Omega) ⧸ H.toSubgroup.map rho) :=
    (Subgroup.index_ne_zero_iff_finite (H := H.toSubgroup.map rho)).mp
      hmapIndex
  have himage : H.toSubgroup.map rho = F.fixingSubgroup :=
    localAbstractFixedResidueAction_map_eq_fixingSubgroup K H
  let : Finite ((Omega ≃ₐ[k] Omega) ⧸ F.fixingSubgroup) := by
    rw [← himage]
    infer_instance
  let : Subgroup.FiniteIndex F.fixingSubgroup :=
    F.fixingSubgroup.finiteIndex_of_finite_quotient
  apply (InfiniteGalois.isOpen_iff_finite (K := Omega) F).1
  exact Subgroup.isOpen_of_isClosed_of_finiteIndex
    F.fixingSubgroup (InfiniteGalois.fixingSubgroup_isClosed F)

/-- The finite residue subfield, packaged in the form used by the intrinsic
finite-field residue datum. -/
noncomputable def localAbstractFixedResidueFiniteGaloisIntermediateField
    (H : ClosedSubgroup (Gal(SeparableClosure K / K)))
    [Finite
      ((baseField (Gal(SeparableClosure K / K))).toSubgroup ⧸
        extensionSubgroup
          (baseField (Gal(SeparableClosure K / K))) H
          (le_baseField H))] :
    FiniteGaloisIntermediateField
      (decompositionResidueField K (localSeparableValuationSubring K))
      (selectedResidueField (localSeparableValuationSubring K)) := by
  let A := localSeparableValuationSubring K
  let k := decompositionResidueField K A
  let Omega := selectedResidueField A
  let F := localAbstractFixedResidueIntermediateField K H
  letI : Algebra k F := F.algebra
  letI : FiniteDimensional k F :=
    localAbstractFixedResidueIntermediateField_finiteDimensional K H
  letI : Finite F := Module.finite_of_finite k
  letI : Fintype F := Fintype.ofFinite F
  letI : IsGalois k F := by
    obtain ⟨p, hp⟩ := CharP.exists k
    let : CharP k p := hp
    let : CharP F p :=
      charP_of_injective_algebraMap (R := k) (A := F)
        (algebraMap k F).injective p
    exact IsGalois.of_separable_splitting_field
      (galois_poly_separable p (Fintype.card F)
        (let ⟨n, _, hn⟩ := FiniteField.card F p
        hn.symm ▸ dvd_pow_self p n.ne_zero))
  exact { toIntermediateField := F }

/-- **Finite local reciprocity, finite-field index form.**  The residue degree attached
by `localResidueDatum` to a finite abstract field is the degree of the actual
residue subfield selected by the residue action. -/
theorem localResidueDatum_residueDegree_eq_selectedResidueFinrank
    (H : FiniteAbstractField (Gal(SeparableClosure K / K))) :
    (H.residueDegree (localResidueDatum K) : ℕ) =
      Module.finrank
        (decompositionResidueField K (localSeparableValuationSubring K))
        (localAbstractFixedResidueIntermediateField K H.field) := by
  let A := localSeparableValuationSubring K
  let k := decompositionResidueField K A
  let Omega := selectedResidueField A
  let rho := (localSeparableResidueAlgAction K).toMonoidHom
  let R := localAbstractFixedResidueIntermediateField K H.field
  let : Algebra k R := R.algebra
  let : FiniteDimensional k R :=
    localAbstractFixedResidueIntermediateField_finiteDimensional K H.field
  let F := localAbstractFixedResidueFiniteGaloisIntermediateField K H.field
  let HR := H.toFiniteResidueAbstractField (localResidueDatum K)
  let : Finite ((localResidueDatum K).residueQuotient H.field) :=
    HR.finiteResidueQuotient
  have himage : H.field.toSubgroup.map rho =
      F.toIntermediateField.fixingSubgroup := by
    change H.field.toSubgroup.map
        (localSeparableResidueAlgAction K).toMonoidHom =
      (localAbstractFixedResidueIntermediateField K H.field).fixingSubgroup
    exact localAbstractFixedResidueAction_map_eq_fixingSubgroup K H.field
  have hindex :
      ((localResidueDatum K).fieldImage HR.field).index =
        Module.finrank k R := by
    rw [(localResidueDatum K).fieldImage_eq_map]
    change
      (H.field.toSubgroup.map
        ((residueAbsoluteDegreeIn k Omega).toMonoidHom.comp rho)).index =
          Module.finrank k R
    exact residueDegreeImage_index_eq_finrank_of_map_eq_fixingSubgroup
      k Omega rho H.field.toSubgroup F himage
  let : ((localResidueDatum K).fieldImage HR.field).IsFiniteRelIndex
      (⊤ : Subgroup ZHatMul) :=
    ⟨by
      rw [Subgroup.relIndex_top_right, hindex]
      let : Module.IsTorsionFree k R :=
        (Module.isTorsionFree_iff_algebraMap_injective (R := k) (A := R)).mpr
          (algebraMap k R).injective
      exact (Module.finrank_pos (R := k) (M := R)).ne'⟩
  apply Nat.cast_injective (R := Cardinal)
  change ((H.residueDegree (localResidueDatum K) : ℕ) : Cardinal) =
    (Module.finrank k R : Cardinal)
  rw [show H.residueDegree (localResidueDatum K) = HR.residueDegree from rfl,
    ← HR.residueDegreeCardinal_eq_coe,
    DegreeData.residueDegreeCardinal,
    relativeIndexCardinal_eq_index_of_finite
      (show (localResidueDatum K).fieldImage HR.field ≤
        (⊤ : Subgroup ZHatMul) from le_top)]
  norm_cast
  simpa only [Subgroup.relIndex_top_right] using hindex

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FiniteResidueFinrankTransfer
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_isGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_finite_residue _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeDegreeIntermediate_top_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.primeOrderFixedField_isGalois _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.scaledRelativeIntegerLatticeQuotientFinite
attribute [-simp] _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_apply _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_zero _root_.ClassFormation.ValuationData.canonicalUnramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.mem_infiniteUnitAddSubgroup_iff _root_.ClassFormation.ValuationData.mem_infiniteUnitNormSubgroup_iff _root_.ClassFormation.ValuationData.unramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.unramifiedReciprocity_equiv_of_generator_apply _root_.ClassFormation.ValuationData.valuationAt_chosenPrimeElement _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.intrinsicFiniteAbstractBase_eq_base _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.infinitePlace_mult_smul
set_option synthInstance.maxHeartbeats 400000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory
open CyclicCohomology RamificationTheory ClassFormation

open LocalFieldTheory ValuationTheory

/-!
# Finite local reciprocity: comparison of the two finite residue-field models

The residue-action exact sequence presents the residue field of a
finite fixed field intrinsically, inside the selected residue algebraic
closure.  The norm formula uses the literal residue field of the spectral
valuation on that fixed field.  This file compares those presentations by
the uniqueness of the finite extension valuation.
-/

noncomputable section

open scoped ValuativeRel
open _root_.RamificationTheory.HilbertRamification.ValuationSubring

universe u v

/-- The corresponding equivalence between literal and intrinsic residue
fields. -/
noncomputable def residueFieldEquivDecompositionResidueOfEqTop
    {F : Type u} {Omega : Type v} [Field F] [Field Omega] [Algebra F Omega]
    [IsGalois F Omega]
    (A : ValuationSubring Omega) (C : ValuationSubring F)
    (hC : A.comap (algebraMap F Omega) = C)
    (hA : decompositionGroup F A = ⊤) :
    IsLocalRing.ResidueField C ≃+* decompositionResidueField F A :=
  (IsLocalRing.ResidueField.mapEquiv
      (valuationSubringEquivDecompositionFieldOfEqTop A C hC hA)).trans
    (decompositionFieldResidueEquiv (K := F) A)

/-- Naturality of the preceding residue equivalence with reduction into the
selected residue field. -/
theorem residueFieldEquivDecompositionResidueOfEqTop_algebraMap
    {F : Type u} {Omega : Type v} [Field F] [Field Omega] [Algebra F Omega]
    [IsGalois F Omega]
    (A : ValuationSubring Omega) (C : ValuationSubring F)
    (hC : A.comap (algebraMap F Omega) = C)
    (hA : decompositionGroup F A = ⊤) (x : C) :
    algebraMap (decompositionResidueField F A) (selectedResidueField A)
        (residueFieldEquivDecompositionResidueOfEqTop A C hC hA
          (IsLocalRing.residue C x)) =
      IsLocalRing.residue A
        (⟨algebraMap F Omega (x : F), by
          have hx : (x : F) ∈ A.comap (algebraMap F Omega) := by
            rw [hC]
            exact x.property
          exact hx⟩ : A) := by
  rfl

/-! ## The finite fixed-field comparison -/

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **Finite local reciprocity, residue-degree comparison.**  For an arbitrary finite
closed subgroup field (not necessarily normal over `K`), the residue degree
defined by the absolute residue action is the degree of the literal residue
field of the unique finite extension valuation. -/
theorem localResidueDatum_residueDegree_eq_residueFinrank
    (H : FiniteAbstractField (Gal(SeparableClosure K / K)))
    [FiniteDimensional K
      (abstractFixedField K (SeparableClosure K) H.field)]
    [ValuativeRel (abstractFixedField K (SeparableClosure K) H.field)]
    [TopologicalSpace (abstractFixedField K (SeparableClosure K) H.field)]
    [IsNonarchimedeanLocalField
      (abstractFixedField K (SeparableClosure K) H.field)]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation
        (abstractFixedField K (SeparableClosure K) H.field))] :
    (H.residueDegree (localResidueDatum K) : ℕ) =
      @Module.finrank 𝓀[K]
        𝓀[abstractFixedField K (SeparableClosure K) H.field] _ _
          (IsLocalRing.ResidueField.instModule
            (R := 𝒪[K])
            (S := 𝒪[abstractFixedField K (SeparableClosure K) H.field])) := by
  let E := abstractFixedField K (SeparableClosure K) H.field
  let A := localSeparableValuationSubring K
  let C := (ValuativeRel.valuation E).valuationSubring
  let V := (localCompleteDVF K).valuation.valuationSubring
  let kK := IsLocalRing.ResidueField
    V
  let kE := IsLocalRing.ResidueField C
  let k₀ := decompositionResidueField K A
  let kE' := decompositionResidueField E A
  let Omega := selectedResidueField A
  let F := localAbstractFixedResidueIntermediateField K H.field
  let : Algebra kK kE := by
    change Algebra 𝓀[K] 𝓀[E]
    exact IsLocalRing.ResidueField.instAlgebra
  let : Module kK kE := by
    change Module 𝓀[K] 𝓀[E]
    exact IsLocalRing.ResidueField.instModule
  change (H.residueDegree (localResidueDatum K) : ℕ) =
    Module.finrank kK kE

  have hExtC : (localCompleteDVF K).valuation.HasExtension C.valuation := by
    apply
      ValuationTheory.DiscreteValuationField.Valuation.hasExtension_valuation_of_valuationSubring_pullback
    intro x
    change ValuativeRel.valuation E (algebraMap K E x) ≤ 1 ↔
      (localCompleteDVF K).valuation x ≤ 1
    rw [_root_.Valuation.HasExtension.val_map_le_one_iff
      (ValuativeRel.valuation K) (ValuativeRel.valuation E)]
    rfl
  let : (localCompleteDVF K).valuation.HasExtension C.valuation := hExtC
  have hVC : V.valuation.HasExtension C.valuation := by
    apply
      ValuationTheory.DiscreteValuationField.Valuation.hasExtension_valuation_of_valuationSubring_pullback
    intro x
    simpa only [V, ValuationSubring.valuationSubring_valuation] using
      (ValuationTheory.DiscreteValuationField.Valuation.valuationSubring_pullback_of_hasExtension_valuation
        (localCompleteDVF K).valuation C x)
  have hC : A.comap (algebraMap E (SeparableClosure K)) = C := by
    simpa only [RamificationTheory.ValuationSubring.restrictIntermediateField_eq_comap] using
      (ValuationSubring.restrictIntermediateField_eq_of_finite_separable
        (localCompleteDVF K) A
        (abstractFixedField K (SeparableClosure K) H.field) C)
  have htop : decompositionGroup E A = ⊤ :=
    localAbstractFixedDecompositionGroup_eq_top K H.field

  let eK : kK ≃+* k₀ :=
    localBaseResidueEquivDecompositionResidue K
  let eE : kE ≃+* kE' :=
    residueFieldEquivDecompositionResidueOfEqTop A C hC htop
  let i : V →+* C :=
    ValuationTheory.Valuations.valuationSubringMapOfHasExtension V C hVC
  let bar : kE →+* Omega :=
    (algebraMap kE' Omega).comp eE.toRingHom

  have hbar_base (x : kK) :
      bar (algebraMap kK kE x) =
        algebraMap k₀ Omega (eK x) := by
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    have hres :
        algebraMap kK kE
            (IsLocalRing.residue V a) =
          IsLocalRing.residue C
            (i a) := by
      change algebraMap 𝓀[K] 𝓀[E]
          (IsLocalRing.residue 𝒪[K] a) =
        IsLocalRing.residue 𝒪[E] (algebraMap 𝒪[K] 𝒪[E] a)
      exact residueField_algebraMap_residue K E a
    rw [hres]
    change algebraMap kE' Omega
        (eE (IsLocalRing.residue C
          (i a))) =
      algebraMap k₀ Omega
        (eK (IsLocalRing.residue V a))
    rw [residueFieldEquivDecompositionResidueOfEqTop_algebraMap]
    have hbase :=
      localBaseResidueEquivDecompositionResidue_algebraMap K a
    change algebraMap k₀ Omega
      (eK (IsLocalRing.residue V a)) = _ at hbase
    rw [hbase]
    congr 1

  let : Algebra k₀ kE :=
    ((algebraMap kK kE).comp eK.symm.toRingHom).toAlgebra
  let barAlg : kE →ₐ[k₀] Omega :=
    { bar with
      commutes' := fun z => by
        change bar (algebraMap kK kE (eK.symm z)) =
          algebraMap k₀ Omega z
        simpa using hbar_base (eK.symm z) }

  have hF : F = barAlg.fieldRange := by
    change IntermediateField.adjoin k₀
        (Set.range (algebraMap kE' Omega)) = barAlg.fieldRange
    apply le_antisymm
    · apply IntermediateField.adjoin_le_iff.mpr
      rintro y ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := eE.surjective z
      exact ⟨x, rfl⟩
    · rintro y ⟨x, rfl⟩
      apply IntermediateField.subset_adjoin
      exact ⟨eE x, rfl⟩

  let eRange : kE ≃+* barAlg.fieldRange :=
    (AlgEquiv.ofInjectiveField barAlg).toRingEquiv
  let : Algebra k₀ barAlg.fieldRange := barAlg.fieldRange.algebra
  let : Algebra k₀ F :=
    localAbstractFixedResidueIntermediateFieldAlgebra K H.field
  let eTop : kE ≃+* F :=
    eRange.trans
      (IntermediateField.equivOfEq hF.symm).toRingEquiv
  have hcomm :
      (algebraMap k₀ F).comp eK.toRingHom =
        eTop.toRingHom.comp (algebraMap kK kE) := by
    ext x
    change algebraMap k₀ Omega (eK x) =
      bar (algebraMap kK kE x)
    exact (hbar_base x).symm
  have hfinrankRaw :
      Module.finrank kK kE = Module.finrank k₀ F :=
    Algebra.finrank_eq_of_equiv_equiv eK eTop hcomm
  exact
    (localResidueDatum_residueDegree_eq_selectedResidueFinrank K H).trans
      hfinrankRaw.symm

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Completion_IntegerRingComparison
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Integer rings in the two finite-place completion models

This file restricts the canonical equivalences between the absolute-value and
adic completion models to their valuation rings.  It also identifies the
residue field of a rational finite-place completion.
-/

open scoped NumberField Classical NNReal ValuativeRel
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

/-- The canonical equivalence of completion fields identifies their two
valuation rings. -/
theorem finitePlaceCompletionRingEquiv_mem_integers_iff
    {K : Type} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K))
    (x : ChosenFinitePlaceBaseCompletion (K := K) v) :
    finitePlaceCompletionRingEquiv v x ∈
        v.adicCompletionIntegers K ↔
      x ∈ 𝒪[ChosenFinitePlaceBaseCompletion (K := K) v] := by
  symm
  have hnorm :
      ‖finitePlaceCompletionRingEquiv v x‖ = ‖x‖ :=
    (finitePlaceCompletionRingHom_isometry v).norm_map_of_map_zero
      (map_zero (finitePlaceCompletionRingHom v)) x
  rw [finitePlaceCompletion_mem_integers_iff_norm_le_one
    (HeightOneSpectrum.adicAbv K v)
    (HeightOneSpectrum.isNonarchimedean_adicAbv K v) x]
  constructor
  · intro hx
    apply mem_adicCompletionIntegers_of_norm_le_one v
    simpa only [hnorm] using hx
  · intro hx
    have hxnorm :=
      norm_le_one_of_mem_adicCompletionIntegers v hx
    simpa only [hnorm] using hxnorm

/-- The canonical equivalence between the valuation ring of the
absolute-value completion and mathlib's adic completion integers. -/
noncomputable def finitePlaceCompletionIntegerRingEquiv
    {K : Type} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    𝒪[ChosenFinitePlaceBaseCompletion (K := K) v] ≃+*
      v.adicCompletionIntegers K :=
  RingEquiv.restrict
    (finitePlaceCompletionRingEquiv v)
    𝒪[ChosenFinitePlaceBaseCompletion (K := K) v]
    (v.adicCompletionIntegers K).toSubring
      (fun x =>
        (finitePlaceCompletionRingEquiv_mem_integers_iff v x).symm)
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_ChosenPlaceAction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The action at a chosen finite place

This file exposes the decomposition-group action and the direct local
cohomology endpoint used by the integral induced-block construction. Keeping
this localization boundary in a lower leaf prevents downstream transport
proofs from elaborating it together with the tensor-block API.
-/

open scoped NumberField ValuativeRel NNReal
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

variable
    {K : Type} {L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

section ChosenFinitePlace

/-- The global action on the chosen induced integer-unit block. -/
@[implicit_reducible]
noncomputable def chosenFinitePlaceInducedIntegerUnitsAction
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    MulDistribMulAction (L ≃ₐ[K] L)
      (ChosenFinitePlaceInducedIntegerUnits
        (K := K) (L := L) w₀) := by
  letI : MulDistribMulAction
      (ChosenFinitePlaceDecompositionGroup
        (K := K) (L := L) w₀)
      (ChosenFinitePlaceLocalizedIntegerUnits
        (K := K) (L := L) w₀) :=
    chosenFinitePlaceDecompositionGroupIntegerUnitsAction
      (K := K) (L := L) w₀
  exact inducedMulDistribMulAction
    (ChosenFinitePlaceDecompositionGroup
      (K := K) (L := L) w₀)

/-- The global action on the chosen local multiplicative block. -/
@[implicit_reducible]
noncomputable def chosenFinitePlaceLocalPlaceBlockAction
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    MulDistribMulAction (L ≃ₐ[K] L)
      (ChosenFinitePlaceLocalPlaceBlock
        (K := K) (L := L) w₀) := by
  letI : MulDistribMulAction
      (ChosenFinitePlaceDecompositionGroup
        (K := K) (L := L) w₀)
      (ChosenFinitePlaceLocalizedFieldUnits
        (K := K) (L := L) w₀) :=
    chosenFinitePlaceDecompositionGroupLocalUnitsAction
      (K := K) (L := L) w₀
  exact inducedMulDistribMulAction
    (ChosenFinitePlaceDecompositionGroup
      (K := K) (L := L) w₀)

end ChosenFinitePlace
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_ChosenPlace
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Integral induced blocks at the chosen finite place

This file specializes the integral induced-block construction to the actual
chosen localization above a finite place and proves its unramified Tate
cohomology consequences.
-/

open scoped NumberField TensorProduct ValuativeRel NNReal
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

variable
    {K : Type} {L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

section ChosenFinitePlace

omit [NumberField L] in
noncomputable def chosenFinitePlaceDecompositionGroupEquivProvider
    (w₀ : HeightOneSpectrum (𝓞 K)) :=
  decompositionGroupEquivAlgebraicLocalizationAut
    (HeightOneSpectrum.adicAbv K w₀)
    (RayClass.adicAbv_isNontrivial w₀)
    (chosenFinitePlaceExtension (L := L) w₀)

omit [NumberField L] in
@[implicit_reducible]
noncomputable def
    chosenFinitePlaceLocalizedIntegerUnitsGaloisActionProvider
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    MulDistribMulAction
      (Gal(
        ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) w₀ /
        ChosenFinitePlaceBaseCompletion (K := K) w₀))
      𝒪[ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) w₀]ˣ :=
  galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure
    (ChosenFinitePlaceBaseCompletion (K := K) w₀)
    (ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) w₀)

omit [NumberField L] in
@[implicit_reducible]
noncomputable def chosenFinitePlaceDecompositionGroupFintypeProvider
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    Fintype
      (absoluteValueDecompositionGroup K
        (chosenFinitePlaceExtension (L := L) w₀).1) :=
  Fintype.ofFinite _

end ChosenFinitePlace
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_IdelePowerLocalUnitSubgroup
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

/-- Membership in `idelePowerLocalUnitSubgroup` expressed componentwise. -/
theorem mem_idelePowerLocalUnitSubgroup_iff
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (a : IdeleGroup K) :
    a ∈ idelePowerLocalUnitSubgroup (K := K) n S T ↔
      (∀ w : InfinitePlace K,
        IdeleGroup.infiniteComponent w a ∈
          (powMonoidHom (n : ℕ) :
            w.Completionˣ →* w.Completionˣ).range) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∈ S →
        IdeleGroup.finiteComponent v a ∈
          (powMonoidHom (n : ℕ) :
            (v.adicCompletion K)ˣ →*
              (v.adicCompletion K)ˣ).range) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S ∪ T →
        IdeleGroup.finiteComponent v a ∈
          (v.adicCompletionIntegers K).units) := by
  simp only [idelePowerLocalUnitSubgroup, Subgroup.mem_inf,
    Subgroup.mem_iInf, Subgroup.mem_comap, and_assoc]

/-- Field units whose principal ideles lie in the local power-unit
subgroup. -/
def principalIdelePowerLocalUnitSubgroup
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup Kˣ :=
  (idelePowerLocalUnitSubgroup (K := K) n S T).comap
    (IdeleGroup.principalIdele K)

/-- A principal idele satisfying the local power-unit conditions comes
from an `(S ∪ T)`-unit. -/
theorem principalIdelePowerLocalUnitSubgroup_le_sUnitGroup
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    principalIdelePowerLocalUnitSubgroup (K := K) n S T ≤
      SUnitGroup (K := K) (S ∪ T) := by
  intro y hy
  rw [mem_SUnitGroup_iff]
  intro v hv
  have hAway :=
    ((mem_idelePowerLocalUnitSubgroup_iff
      (K := K) n S T
      (IdeleGroup.principalIdele K y)).mp hy).2.2 v hv
  rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
    at hAway
  rw [IdeleGroup.finiteComponent_principalIdele,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hAway
  exact hAway

end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_SupportedIdelePowerLocalUnitQuotient
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.chosenFinitePlaceCompletionAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

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

/-- The power/local-unit subgroup `h(S,T)`, regarded inside
`I_K^{S ∪ T}`. -/
def supportedIdelePowerLocalUnitSubgroup
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup
      (IdeleGroup.supportedAt
        (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K)))) :=
  (idelePowerLocalUnitSubgroup (K := K) n S T).comap
    (IdeleGroup.supportedAt
      (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K)))).subtype

/-- Membership in `h(S,T)` automatically supplies the restricted-product
condition defining `I_K^{S ∪ T}`. -/
theorem idelePowerLocalUnitSubgroup_le_supportedAt
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    idelePowerLocalUnitSubgroup (K := K) n S T ≤
      IdeleGroup.supportedAt
        (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K))) := by
  intro a ha
  rw [IdeleGroup.mem_supportedAt_iff]
  intro v hv
  apply
    ((mem_idelePowerLocalUnitSubgroup_iff
      (K := K) n S T a).mp ha).2.2 v
  simpa using hv

/-- Reduction modulo local `n`-th powers at all infinite places and at the
finite places in `S`.  The coordinates in `T` and the integral coordinates
away from `S ∪ T` disappear in the supported-idele index calculation. -/
def supportedIdelePowerClassMap
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    IdeleGroup.supportedAt
        (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K))) →*
      ((
        ∀ w : InfinitePlace K,
          w.Completionˣ ⧸
            (powMonoidHom (n : ℕ) :
              w.Completionˣ →* w.Completionˣ).range) ×
        (∀ v : ↥S,
          (v.1.adicCompletion K)ˣ ⧸
            (powMonoidHom (n : ℕ) :
              (v.1.adicCompletion K)ˣ →*
                (v.1.adicCompletion K)ˣ).range)) where
  toFun a :=
    (fun w =>
      QuotientGroup.mk'
        (powMonoidHom (n : ℕ) :
          w.Completionˣ →* w.Completionˣ).range
        (IdeleGroup.infiniteComponent w a.1),
     fun v =>
      QuotientGroup.mk'
        (powMonoidHom (n : ℕ) :
          (v.1.adicCompletion K)ˣ →*
            (v.1.adicCompletion K)ˣ).range
        (IdeleGroup.finiteComponent v.1 a.1))
  map_one' := by
    apply Prod.ext
    · funext w
      apply (QuotientGroup.eq_one_iff _).mpr
      apply
        (MonoidHom.mem_range
          (G := w.Completionˣ)).mpr
      refine ⟨1, ?_⟩
      rw [powMonoidHom_apply, one_pow]
      exact (IdeleGroup.infiniteComponent w).map_one.symm
    · funext v
      simp
  map_mul' a b := by
    apply Prod.ext
    · funext w
      change
        QuotientGroup.mk'
            (powMonoidHom (n : ℕ) :
              w.Completionˣ →* w.Completionˣ).range
            (IdeleGroup.infiniteComponent w (a.1 * b.1)) =
          QuotientGroup.mk'
              (powMonoidHom (n : ℕ) :
                w.Completionˣ →* w.Completionˣ).range
              (IdeleGroup.infiniteComponent w a.1) *
            QuotientGroup.mk'
              (powMonoidHom (n : ℕ) :
                w.Completionˣ →* w.Completionˣ).range
              (IdeleGroup.infiniteComponent w b.1)
      rw [map_mul, map_mul]
    · funext v
      simp

/-- The kernel of the local-power class map is precisely `h(S,T)` inside
`I_K^{S ∪ T}`. -/
theorem supportedIdelePowerClassMap_ker
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    (supportedIdelePowerClassMap (K := K) n S T).ker =
      supportedIdelePowerLocalUnitSubgroup (K := K) n S T := by
  ext a
  rw [MonoidHom.mem_ker]
  constructor
  · intro ha
    rw [supportedIdelePowerLocalUnitSubgroup,
      Subgroup.mem_comap,
      mem_idelePowerLocalUnitSubgroup_iff]
    refine ⟨?_, ?_, ?_⟩
    · intro w
      have hw := congrArg (fun q => q.1 w) ha
      rw [Prod.fst_one, Pi.one_apply] at hw
      exact (QuotientGroup.eq_one_iff _).mp hw
    · intro v hv
      let vS : ↥S := ⟨v, hv⟩
      have hvq := congrArg (fun q => q.2 vS) ha
      rw [Prod.snd_one, Pi.one_apply] at hvq
      exact (QuotientGroup.eq_one_iff _).mp hvq
    · intro v hv
      have hv' :
          v ∉ (S ∪ T : Set (HeightOneSpectrum (𝓞 K))) := by
        simpa using hv
      exact
        (IdeleGroup.mem_supportedAt_iff
          (K := K)
          (S ∪ T : Set (HeightOneSpectrum (𝓞 K))) a.1).mp
            a.2 v hv'
  · intro ha
    rw [supportedIdelePowerLocalUnitSubgroup,
      Subgroup.mem_comap,
      mem_idelePowerLocalUnitSubgroup_iff] at ha
    apply Prod.ext
    · funext w
      exact (QuotientGroup.eq_one_iff _).mpr (ha.1 w)
    · funext v
      exact (QuotientGroup.eq_one_iff _).mpr
        (ha.2.1 v.1 v.2)

/-- The local-power class map is onto: choose representatives independently
at the finitely many constrained finite places and at all archimedean
places, then extend the finite family by `1`. -/
theorem supportedIdelePowerClassMap_surjective
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Surjective
      (supportedIdelePowerClassMap (K := K) n S T) := by
  intro q
  choose aInf hInf using fun w : InfinitePlace K =>
    QuotientGroup.mk_surjective (q.1 w)
  choose aS hS using fun v : ↥S =>
    QuotientGroup.mk_surjective (q.2 v)
  let alpha : IdeleGroup K :=
    (ContinuousMulEquiv.piUnits.symm aInf,
      IdeleGroup.finiteIdeleOfFinset S aS)
  have hAlpha :
      alpha ∈
        IdeleGroup.supportedAt
          (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K))) := by
    rw [IdeleGroup.mem_supportedAt_iff]
    intro v hv
    have hvS : v ∉ S := by
      intro hvS
      apply hv
      exact Or.inl hvS
    change
      IdeleGroup.finiteIdeleOfFinset S aS v ∈
        (v.adicCompletionIntegers K).units
    rw [IdeleGroup.finiteIdeleOfFinset_apply_notMem S aS v hvS]
    exact Subgroup.one_mem _
  refine ⟨⟨alpha, hAlpha⟩, ?_⟩
  apply Prod.ext
  · funext w
    calc
      QuotientGroup.mk'
          (powMonoidHom (n : ℕ) :
            w.Completionˣ →* w.Completionˣ).range
          (IdeleGroup.infiniteComponent w alpha) =
          QuotientGroup.mk'
            (powMonoidHom (n : ℕ) :
              w.Completionˣ →* w.Completionˣ).range
            (aInf w) := by
        apply congrArg
        change
          ContinuousMulEquiv.piUnits
              (ContinuousMulEquiv.piUnits.symm aInf) w =
            aInf w
        exact congrFun
          (ContinuousMulEquiv.piUnits.apply_symm_apply aInf) w
      _ = q.1 w := hInf w
  · funext v
    calc
      QuotientGroup.mk'
          (powMonoidHom (n : ℕ) :
            (v.1.adicCompletion K)ˣ →*
              (v.1.adicCompletion K)ˣ).range
          (IdeleGroup.finiteComponent v.1 alpha) =
          QuotientGroup.mk'
            (powMonoidHom (n : ℕ) :
              (v.1.adicCompletion K)ˣ →*
                (v.1.adicCompletion K)ˣ).range
            (aS v) := by
        apply congrArg
        exact IdeleGroup.finiteIdeleOfFinset_apply_mem S aS v
      _ = q.2 v := hS v

/-- The algebraic supported-idele index decomposition:

`I_K^{S ∪ T} / h(S,T)` is the product of the local `n`-power class
groups at all infinite places and at the finite places in `S`. -/
noncomputable def supportedIdeleQuotientEquivLocalPowerClasses
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    IdeleGroup.supportedAt
          (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K))) ⧸
        supportedIdelePowerLocalUnitSubgroup (K := K) n S T ≃*
      ((
        ∀ w : InfinitePlace K,
          w.Completionˣ ⧸
            (powMonoidHom (n : ℕ) :
              w.Completionˣ →* w.Completionˣ).range) ×
        (∀ v : ↥S,
          (v.1.adicCompletion K)ˣ ⧸
            (powMonoidHom (n : ℕ) :
              (v.1.adicCompletion K)ˣ →*
                (v.1.adicCompletion K)ˣ).range)) :=
  quotientEquivOfSurjectiveWithKernel
    (H :=
      ((
        ∀ w : InfinitePlace K,
          w.Completionˣ ⧸
            (powMonoidHom (n : ℕ) :
              w.Completionˣ →* w.Completionˣ).range) ×
        (∀ v : ↥S,
          (v.1.adicCompletion K)ˣ ⧸
            (powMonoidHom (n : ℕ) :
              (v.1.adicCompletion K)ˣ →*
                (v.1.adicCompletion K)ˣ).range)))
    (supportedIdelePowerClassMap (K := K) n S T)
    (supportedIdelePowerLocalUnitSubgroup (K := K) n S T)
    (supportedIdelePowerClassMap_surjective (K := K) n S T)
    (supportedIdelePowerClassMap_ker (K := K) n S T)

/-- Cardinal form of the supported-idele index decomposition.  The subsequent
local power-index and product-formula calculation evaluates the right-hand
side. -/
theorem card_supportedIdeleQuotient_eq_localPowerClasses
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Nat.card
        (IdeleGroup.supportedAt
              (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K))) ⧸
          supportedIdelePowerLocalUnitSubgroup (K := K) n S T) =
      Nat.card
        ((
          ∀ w : InfinitePlace K,
            w.Completionˣ ⧸
              (powMonoidHom (n : ℕ) :
                w.Completionˣ →* w.Completionˣ).range) ×
          (∀ v : ↥S,
            (v.1.adicCompletion K)ˣ ⧸
              (powMonoidHom (n : ℕ) :
                (v.1.adicCompletion K)ˣ →*
                  (v.1.adicCompletion K)ˣ).range)) :=
  Nat.card_congr
    (supportedIdeleQuotientEquivLocalPowerClasses
      (K := K) n S T).toEquiv


end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_NormRestriction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

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

theorem finitePlaceArtinNormUnits_map_ringEquiv
    {F M F' M' : Type}
    [Field F] [Field M] [Field F'] [Field M']
    [Algebra F M] [Algebra F' M']
    (eF : F ≃+* F') (eM : M ≃+* M')
    (he :
      RingHom.comp (algebraMap F' M') eF =
        RingHom.comp eM (algebraMap F M))
    (x : Mˣ) :
    Units.mapEquiv eF.toMulEquiv
        (LocalFieldTheory.normUnits F M x) =
      LocalFieldTheory.normUnits F' M'
        (Units.mapEquiv eM.toMulEquiv x) := by
  apply Units.ext
  change
    eF (Algebra.norm F (x : M)) =
      Algebra.norm F' (eM (x : M))
  rw [Algebra.norm_eq_of_equiv_equiv eF eM he]
  exact eF.apply_symm_apply _

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.KummerTheory_Concrete_SUnitPreparation_FiniteRadicalSupport
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.chosenFinitePlaceCompletionAlgebra
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

/-- A chosen finite set of places outside which a given global unit is
an integral unit. -/
noncomputable def chosenUnitFiniteSupport (x : Kˣ) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  Classical.choose
    (IdeleGroup.exists_finset_supportedAt
      (IdeleGroup.principalIdele K x))

/-- The union of the supports of one representative of every actual
Kummer radical class. -/
noncomputable def finiteKummerRadicalSupport
    {L : Type*} [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    Finset (HeightOneSpectrum (𝓞 K)) := by
  let D :=
    KummerTheory.chosenFiniteKummerRadicalDatum
      (K := K) (L := L) n
  letI : Finite D.RadicalQuotient :=
    finite_chosenFiniteKummerRadicalQuotient
      (K := K) (L := L) n hmu
  letI : Fintype D.RadicalQuotient :=
    Fintype.ofFinite D.RadicalQuotient
  exact
    Finset.univ.biUnion fun q =>
      chosenUnitFiniteSupport (K := K)
        (chosenFiniteKummerRadicalRepresentative
          (K := K) (L := L) n q).1

/-- Enlarge any prescribed finite set by the finite supports needed to
represent all actual Kummer radical classes by `S`-units. -/
noncomputable def enlargeByFiniteKummerRadicalSupport
    {L : Type*} [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  S ∪ finiteKummerRadicalSupport
    (K := K) (L := L) n hmu

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_MixedCharacteristicQp
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.gLocallyCompact _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseIsUltrametricDist _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.coe_valuationSubringUnitFieldUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_coord _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotLift_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_map_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerFieldHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltration_subgroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModPrincipalUnitEquivOfPreserves_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitEquivOfPreserves_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.zero_eq_top _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Mixed-characteristic input for the `Qp` branch of the local-field structure classification

This file keeps the converse direction of the local-field structure theory, the local-field structure classification focused on the mixed-characteristic case.  The key point proved here is
that the actual range-restricted local-field valuation still restricts on
`ℚ` to the usual `p`-adic valuation, where `p` is the residue characteristic.
-/

noncomputable section

universe u v

open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace LocalField

open scoped WithZero

variable {K : Type u} [Field K]

/-- A mixed-characteristic local field is finite-dimensional over the closed
subfield generated by its rational prime field. -/
theorem finiteDimensional_over_qpadicClosureSubfield
    (F : LocalField.{u, v} K) [CharZero K] :
    letI : Valued K F.mrangeValueGroup :=
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
    letI : NontriviallyNormedField K :=
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F.toCompleteDVF
    letI : NontriviallyNormedField F.qpadicClosureSubfield :=
      F.qpadicClosureSubfield_nontriviallyNormedField
    letI : NormedAlgebra F.qpadicClosureSubfield K :=
      F.qpadicClosureSubfield_normedAlgebra
    FiniteDimensional F.qpadicClosureSubfield K := by
  let : Valued K F.mrangeValueGroup :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
  let : NontriviallyNormedField K :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F.toCompleteDVF
  let : NontriviallyNormedField F.qpadicClosureSubfield :=
    F.qpadicClosureSubfield_nontriviallyNormedField
  let : NormedAlgebra F.qpadicClosureSubfield K :=
    F.qpadicClosureSubfield_normedAlgebra
  have : ProperSpace K :=
    F.mrangeRestrict_properSpace
  have : CompleteSpace F.qpadicClosureSubfield :=
    (F.qpadicClosureSubfield_isClosed : IsClosed
      (F.qpadicClosureSubfield : Set K)).completeSpace_coe
  exact
    FiniteDimensional.of_locallyCompactSpace F.qpadicClosureSubfield

/-- Mixed-characteristic local fields are finite-dimensional over the actual
`p`-adic number field.  This transports the finite-dimensionality already
proved over the closed `Qp` candidate along the canonical field isomorphism. -/
theorem finiteDimensional_over_qpadicNumbers
    (F : LocalField.{u, v} K) [CharZero K] :
    letI : Algebra ℚ_[F.residueCharacteristic] K :=
      F.qpadicNumbersAlgebra
    FiniteDimensional ℚ_[F.residueCharacteristic] K := by
  let : Algebra ℚ_[F.residueCharacteristic] K :=
    F.qpadicNumbersAlgebra
  let : Valued K F.mrangeValueGroup :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
  let : NontriviallyNormedField K :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F.toCompleteDVF
  let : NontriviallyNormedField F.qpadicClosureSubfield :=
    F.qpadicClosureSubfield_nontriviallyNormedField
  let : NormedAlgebra F.qpadicClosureSubfield K :=
    F.qpadicClosureSubfield_normedAlgebra
  have : FiniteDimensional F.qpadicClosureSubfield K :=
    F.finiteDimensional_over_qpadicClosureSubfield
  have hcompat :
      (algebraMap F.qpadicClosureSubfield K).comp
          (F.qpadicNumbersEquivQpadicClosureSubfield :
            ℚ_[F.residueCharacteristic] →+* F.qpadicClosureSubfield) =
        (RingEquiv.refl K).toRingHom.comp
          (algebraMap ℚ_[F.residueCharacteristic] K) := by
    ext x
    rfl
  have hrank :
      Module.rank ℚ_[F.residueCharacteristic] K =
        Module.rank F.qpadicClosureSubfield K := by
    simpa using
      (Algebra.rank_eq_of_equiv_equiv
        F.qpadicNumbersEquivQpadicClosureSubfield
        (RingEquiv.refl K) hcompat)
  exact
    FiniteDimensional.of_rank_eq_nat
      (n := Module.finrank F.qpadicClosureSubfield K) <| by
        simpa [Module.finrank_eq_rank'] using hrank

end LocalField
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PrincipalUnitPadicAction_ProdiscretePadicModule
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The p-adic module on the prodiscrete principal-unit limit

Coordinatewise scalar multiplication makes the prodiscrete inverse limit a topological
module over the p-adic integers.
-/

noncomputable section

open scoped BigOperators

universe u v

namespace LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField
namespace CompleteDVF
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
namespace higherPrincipalUnitGroup

open LubinTate
open LubinTate.Valuations

variable {K : Type u} [Field K]

open Internal

/-! ## The inverse-limit module and transport to `U^1` -/

/-- Evaluation at a wrapped coordinate as a `Z_p`-linear map. -/
noncomputable def PrincipalUnitProdiscreteLimit.coordinateLinear
    (F : LocalField.{u, v} K) (n : ℕ) :
    PrincipalUnitProdiscreteLimit F.toCompleteDVF →ₗ[
      ℤ_[F.residueCharacteristic]]
      DiscretePrincipalUnitQuotient F.toCompleteDVF n where
  toFun := PrincipalUnitProdiscreteLimit.coordinate F.toCompleteDVF n
  map_add' := fun x y =>
    (PrincipalUnitProdiscreteLimit.coordinate F.toCompleteDVF n).map_add x y
  map_smul' := PrincipalUnitProdiscreteLimit.coordinate_smul F n

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PrincipalUnitPadicAction_AdicPadicModule
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The p-adic module on adic principal units

The coordinatewise p-adic action is transported across the canonical adic/prodiscrete
comparison, producing its linear and topological forms on first principal units.
-/

noncomputable section

open scoped BigOperators

universe u v

namespace LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField
namespace CompleteDVF
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
namespace higherPrincipalUnitGroup

open LubinTate
open LubinTate.Valuations

variable {K : Type u} [Field K]

open Internal

/-- Projection from adic first principal units to one wrapped quotient
coordinate. -/
noncomputable def adicPrincipalUnitsCoordinateLinear
    (F : LocalField.{u, v} K) (n : ℕ) :
    AdicPrincipalUnits F.toCompleteDVF →ₗ[ℤ_[F.residueCharacteristic]]
      DiscretePrincipalUnitQuotient F.toCompleteDVF n :=
  (PrincipalUnitProdiscreteLimit.coordinateLinear F n).comp
    (adicPrincipalUnitsLinearEquivProdiscreteLimit F).toLinearMap

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_MixedCharacteristicStructure_IntegralLattice
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
Equips the target with its canonical `FiniteDimensional` structure, namely `FiniteDimensional
ℚ_[F.residueCharacteristic] K`.
-/
noncomputable instance mixedQPadicContextFiniteDimensional
    (F : LocalField.{u, v} K) [CharZero K] [MixedQPadicContext F] :
    FiniteDimensional ℚ_[F.residueCharacteristic] K :=
  F.finiteDimensional_over_qpadicNumbers

/-! ### the canonical `Z_p` integral basis -/

/-! ### The canonical `Z_p` action on `U^r` -/

end LocalField
end LocalFieldTheory.DiscreteValuationField
end
end


