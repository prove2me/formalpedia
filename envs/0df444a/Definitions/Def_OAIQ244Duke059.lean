-- Prove2me | Definitions.Def_OAIQ244Duke059
-- name    : OAIQ244Duke059
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T22:19:21.469697+00:00
-- url     : https://prove2.me/theorems/13364ca4-ee82-4008-b90f-da59e2e7daa0
-- title:
--   Definitions bundle OAIQ244Duke059 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 31 declarations of OpenAI's Lean: 9 definitions and 22 theorems. The definitions and types are `GlobalClassFieldTheory.Reciprocity.finitePlaceArtinLocalizedAutomorphism`, `GlobalClassFieldTheory.Reciprocity.finitePlaceArtinLocalizedCompletion`, `GlobalClassFieldTheory.Reciprocity.finitePlaceConjugateLocalizedCompletionAlgEquiv`, `GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinLocalizedAlgebra`, `GlobalClassFieldTheory.Reciprocity.finitePlaceLocalToGlobalMonoidHom`, `GlobalClassFieldTheory.Reciprocity.finitePlaceNormLocalizedCompletion`, `GlobalClassFieldTheory.Reciprocity.finitePlaceNormUpperCompletionAlgebra`, `LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicLocalField`, `LubinTate.padicValuationSubringToCompletedUnramifiedWittRing`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Completion_AdicCompletionComparison`, `AlgebraicNumberTheory_Completion_UnramifiedComparison_LocalNorm`, `AlgebraicNumberTheory_Idele_Relative_InfinitePlaceTensorNorm`, `AlgebraicNumberTheory_Ramification_Splitting_NormalClosure`, `GlobalClassFieldTheory_ClassFieldAxiom_IdelePowerLocalUnitSubgroup`, `GlobalClassFieldTheory_GlobalClassFields_ConductorLattice`, `GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_Conjugation`, `GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_Construction`, `GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_CrossLocalRestriction`, `GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_NormRestriction`, `GlobalClassFieldTheory_Reciprocity_InfinitePlaceArtin`, `KummerTheory_Concrete_FinitePlaceDecomposition`, `KummerTheory_Concrete_SUnitPreparation_SUnitLocalPowerKernel`, `LocalField_DiscreteValuationField_PadicField`, `LubinTate_Padic_ChangedUniformizerCoefficient`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke046`, `OAIQ244Duke047`, `OAIQ244Duke048`, `OAIQ244Duke049`, `OAIQ244Duke050` and `OAIQ244Duke051` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke062`, `OAIQ244Duke064`, `OAIQ244Duke065`, `OAIQ244Duke066`, `OAIQ244Duke067` and `OAIQ244Duke068`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
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
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.NumberTheory.Ostrowski
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
import Definitions.Def_OAIQ244Duke046
import Definitions.Def_OAIQ244Duke047
import Definitions.Def_OAIQ244Duke048
import Definitions.Def_OAIQ244Duke049
import Definitions.Def_OAIQ244Duke050
import Definitions.Def_OAIQ244Duke051

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Completion_AdicCompletionComparison
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Comparing the exact-extension and concrete adic-completion maps

The completion map attached to an exact extension of a finite-place
absolute value agrees with the canonical map between the concrete adic
completions at the corresponding finite places.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations

universe u v

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

/-- The canonical map between concrete adic completions preserves the
valuation ring, expressed by the norm bound defining its unit ball. -/
theorem finitePlaceAdicCompletionMap_norm_le_one_iff
    (w : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) //
      finitePlaceBelow (K := K) W = w})
    (x : w.adicCompletion K) :
    ‖finitePlaceAdicCompletionMap K L w W x‖ ≤ 1 ↔
      ‖x‖ ≤ 1 := by
  obtain ⟨a, rfl⟩ :=
    (finitePlaceExtensionEquivAbove
      (K := K) (L := L) w).surjective W
  have hnorm :
      ‖finitePlaceExtensionAdicCompletionMap K L w a x‖ =
        ‖finitePlaceAdicCompletionMap K L w
          (finitePlaceExtensionEquivAbove
            (K := K) (L := L) w a) x‖ :=
    congrArg (fun y => ‖y‖)
      (finitePlaceExtensionAdicCompletionMap_eq_finitePlaceAdicCompletionMap
        K L w a x)
  rw [← hnorm,
    finitePlaceExtensionAdicCompletionMap_norm]
  simpa only [Real.one_rpow] using
    Real.rpow_le_rpow_iff (norm_nonneg x) zero_le_one
      (finitePlaceExtensionExponent_pos
        (K := K) (L := L) w a)
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Completion_UnramifiedComparison_LocalNorm
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteNormalClosure_isGalois
attribute [-simp] _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_primitiveRoot _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure_arithmeticFrobenius _root_.LocalFieldTheory.galoisGroupEquivZModOfUnramifiedValuationNormalized_arithmeticFrobenius _root_.LocalFieldTheory.galoisGroupEquivZModOfUnramifiedValuationNormalized_arithmeticFrobenius_zpow _root_.LocalFieldTheory.galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.finitePlaceExtensionAdicCompletionRingEquiv_toCompletion _root_.finitePlaceExtensionCompletionRingEquiv_toCompletion _root_.finitePlaceIdealResidueEquivCompletion_apply_mk _root_.finitePlaceIntegerToCompletion_coe _root_.finitePlaceTensorRingEquivAboveAdic_apply_extension _root_.finitePlaceTensorUnitsEquivAboveAdic_apply_extension _root_.infinitePlaceAboveEquivExtension_apply_val _root_.infinitePlaceTensorRingEquivAbove_apply _root_.infinitePlaceTensorUnitsEquivAbove_apply _root_.infinitePlace_mult_smul _root_.mem_finitePlaceDecompositionGroup_iff _root_.restrictAbsoluteValueExtensionToIntermediate_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Local norms at an unramified chosen finite place

This file proves that the concrete adic integer units lie in the actual local
norm subgroup of the chosen localized completion.
-/

open scoped NumberField Classical NNReal ValuativeRel
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open LocalClassFieldTheory
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- At a chosen finite place which is unramified in `L`, every concrete
adic integer unit is an actual norm from the chosen localization. -/
theorem adicCompletionIntegerUnits_le_chosenFinitePlaceLocalNormSubgroup
    (v₀ : HeightOneSpectrum (𝓞 K))
    (hunram :
      ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v₀) :
    (v₀.adicCompletionIntegers K).units ≤
      chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v₀ := by
  let vK := HeightOneSpectrum.adicAbv K v₀
  let E :=
    ChosenFinitePlaceLocalizedCompletion
      (K := K) (L := L) v₀
  let :
      IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
        vK.Completion E := by
    simpa [ChosenFinitePlaceIsUnramified] using hunram
  intro x hx
  let e :=
    finitePlaceCompletionUnitsContinuousMulEquiv v₀
  let x₀ : vK.Completionˣ := e.symm x
  have hx₀map : e x₀ = x :=
    e.apply_symm_apply x
  rw [Submonoid.mem_units_iff] at hx
  have hx₀norm :
      ‖(x₀ : vK.Completion)‖ ≤ 1 := by
    have hval :=
      congrArg
        (fun q : (v₀.adicCompletion K)ˣ =>
          (q : v₀.adicCompletion K)) hx₀map
    have hnorm :
        ‖finitePlaceCompletionRingHom v₀
            (x₀ : vK.Completion)‖ =
          ‖(x₀ : vK.Completion)‖ :=
      (finitePlaceCompletionRingHom_isometry v₀).norm_map_of_map_zero
        (map_zero (finitePlaceCompletionRingHom v₀)) _
    rw [← hnorm]
    rw [show finitePlaceCompletionRingHom v₀
          (x₀ : vK.Completion) = (x : v₀.adicCompletion K) by
      exact hval]
    exact norm_le_one_of_mem_adicCompletionIntegers v₀ hx.1
  have hx₀invnorm :
      ‖((x₀⁻¹ : vK.Completionˣ) : vK.Completion)‖ ≤ 1 := by
    have hval :=
      congrArg
        (fun q : (v₀.adicCompletion K)ˣ =>
          (q : v₀.adicCompletion K))
        (congrArg Inv.inv hx₀map)
    have hnorm :
        ‖finitePlaceCompletionRingHom v₀
            ((x₀⁻¹ : vK.Completionˣ) : vK.Completion)‖ =
          ‖((x₀⁻¹ : vK.Completionˣ) : vK.Completion)‖ :=
      (finitePlaceCompletionRingHom_isometry v₀).norm_map_of_map_zero
        (map_zero (finitePlaceCompletionRingHom v₀)) _
    rw [← hnorm]
    rw [show finitePlaceCompletionRingHom v₀
          ((x₀⁻¹ : vK.Completionˣ) : vK.Completion) =
        ((x⁻¹ : (v₀.adicCompletion K)ˣ) :
          v₀.adicCompletion K) by
      exact hval]
    exact norm_le_one_of_mem_adicCompletionIntegers v₀ hx.2
  have hBaseMem (a : vK.Completion) :
      a ∈ 𝒪[vK.Completion] ↔ ‖a‖ ≤ 1 := by
    simpa [vK] using
      (finitePlaceCompletion_mem_integers_iff_norm_le_one
        vK (HeightOneSpectrum.isNonarchimedean_adicAbv K v₀) a)
  let x₀O : 𝒪[vK.Completion]ˣ :=
    { val := ⟨x₀, (hBaseMem (x₀ : vK.Completion)).2 hx₀norm⟩
      inv :=
        ⟨x₀⁻¹,
          by
            simpa using
              (hBaseMem
                ((x₀⁻¹ : vK.Completionˣ) :
                  vK.Completion)).2 hx₀invnorm⟩
      val_inv := by
        apply Subtype.ext
        simp
      inv_val := by
        apply Subtype.ext
        simp }
  have hx₀O :
      integerUnitsToFieldUnits vK.Completion x₀O = x₀ := by
    apply Units.ext
    rfl
  obtain ⟨yO, hyO⟩ :=
    LocalClassFieldTheory.normIntegerUnits_surjective_unramified_of_isIntegralClosure
      vK.Completion E x₀O
  have hx₀Norm :
      x₀ ∈ localNormSubgroup vK.Completion E := by
    rw [← hx₀O, ← hyO,
      LocalClassFieldTheory.normIntegerUnits_to_fieldUnits]
    exact ⟨integerUnitsToFieldUnits E yO, rfl⟩
  change
    x ∈
      (localNormSubgroup vK.Completion E).map e.toMonoidHom
  exact ⟨x₀, hx₀Norm, hx₀map⟩
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Relative_InfinitePlaceTensorNorm
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued
attribute [-simp] _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_primitiveRoot _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.finitePlaceBelow_finitePlaceExtensionCentre _root_.finitePlaceExtensionAdicCompletionRingEquiv_toCompletion _root_.finitePlaceExtensionCentreInFibre_coe _root_.finitePlaceExtensionCentre_asIdeal _root_.finitePlaceExtensionCompletionRingEquiv_toCompletion _root_.finitePlaceExtensionEquivAbove_coe _root_.finitePlaceLocalTensorDecompositionComponentRingHom_apply _root_.finitePlaceLocalTensorDecompositionComponent_add _root_.finitePlaceLocalTensorDecompositionComponent_tmul _root_.finitePlaceLocalTensorDecompositionComponent_zero _root_.finitePlaceLocalTensorDecompositionUnitsComponent_coe _root_.finitePlaceLocalTensorDecompositionUnitsEquiv_apply _root_.finitePlaceTensorRingEquivAboveAdic_apply_extension _root_.finitePlaceTensorUnitsEquivAboveAdic_apply_extension _root_.infinitePlaceAboveEquivExtension_apply_val _root_.infinitePlaceLocalTensorUnitsEquiv_infiniteLocalIdeleInclusion_coe _root_.infinitePlaceTensorRingEquivAbove_apply _root_.infinitePlaceTensorUnitsEquivAbove_apply _root_.infinitePlace_mult_smul _root_.restrictAbsoluteValueExtensionToIntermediate_apply _root_.ringOfIntegersToFinitePlaceExtensionValuationSubring_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The norm image of an archimedean tensor factor

For a finite Galois extension `L / K`, the determinant-norm image on
`K_v ⊗[K] L` is the field-norm subgroup of any completion of `L` above
the infinite place `v`.  This is the archimedean counterpart of the
finite-place tensor-norm comparison.
-/

open scoped NumberField TensorProduct NumberField.LiesOver
open NumberField

noncomputable section

open LocalClassFieldTheory

open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L]

/-- The determinant-norm image on the actual archimedean tensor factor
is the field-norm subgroup of any completion above the base place. -/
theorem infiniteTensorNormSubgroup_eq_localNormSubgroup
    (v : InfinitePlace K) (w : InfinitePlace L)
    (hw : w.comap (algebraMap K L) = v) :
    let : w.1.LiesOver v.1 :=
      ⟨congrArg (fun q : InfinitePlace K => q.1) hw⟩
    infiniteTensorNormSubgroup (K := K) (L := L) v =
      localNormSubgroup v.Completion w.Completion := by
  let : w.1.LiesOver v.1 :=
    ⟨congrArg (fun q : InfinitePlace K => q.1) hw⟩
  let u :=
    infinitePlaceAbsoluteValueExtension v w hw
  let hL :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) u.1
  let : SMul K u.1.Completion :=
    hL.toSMul
  let : Algebra v.1.Completion u.1.Completion :=
    AbsoluteValue.completionAlgebra v.1 u.1 u.2
  let : Algebra v.1.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra v.1 w.1
      (infinitePlaceAbsoluteValueExtension v w hw).2
  let E :=
    AlgebraicNumberTheory.Valuations.LocalizedCompletion v.1 u
  let : Module.Finite v.1.Completion E :=
    AlgebraicNumberTheory.Valuations.localizedCompletionModuleFinite
      v.1 v.isNontrivial u
  let eVField :
      v.Completion ≃+* v.1.Completion :=
    (infinitePlaceCompletionAlgEquiv
      (K := K) v).toRingEquiv
  let eWField :
      w.Completion ≃+* w.1.Completion :=
    (infinitePlaceCompletionAlgEquiv
      (K := L) w).toRingEquiv
  let eVUnits :
      v.Completionˣ ≃* v.1.Completionˣ :=
    Units.mapEquiv eVField.toMulEquiv
  let eTensorUnits :
      (v.Completion ⊗[K] L)ˣ ≃*
        (LocalTensorAlgebra (L := L) v.1)ˣ :=
    infinitePlaceLocalTensorUnitsEquiv
      (K := K) (L := L) v
  have hTensorNorm
      (z : (v.Completion ⊗[K] L)ˣ) :
      eVUnits
          (infiniteTensorDetNorm
            (K := K) (L := L) v z) =
        localTensorDetNorm
          (K := K) (L := L) v.1
          (eTensorUnits z) := by
    apply Units.ext
    change
      eVField
          (Algebra.norm v.Completion
            (z : v.Completion ⊗[K] L)) =
        Algebra.norm v.1.Completion
          (infinitePlaceLocalTensorAlgEquiv
            (K := K) (L := L) v
            (z : v.Completion ⊗[K] L))
    exact
      _root_.map_norm_tensorProduct_baseChange
        (K := K) (L := L)
        (infinitePlaceCompletionAlgEquiv
          (K := K) v).toAlgHom
        (z : v.Completion ⊗[K] L)
  have hTensorTransport :
      infiniteTensorNormSubgroup
          (K := K) (L := L) v =
        (localTensorNormSubgroup
          (K := K) (L := L) v.1).map
            eVUnits.symm.toMonoidHom := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      refine
        ⟨localTensorDetNorm
            (K := K) (L := L) v.1
            (eTensorUnits z),
          ⟨eTensorUnits z, rfl⟩, ?_⟩
      apply eVUnits.injective
      change
        eVUnits
            (eVUnits.symm
              (localTensorDetNorm
                (K := K) (L := L) v.1
                (eTensorUnits z))) =
          eVUnits
            (infiniteTensorDetNorm
              (K := K) (L := L) v z)
      rw [eVUnits.apply_symm_apply]
      exact (hTensorNorm z).symm
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      refine ⟨eTensorUnits.symm z, ?_⟩
      apply eVUnits.injective
      change
        eVUnits
            (infiniteTensorDetNorm
              (K := K) (L := L) v
              (eTensorUnits.symm z)) =
          eVUnits
            (eVUnits.symm
              (localTensorDetNorm
                (K := K) (L := L) v.1 z))
      rw [hTensorNorm, eTensorUnits.apply_symm_apply,
        eVUnits.apply_symm_apply]
  let eLocalized :
      E ≃ₐ[v.1.Completion] w.1.Completion :=
    AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
      v.1 v.isNontrivial u
  let eBase :
      v.1.Completion ≃+* v.Completion :=
    eVField.symm
  let eExtension :
      E ≃+* w.Completion :=
    eLocalized.toRingEquiv.trans eWField.symm
  have hCompatible :
      RingHom.comp
          (algebraMap v.Completion w.Completion)
          eBase =
        RingHom.comp eExtension
          (algebraMap v.1.Completion E) := by
    have hWrapperCompletionSymm :=
      ringEquiv_compat_symm
        eVField eWField (by
          simpa [u, infinitePlaceAbsoluteValueExtension,
            eVField, eWField] using
            (infinitePlaceCompletionAlgEquiv_algebraMap
              (K := K) (L := L) v w hw))
    apply RingHom.ext
    intro x
    change
      algebraMap v.Completion w.Completion
          (eVField.symm x) =
        eWField.symm
          (eLocalized
            (algebraMap v.1.Completion E x))
    rw [eLocalized.commutes]
    exact
      DFunLike.congr_fun hWrapperCompletionSymm x
  have hNormTransport :
      (localNormSubgroup
          v.1.Completion E).map
            eVUnits.symm.toMonoidHom =
        localNormSubgroup
          v.Completion w.Completion := by
    ext x
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      refine
        ⟨Units.mapEquiv
            eExtension.toMulEquiv z, ?_⟩
      simpa [eBase, eVUnits] using
        (normUnits_map_ringEquiv
          eBase eExtension hCompatible z).symm
    · rintro ⟨z, rfl⟩
      refine
        ⟨normUnits v.1.Completion E
            ((Units.mapEquiv
              eExtension.toMulEquiv).symm z),
          ⟨(Units.mapEquiv
              eExtension.toMulEquiv).symm z, rfl⟩,
          ?_⟩
      have hTransport :=
        normUnits_map_ringEquiv
          eBase eExtension hCompatible
          ((Units.mapEquiv
            eExtension.toMulEquiv).symm z)
      rw [(Units.mapEquiv
        eExtension.toMulEquiv).apply_symm_apply] at hTransport
      simpa [eBase, eVUnits] using hTransport
  rw [hTensorTransport,
    localTensorNormSubgroup_eq_localNormSubgroup
      (K := K) (L := L) v.1 u v.isNontrivial]
  exact hNormTransport
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Ramification_Splitting_NormalClosure
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Complete splitting and normal closures

This file formalizes the normal-closure reduction for complete splitting.
For a finite Galois extension `M / K`, an intermediate field `L`, a
nontrivial absolute value `v` of `K`, and an extension `w` to `M`, put

* `G = Gal(M / K)`,
* `H = Gal(M / L)`, and
* `D = D(w / v)`.

Restriction of the conjugates of `w` gives an equivalence

`H \ G / D ≃ { extensions of v to L }`.

Thus the intrinsic complete-splitting condition for the possibly
non-Galois extension `L / K` is exactly the equality between the number
of double cosets and the number of left cosets.  If `M` is generated by
the `K`-conjugates of `L`, then `H` has trivial normal core.
`SplittingGroupTheory` consequently forces `D = 1`, so the place splits
completely already in `M`.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open HilbertRamification

section FiniteNormalClosure

variable
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

/-- Finiteness of the nonsplitting set in the original field
transports to its distinguished copy in the finite normal closure. -/
theorem finite_nonSplittingPlaces_originalField
    (hfinite :
      {v : HeightOneSpectrum (𝓞 K) |
        ¬ FinitePlaceSplitsCompletelyInExtension
          (K := K) (E := L) v}.Finite) :
    {v : HeightOneSpectrum (𝓞 K) |
      ¬ FinitePlaceSplitsCompletelyInExtension
        (K := K)
        (E := finiteNormalClosureOriginalField K L) v}.Finite := by
  simpa only [
    finitePlaceSplitsCompletelyInExtension_algEquiv
      (finiteNormalClosureOriginalFieldEquiv K L)] using hfinite

/-- Finiteness of the nonsplitting set in `L / K` implies finiteness
of the nonsplitting set in its finite normal closure. -/
theorem finite_nonSplittingPlaces_normalClosure_of_original
    (hfinite :
      {v : HeightOneSpectrum (𝓞 K) |
        ¬ FinitePlaceSplitsCompletelyInExtension
          (K := K) (E := L) v}.Finite) :
    {v : HeightOneSpectrum (𝓞 K) |
      ¬ FinitePlaceSplitsCompletely
        (K := K) (L := finiteNormalClosure K L) v}.Finite :=
  finite_nonSplittingPlaces_finiteNormalClosure K L
    (finite_nonSplittingPlaces_originalField K L hfinite)

end FiniteNormalClosure
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_IdelePowerLocalUnitSubgroup
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.IdeleClassGroup.normOneSubgroupCompactSpace _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.Modulus.congruenceSubgroup_normal _root_.RayClass.Modulus.infiniteCongruenceSubgroupFiniteIndex _root_.RayClass.congruenceSubgroupFiniteIndex _root_.RayClass.finiteCongruenceSubgroupFiniteRelIndex _root_.RayClass.ideleCongruenceSubgroupFiniteRelIndex _root_.RayClass.ideleCongruenceSupPrincipalFiniteIndex _root_.RayClass.narrowInfiniteCongruenceSubgroupFiniteIndex _root_.RayClass.ordinaryIdealClassSubgroupFiniteIndex _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseValued _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteIdeleGroupLocallyCompactSpace _root_.ideleGroupLocallyCompactSpace _root_.infiniteIdeleGroupLocallyCompactSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

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

/-- An `n`-th power of an `(S ∪ T)`-unit satisfies all local
power-unit conditions. -/
theorem sUnitNthPowersInField_le_principalIdelePowerLocalUnitSubgroup
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    sUnitNthPowersInField (K := K) n (S ∪ T) ≤
      principalIdelePowerLocalUnitSubgroup (K := K) n S T := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := hy
  obtain ⟨x, hx⟩ :=
    (MonoidHom.mem_range
      (G := SUnitGroup (K := K) (S ∪ T))).mp hz
  rw [powMonoidHom_apply] at hx
  subst z
  rw [principalIdelePowerLocalUnitSubgroup,
    Subgroup.mem_comap,
    mem_idelePowerLocalUnitSubgroup_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro w
    apply
      (MonoidHom.mem_range
        (G := w.Completionˣ)).mpr
    refine
      ⟨IdeleGroup.infiniteComponent w
        (IdeleGroup.principalIdele K (x : Kˣ)), ?_⟩
    simp only [powMonoidHom_apply, map_pow]
    have hxcoe :
        (SUnitGroup (K := K) (S ∪ T)).subtype x = (x : Kˣ) :=
      rfl
    rw [hxcoe]
  · intro v _
    apply
      (MonoidHom.mem_range
        (G := (v.adicCompletion K)ˣ)).mpr
    refine
      ⟨IdeleGroup.finiteComponent v
        (IdeleGroup.principalIdele K (x : Kˣ)), ?_⟩
    simp only [powMonoidHom_apply, map_pow]
    have hxcoe :
        (SUnitGroup (K := K) (S ∪ T)).subtype x = (x : Kˣ) :=
      rfl
    rw [hxcoe]
  · intro v hv
    have hxUnit :
        v.valuation K ((x : Kˣ) : K) = 1 :=
      (mem_SUnitGroup_iff (K := K) (S ∪ T) x).mp x.2 v hv
    rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
    rw [IdeleGroup.finiteComponent_principalIdele,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    have hxcoe :
        (SUnitGroup (K := K) (S ∪ T)).subtype x = (x : Kˣ) :=
      rfl
    rw [map_pow, hxcoe]
    change
      v.valuation K (((x : Kˣ) : K) ^ (n : ℕ)) = 1
    rw [map_pow, hxUnit, one_pow]

end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_ConductorLattice
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.chosenFinitePlaceCompletionAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Lattice operations on narrow finite conductors

Increasing a modulus decreases its ray congruence subgroup.  This
contravariance makes the narrow finite conductor of an intersection of
norm subgroups the pointwise maximum of their narrow finite conductors.
Under class-field correspondence, this is the finite-part lcm formula
for a compositum.  For a generated subgroup one obtains the
complementary divisibility by the pointwise minimum.
-/

open scoped NumberField Classical

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

/-- Finite idèle congruence subgroups are contravariant in the modulus. -/
theorem rayClassFiniteCongruenceSubgroup_antitone
    {m n : RayClass.FiniteModulus K} (hmn : m ≤ n) :
    RayClass.finiteCongruenceSubgroup n ≤
      RayClass.finiteCongruenceSubgroup m := by
  intro a ha v
  exact
    RayClass.localHigherUnitGroup_antitone
      (K := K) v (hmn v) (ha v)

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_Construction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued
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

/-- The canonical algebra structure on the localized completion used by the
finite-place local Artin map. -/
@[reducible]
noncomputable def finitePlaceLocalArtinLocalizedAlgebra
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    Algebra vK.Completion
      (AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w) := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  letI hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  exact inferInstance

omit [IsAbelianGalois K L] in
/-- The canonical finite-dimensional certificate for the localized
completion used by the finite-place local Artin map. -/
theorem finitePlaceLocalArtinFiniteDimensional
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    letI : Algebra vK.Completion E :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    FiniteDimensional vK.Completion E := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  let : Algebra vK.Completion E :=
    finitePlaceLocalArtinLocalizedAlgebra v w
  exact
    AlgebraicNumberTheory.Valuations.localizedCompletionModuleFinite
      vK hvK w

omit hKLfinite in
/-- The canonical abelian-Galois certificate for the localized completion
used by the finite-place local Artin map. -/
theorem finitePlaceLocalArtinIsAbelianGalois
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (_hKLfinite : FiniteDimensional K L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    letI : Algebra vK.Completion E :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    IsAbelianGalois vK.Completion E := by
  let : FiniteDimensional K L := _hKLfinite
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let E :=
    AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  let : Algebra vK.Completion E :=
    finitePlaceLocalArtinLocalizedAlgebra v w
  let : FiniteDimensional vK.Completion E :=
    finitePlaceLocalArtinFiniteDimensional
      (hKLfinite := _hKLfinite) v w
  exact
    LocalClassFieldTheory.localizedCompletion_isAbelianGalois
      vK hvK w

/-- The decomposition-group inclusion transporting localized automorphisms to the global Galois group. -/
noncomputable def finitePlaceLocalToGlobalMonoidHom
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    letI : Algebra vK.Completion E :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    (E ≃ₐ[vK.Completion] E) →* (L ≃ₐ[K] L) := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  letI : Algebra vK.Completion E :=
    finitePlaceLocalArtinLocalizedAlgebra v w
  let eD :
      absoluteValueDecompositionGroup K w.1 ≃*
        (E ≃ₐ[vK.Completion] E) :=
    decompositionGroupEquivAlgebraicLocalizationAut
      vK hvK w
  exact
    (absoluteValueDecompositionGroup K w.1).subtype.comp
      eD.symm.toMonoidHom

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_Conjugation
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued
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

/-- The algebraic localizations belonging to conjugate extensions of a
finite place are identified by the induced equivalence of completions. -/
noncomputable def finitePlaceConjugateLocalizedCompletionAlgEquiv
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
    Ewc ≃ₐ[vK.Completion] Ew := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let wc := absoluteValueExtensionConjugate vK w g
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  letI hwK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  letI : SMul K w.1.Completion := hwK.toSMul
  letI : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  letI hwcK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) wc.1
  letI : SMul K wc.1.Completion := hwcK.toSMul
  letI : Algebra vK.Completion wc.1.Completion :=
    AbsoluteValue.completionAlgebra vK wc.1 wc.2
  let Ew := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  let Ewc := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wc
  let eCompletion : wc.1.Completion ≃ₐ[vK.Completion]
      w.1.Completion :=
    { LocalClassFieldTheory.conjugateExtensionCompletionRingEquiv
        vK w g with
      commutes' :=
        LocalClassFieldTheory.conjugateExtensionCompletionRingEquiv_algebraMap
          vK w g }
  let e : Ewc ≃ₐ[vK.Completion] Ew :=
    (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
        vK hvK wc).trans
      (eCompletion.trans
        (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
          vK hvK w).symm)
  exact e

omit [IsAbelianGalois K L] in
/-- The conjugate-localization equivalence carries the canonical
embedding of `L` to the conjugate of that embedding. -/
theorem finitePlaceConjugateLocalizedCompletionAlgEquiv_toAlgebraicLocalization
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (g : L ≃ₐ[K] L) (x : L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let wc := absoluteValueExtensionConjugate vK w g
    let Ew := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    let Ewc := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wc
    letI : Algebra vK.Completion Ew :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    letI : Algebra vK.Completion Ewc :=
      finitePlaceLocalArtinLocalizedAlgebra v wc
    finitePlaceConjugateLocalizedCompletionAlgEquiv
        (K := K) (L := L) v w g
        (AbsoluteValue.toAlgebraicLocalization
          vK wc.1 wc.2 x) =
      AbsoluteValue.toAlgebraicLocalization
        vK w.1 w.2 (g x) := by
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
  apply
    (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
      vK hvK w).injective
  change
    LocalClassFieldTheory.conjugateExtensionCompletionRingEquiv
        vK w g
        (AbsoluteValue.toCompletion wc.1 x) =
      AbsoluteValue.toCompletion w.1 (g x)
  exact
    LocalClassFieldTheory.conjugateExtensionCompletionRingEquiv_toCompletion
      vK w g x

omit [IsAbelianGalois K L] in
/-- The inverse conjugate-localization equivalence carries the
canonical embedding back along the inverse global automorphism. -/
theorem
    finitePlaceConjugateLocalizedCompletionAlgEquiv_symm_toAlgebraicLocalization
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (g : L ≃ₐ[K] L) (x : L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let wc := absoluteValueExtensionConjugate vK w g
    let Ew := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    let Ewc := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wc
    letI : Algebra vK.Completion Ew :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    letI : Algebra vK.Completion Ewc :=
      finitePlaceLocalArtinLocalizedAlgebra v wc
    (finitePlaceConjugateLocalizedCompletionAlgEquiv
        (K := K) (L := L) v w g).symm
        (AbsoluteValue.toAlgebraicLocalization
          vK w.1 w.2 x) =
      AbsoluteValue.toAlgebraicLocalization
        vK wc.1 wc.2 (g.symm x) := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let wc := absoluteValueExtensionConjugate vK w g
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
  let e :=
    finitePlaceConjugateLocalizedCompletionAlgEquiv
      (K := K) (L := L) v w g
  apply e.injective
  rw [e.apply_symm_apply,
    finitePlaceConjugateLocalizedCompletionAlgEquiv_toAlgebraicLocalization,
    g.apply_symm_apply]

/-- Conjugation of a place intertwines the two localization
decomposition-group identifications on each local automorphism. -/
theorem finitePlaceDecompositionTransport_conjugate_apply
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (g : L ≃ₐ[K] L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let wc := absoluteValueExtensionConjugate vK w g
    let hvK : vK.IsNontrivial :=
      RayClass.adicAbv_isNontrivial v
    let Ew := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    let Ewc := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wc
    letI : Algebra vK.Completion Ew :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    letI : Algebra vK.Completion Ewc :=
      finitePlaceLocalArtinLocalizedAlgebra v wc
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
    ∀ tauC : Ewc ≃ₐ[vK.Completion] Ewc,
      (absoluteValueDecompositionGroup K wc.1).subtype
          (eDwc.symm tauC) =
        (absoluteValueDecompositionGroup K w.1).subtype
          (eDw.symm (AlgEquiv.autCongr e tauC)) := by
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
  change
    ∀ tauC : Ewc ≃ₐ[vK.Completion] Ewc,
      (absoluteValueDecompositionGroup K wc.1).subtype
          (eDwc.symm tauC) =
        (absoluteValueDecompositionGroup K w.1).subtype
          (eDw.symm (AlgEquiv.autCongr e tauC))
  intro tauC
  let tau := AlgEquiv.autCongr e tauC
  let rhoC : absoluteValueDecompositionGroup K wc.1 :=
    eDwc.symm tauC
  let rho : absoluteValueDecompositionGroup K w.1 :=
    eDw.symm tau
  change (rhoC.1 : L ≃ₐ[K] L) =
    (rho.1 : L ≃ₐ[K] L)
  apply AlgEquiv.ext
  intro z
  apply
    (AbsoluteValue.toAlgebraicLocalization
      vK w.1 w.2).injective
  have hcomm :
      g ((rhoC.1 : L ≃ₐ[K] L) (g.symm z)) =
        (rhoC.1 : L ≃ₐ[K] L) z := by
    have hg :
        g * (rhoC.1 : L ≃ₐ[K] L) =
          (rhoC.1 : L ≃ₐ[K] L) * g :=
      (inferInstance :
        IsMulCommutative (L ≃ₐ[K] L)).is_comm.comm _ _
    calc
      g ((rhoC.1 : L ≃ₐ[K] L) (g.symm z)) =
          (g * (rhoC.1 : L ≃ₐ[K] L)) (g.symm z) := rfl
      _ = ((rhoC.1 : L ≃ₐ[K] L) * g) (g.symm z) :=
        DFunLike.congr_fun hg (g.symm z)
      _ = (rhoC.1 : L ≃ₐ[K] L) (g (g.symm z)) := rfl
      _ = (rhoC.1 : L ≃ₐ[K] L) z := by
        rw [g.apply_symm_apply]
  calc
    AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
        ((rhoC.1 : L ≃ₐ[K] L) z) =
      AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
        (g ((rhoC.1 : L ≃ₐ[K] L) (g.symm z))) := by
          rw [hcomm]
    _ = e
        (AbsoluteValue.toAlgebraicLocalization vK wc.1 wc.2
          ((rhoC.1 : L ≃ₐ[K] L) (g.symm z))) := by
          rw [
            finitePlaceConjugateLocalizedCompletionAlgEquiv_toAlgebraicLocalization]
    _ = e
        (eDwc rhoC
          (AbsoluteValue.toAlgebraicLocalization
            vK wc.1 wc.2 (g.symm z))) := by
          rw [localizationRamificationGroups_decompositionGroupEquiv_toLocalization]
    _ = e
        (tauC
          (AbsoluteValue.toAlgebraicLocalization
            vK wc.1 wc.2 (g.symm z))) := by
          rw [eDwc.apply_symm_apply]
    _ = (AlgEquiv.autCongr e tauC)
        (AbsoluteValue.toAlgebraicLocalization
          vK w.1 w.2 z) := by
          change
            e
                (tauC
                  (AbsoluteValue.toAlgebraicLocalization
                    vK wc.1 wc.2 (g.symm z))) =
              e
                (tauC
                  (e.symm
                    (AbsoluteValue.toAlgebraicLocalization
                      vK w.1 w.2 z)))
          rw [
            finitePlaceConjugateLocalizedCompletionAlgEquiv_symm_toAlgebraicLocalization]
    _ = tau
        (AbsoluteValue.toAlgebraicLocalization
          vK w.1 w.2 z) := by
          rfl
    _ = eDw rho
        (AbsoluteValue.toAlgebraicLocalization
          vK w.1 w.2 z) := by
          rw [eDw.apply_symm_apply]
    _ = AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
        ((rho.1 : L ≃ₐ[K] L) z) := by
          rw [localizationRamificationGroups_decompositionGroupEquiv_toLocalization]

/-- Conjugation of a place intertwines the two localization
decomposition-group identifications after inclusion in the global
Galois group. -/
theorem finitePlaceDecompositionTransport_conjugate
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (g : L ≃ₐ[K] L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let wc := absoluteValueExtensionConjugate vK w g
    let hvK : vK.IsNontrivial :=
      RayClass.adicAbv_isNontrivial v
    let Ew := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    let Ewc := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wc
    letI : Algebra vK.Completion Ew :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    letI : Algebra vK.Completion Ewc :=
      finitePlaceLocalArtinLocalizedAlgebra v wc
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
    (absoluteValueDecompositionGroup K wc.1).subtype.comp
        eDwc.symm.toMonoidHom =
      ((absoluteValueDecompositionGroup K w.1).subtype.comp
          eDw.symm.toMonoidHom).comp
        (AlgEquiv.autCongr e).toMonoidHom := by
  apply MonoidHom.ext
  intro tauC
  exact
    finitePlaceDecompositionTransport_conjugate_apply
      (K := K) (L := L) v w g tauC

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_CrossLocalRestriction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Cross-base restriction of finite-place Artin homomorphisms

This module compares localized completions in a square of number fields with different base fields and transports restriction through the corresponding decomposition groups.
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

/-- The localized completion at a finite place, with its completion-algebra
tower hidden behind one named type. -/
noncomputable abbrev finitePlaceArtinLocalizedCompletion
    (F M : Type) [Field F] [NumberField F]
    [Field M] [NumberField M] [Algebra F M]
    (v : HeightOneSpectrum (𝓞 F))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv F v) M) : Type :=
  let vF := NumberField.HeightOneSpectrum.adicAbv F v
  let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vF w
  letI : Algebra vF.Completion E :=
    finitePlaceLocalArtinLocalizedAlgebra (K := F) (L := M) v w
  E

/-- Localized automorphisms with the completion tower hidden behind one named
type. -/
noncomputable abbrev finitePlaceArtinLocalizedAutomorphism
    (F M : Type) [Field F] [NumberField F]
    [Field M] [NumberField M] [Algebra F M]
    (v : HeightOneSpectrum (𝓞 F))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv F v) M) : Type :=
  let vF := NumberField.HeightOneSpectrum.adicAbv F v
  let E := finitePlaceArtinLocalizedCompletion F M v w
  letI : Algebra vF.Completion E :=
    finitePlaceLocalArtinLocalizedAlgebra (K := F) (L := M) v w
  E ≃ₐ[vF.Completion] E

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_NormRestriction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued
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

abbrev finitePlaceNormLocalizedCompletion
    (F M : Type) [Field F] [Field M] [Algebra F M]
    [NumberField F]
    (v : HeightOneSpectrum (𝓞 F))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv F v) M) :=
  AlgebraicNumberTheory.Valuations.LocalizedCompletion
    (NumberField.HeightOneSpectrum.adicAbv F v) w

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

local instance finitePlaceNormLowerExtensionAlgebra_r279dbe_1 :
    Algebra K w.1.Completion :=
  AbsoluteValue.extensionCompletionAlgebra
    (K := K) w.1
local instance finitePlaceNormLowerCompletionAlgebra_r279dbe_1 :
    Algebra Cₙ w.1.Completion :=
  AbsoluteValue.completionAlgebra vKₙ w.1 w.2
local instance finitePlaceNormLowerGlobalAlgebra_r279dbe_1 :
    Algebra K Eₙ :=
  LocalClassFieldTheory.localizedCompletionGlobalAlgebra vKₙ w
local instance finitePlaceNormUpperExtensionAlgebra_r279dbe_1 :
    Algebra K' w'.1.Completion :=
  AbsoluteValue.extensionCompletionAlgebra
    (K := K') w'.1
local instance finitePlaceNormUpperCompletionAlgebra :
    Algebra Dₙ w'.1.Completion :=
  AbsoluteValue.completionAlgebra vKₙ' w'.1 w'.2

local instance finitePlaceNormUpperGlobalAlgebra_r279dbe_1 :
    Algebra K' Eₙ' :=
  LocalClassFieldTheory.localizedCompletionGlobalAlgebra vKₙ' w'
local instance finitePlaceNormLowerNontriviallyNormedField_r279dbe_1 :
    NontriviallyNormedField Cₙ :=
  absoluteValueExtension_completionNontriviallyNormedField
    vKₙ (RayClass.adicAbv_isNontrivial v)
local instance finitePlaceNormLowerLocallyCompactSpace_r279dbe_1 :
    LocallyCompactSpace Cₙ :=
  AbsoluteValue.Completion.locallyCompactSpace
    (finitePlaceCompletionBaseMap_isometry v)
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePlaceNormUpperNontriviallyNormedField
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePlaceNormUpperLocallyCompactSpace
local instance finitePlaceNormLowerLocalizedFiniteDimensional :
    FiniteDimensional Cₙ Eₙ :=
  AlgebraicNumberTheory.Valuations.localizedCompletionModuleFinite
    vKₙ (RayClass.adicAbv_isNontrivial v) w

local instance finitePlaceNormLowerLocalizedAbelianGalois_r279dbe_1 :
    IsAbelianGalois Cₙ Eₙ :=
  LocalClassFieldTheory.localizedCompletion_isAbelianGalois
    vKₙ (RayClass.adicAbv_isNontrivial v) w
local instance finitePlaceNormUpperLocalizedFiniteDimensional :
    FiniteDimensional Dₙ Eₙ' :=
  AlgebraicNumberTheory.Valuations.localizedCompletionModuleFinite
    vKₙ' (RayClass.adicAbv_isNontrivial W) w'

local instance finitePlaceNormUpperLocalizedAbelianGalois :
    IsAbelianGalois Dₙ Eₙ' :=
  LocalClassFieldTheory.localizedCompletion_isAbelianGalois
    vKₙ' (RayClass.adicAbv_isNontrivial W) w'

end FinitePlaceNormRestrictionInstances

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_InfinitePlaceArtin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.instContinuousSMulPadicLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul
attribute [-simp] _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfieldEmbedding_coe _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Archimedean Artin homomorphisms

At a ramified infinite place, the local extension is complex over
real.  Its Artin homomorphism sends the sign of a real unit to the
corresponding complex-conjugation element of the decomposition group.
At an unramified infinite place the decomposition group, and hence the
local homomorphism, is trivial.
-/

open scoped BigOperators Classical IsMulCommutative NumberField
  NumberField.LiesOver
open NumberField IsDedekindDomain
open IdeleGroup RelativeIdeleGroup

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open HilbertRamification
open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

section Galois

variable [IsGalois K L]

/-- The kernel of the actual Artin homomorphism at an infinite place
is exactly the determinant-norm image on the corresponding tensor
factor. -/
theorem chosenInfinitePlaceArtinMonoidHom_ker
    (v : InfinitePlace K) :
    MonoidHom.ker
        (chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L) v) =
      infiniteTensorNormSubgroup
        (K := K) (L := L) v := by
  let w :=
    chosenInfinitePlaceAbove
      (L := L) v
  have hw :
      w.comap (algebraMap K L) = v :=
    chosenInfinitePlaceAbove_comap
      (L := L) v
  let : w.1.LiesOver v.1 :=
    ⟨congrArg (fun q : InfinitePlace K => q.1) hw⟩
  rw [
    infiniteTensorNormSubgroup_eq_localNormSubgroup
      (K := K) (L := L) v w hw]
  by_cases hUnramified : w.IsUnramified K
  · have hDegree :
        Module.finrank v.Completion w.Completion = 1 :=
      InfinitePlace.IsUnramified.finrank_eq_one v hUnramified
    have hNormTop :
        localNormSubgroup
          v.Completion w.Completion = ⊤ := by
      apply top_unique
      intro x _
      refine
        ⟨Units.map
            (algebraMap
              v.Completion w.Completion).toMonoidHom x,
          ?_⟩
      apply Units.ext
      change
        Algebra.norm v.Completion
            (algebraMap v.Completion w.Completion
              (x : v.Completion)) =
          (x : v.Completion)
      rw [Algebra.norm_algebraMap, hDegree, pow_one]
    rw [hNormTop, MonoidHom.ker_eq_top_iff]
    have hUnramified' :
        (chosenInfinitePlaceAbove (L := L) v).IsUnramified K := by
      simpa only [w] using hUnramified
    unfold chosenInfinitePlaceArtinMonoidHom
    unfold infinitePlaceArtinMonoidHomOfPlace
    rw [dite_eq_left hUnramified']
  · have hRamified : w.IsRamified K :=
      hUnramified
    have hvReal : v.IsReal := by
      rw [← hw]
      exact hRamified.isReal
    let σ :=
      ramifiedInfinitePlaceConjugation
        (K := K) w hRamified
    have hσ :=
      ramifiedInfinitePlaceConjugation_isConj
        (K := K) w hRamified
    have hσsq : σ * σ = 1 := by
      exact
        ramifiedInfinitePlaceConjugation_sq
          (K := K) w hRamified
    let signToGalois : ℤˣ →* (L ≃ₐ[K] L) :=
      { toFun := fun u =>
          if u = 1 then 1 else σ
        map_one' := ite_eq_left rfl
        map_mul' := by
          intro x y
          rcases Int.units_eq_one_or x with rfl | rfl
          · simp
          rcases Int.units_eq_one_or y with rfl | rfl
          · simp
          · simp [hσsq] }
    have hσne : σ ≠ 1 :=
      (NumberField.ComplexEmbedding.isConj_ne_one_iff
        hσ).2
        (InfinitePlace.isComplex_iff.mp
          hRamified.isComplex)
    have hSignInjective :
        Function.Injective signToGalois := by
      intro x y hxy
      rcases Int.units_eq_one_or x with rfl | rfl
      · rcases Int.units_eq_one_or y with rfl | rfl
        · rfl
        · exfalso
          apply hσne
          simpa [signToGalois] using
            hxy.symm
      · rcases Int.units_eq_one_or y with rfl | rfl
        · exfalso
          apply hσne
          simpa [signToGalois] using
            hxy
        · rfl
    let eRealField :
        v.Completion ≃+* ℝ :=
      InfinitePlace.Completion.ringEquivRealOfIsReal
        hvReal
    let completionUnitsEquivRealUnits :
        v.Completionˣ ≃* ℝˣ :=
      Units.mapEquiv eRealField.toMulEquiv
    have hwComplex : w.IsComplex :=
      hRamified.isComplex
    let eComplexField :
        w.Completion ≃+* ℂ :=
      InfinitePlace.Completion.ringEquivComplexOfIsComplex
        hwComplex
    let eComplexUnits :
        w.Completionˣ ≃* ℂˣ :=
      Units.mapEquiv eComplexField.toMulEquiv
    let :
        NumberField.ComplexEmbedding.LiesOver
          (InfinitePlace.Completion.extensionEmbedding w)
          (InfinitePlace.Completion.extensionEmbedding v) :=
      InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal
        w hvReal
    have hCompletionCompatible :
        RingHom.comp (algebraMap ℝ ℂ) eRealField =
          RingHom.comp eComplexField
            (algebraMap v.Completion w.Completion) := by
      ext x
      simp [eRealField, eComplexField]
    have hCompletionCompatibleSymm :=
      LocalClassFieldTheory.ringEquiv_compat_symm
        eRealField eComplexField hCompletionCompatible
    have hRealComplexNormTransport :
        (localNormSubgroup ℝ ℂ).map
            completionUnitsEquivRealUnits.symm.toMonoidHom =
          localNormSubgroup
            v.Completion w.Completion := by
      ext x
      constructor
      · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
        refine ⟨eComplexUnits.symm z, ?_⟩
        simpa [completionUnitsEquivRealUnits,
          eComplexUnits] using
          (LocalClassFieldTheory.normUnits_map_ringEquiv
            eRealField.symm eComplexField.symm
            hCompletionCompatibleSymm z).symm
      · rintro ⟨z, rfl⟩
        refine
          ⟨normUnits ℝ ℂ (eComplexUnits z),
            ⟨eComplexUnits z, rfl⟩, ?_⟩
        have hInverse :
            Units.mapEquiv eComplexField.symm.toMulEquiv
                (eComplexUnits z) = z := by
          change
            (Units.mapEquiv eComplexField.toMulEquiv).symm
                (eComplexUnits z) = z
          change eComplexUnits.symm (eComplexUnits z) = z
          exact eComplexUnits.symm_apply_apply z
        calc
          completionUnitsEquivRealUnits.symm
              (normUnits ℝ ℂ (eComplexUnits z)) =
            normUnits v.Completion w.Completion
              (Units.mapEquiv eComplexField.symm.toMulEquiv
                (eComplexUnits z)) := by
              simpa [completionUnitsEquivRealUnits] using
                LocalClassFieldTheory.normUnits_map_ringEquiv
                  eRealField.symm eComplexField.symm
                  hCompletionCompatibleSymm
                  (eComplexUnits z)
          _ = normUnits v.Completion w.Completion z := by
            rw [hInverse]
    simp only [chosenInfinitePlaceArtinMonoidHom,
      infinitePlaceArtinMonoidHomOfPlace,
      w, hUnramified]
    change
      MonoidHom.ker
          (signToGalois.comp
            (LocalClassFieldTheory.realUnitsSign.comp
              completionUnitsEquivRealUnits.toMonoidHom)) =
        localNormSubgroup
          v.Completion w.Completion
    calc
      MonoidHom.ker
          (signToGalois.comp
            (LocalClassFieldTheory.realUnitsSign.comp
              completionUnitsEquivRealUnits.toMonoidHom)) =
          MonoidHom.ker
            (LocalClassFieldTheory.realUnitsSign.comp
              completionUnitsEquivRealUnits.toMonoidHom) :=
        MonoidHom.ker_comp_of_injective _ _ hSignInjective
      _ =
          Subgroup.map completionUnitsEquivRealUnits.symm.toMonoidHom
            (MonoidHom.ker LocalClassFieldTheory.realUnitsSign) :=
        MonoidHom.ker_comp_mulEquiv
          LocalClassFieldTheory.realUnitsSign
          completionUnitsEquivRealUnits
      _ =
          Subgroup.map completionUnitsEquivRealUnits.symm.toMonoidHom
            (localNormSubgroup ℝ ℂ) := by
        rw [LocalClassFieldTheory.realUnitsSign_ker_eq_complexNormSubgroup]
      _ = localNormSubgroup v.Completion w.Completion :=
        hRealComplexNormTransport

end Galois

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.KummerTheory_Concrete_FinitePlaceDecomposition
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued _root_.relativeUnrestrictedSPlaceFactorCommGroup _root_.scaledRelativeIntegerLatticeQuotientFinite
attribute [-simp] _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_primitiveRoot _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.LocalClassFieldTheory.completionProductUnitsEquivRightCosets_apply_coe _root_.LocalClassFieldTheory.conjugateExtensionCompletionRingEquiv_toCompletion _root_.LocalClassFieldTheory.localTensorEvaluation_tmul _root_.LocalClassFieldTheory.mem_decompositionRightCosetsFinset _root_.LocalClassFieldTheory.rightCosetCompletionUnitsEquiv_apply_coe _root_.LocalClassFieldTheory.rightCosetExtensionEquiv_apply _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.finitePlaceBelow_finitePlaceExtensionCentre _root_.finitePlaceExtensionAdicCompletionRingEquiv_toCompletion _root_.finitePlaceExtensionCentreInFibre_coe _root_.finitePlaceExtensionCentre_asIdeal _root_.finitePlaceExtensionCompletionRingEquiv_toCompletion _root_.finitePlaceExtensionEquivAbove_coe _root_.finitePlaceLocalTensorDecompositionComponentRingHom_apply _root_.finitePlaceLocalTensorDecompositionComponent_add _root_.finitePlaceLocalTensorDecompositionComponent_tmul _root_.finitePlaceLocalTensorDecompositionComponent_zero _root_.finitePlaceLocalTensorDecompositionUnitsComponent_coe _root_.finitePlaceLocalTensorDecompositionUnitsEquiv_apply _root_.finitePlaceTensorRingEquivAboveAdic_apply_extension _root_.finitePlaceTensorUnitsEquivAboveAdic_apply_extension _root_.infinitePlaceAboveEquivExtension_apply_val _root_.infinitePlaceTensorRingEquivAbove_apply _root_.infinitePlaceTensorUnitsEquivAbove_apply _root_.infinitePlace_mult_smul _root_.mem_finitePlaceDecompositionGroup_iff _root_.restrictAbsoluteValueExtensionToIntermediate_apply _root_.ringOfIntegersToFinitePlaceExtensionValuationSubring_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Kummer radicals and finite-place decomposition fields

For a finite Galois extension containing an `n`-th root `β` of a
base-field unit `a`, this file identifies the local `n`-th-power
condition on `a` with membership of `β` in the decomposition field.

The proof uses the canonical comparison between the two models of the
finite-place completion and the algebraic localization realization of
the decomposition field.  The only Kummer input is the usual fact that
two roots with the same `n`-th power differ by an `n`-th root of unity.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory

noncomputable section

namespace KummerTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

omit [NumberField K] [FiniteDimensional K L] in
/-- If a Kummer radicand is an `n`-th power in an absolute-value
completion, its chosen root lies in the corresponding decomposition
field.  This is the completion-level source behind both the finite and
archimedean localization arguments. -/
theorem
    kummerRadicand_root_mem_decompositionFixedField_of_mem_nthPowerSubgroup
    (vK : AbsoluteValue K ℝ)
    (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a : Kˣ) (beta : Lˣ)
    (hbeta :
      beta ^ (n : ℕ) =
        Units.map (algebraMap K L).toMonoidHom a)
    (ha :
      Units.map
            (algebraMap K vK.Completion).toMonoidHom a ∈
        (powMonoidHom (n : ℕ) :
          vK.Completionˣ →* vK.Completionˣ).range) :
    (beta : L) ∈
      IntermediateField.fixedField
        (absoluteValueDecompositionGroup K w.1) := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let := localizedCompletionGlobalAlgebra vK w
  let := localizedCompletionIsScalarTower vK w
  let C := vK.Completion
  let E := LocalizedCompletion vK w
  let toE :=
    AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
  let aC : Cˣ :=
    Units.map (algebraMap K C).toMonoidHom a
  have hbeta_val :
      (beta : L) ^ (n : ℕ) =
        algebraMap K L (a : K) := by
    simpa using congrArg Units.val hbeta
  obtain ⟨yC, hyC⟩ :=
    (MonoidHom.mem_range
      (G := Cˣ)).mp ha
  rw [powMonoidHom_apply] at hyC
  let betaE : Eˣ :=
    Units.map toE.toMonoidHom beta
  let yE : Eˣ :=
    Units.map (algebraMap C E).toMonoidHom yC
  have hbetaE :
      betaE ^ (n : ℕ) =
        Units.map (algebraMap C E).toMonoidHom aC := by
    apply Units.ext
    change
      toE (beta : L) ^ (n : ℕ) =
        algebraMap C E (algebraMap K C (a : K))
    calc
      toE (beta : L) ^ (n : ℕ) =
          toE ((beta : L) ^ (n : ℕ)) := by
        exact
          (map_pow toE (beta : L) (n : ℕ)).symm
      _ = toE (algebraMap K L (a : K)) := by
        rw [hbeta_val]
      _ = algebraMap C E (algebraMap K C (a : K)) :=
        AbsoluteValue.toAlgebraicLocalization_algebraMap
          vK w.1 w.2 (a : K)
  have hyE :
      yE ^ (n : ℕ) =
        Units.map (algebraMap C E).toMonoidHom aC := by
    calc
      yE ^ (n : ℕ) =
          Units.map (algebraMap C E).toMonoidHom
            (yC ^ (n : ℕ)) := by
        exact
          (map_pow
            (Units.map (algebraMap C E).toMonoidHom)
            yC (n : ℕ)).symm
      _ = Units.map (algebraMap C E).toMonoidHom aC := by
        rw [hyC]
  let q : Eˣ := betaE / yE
  have hq : q ^ (n : ℕ) = 1 :=
    KummerTheory.div_pow_eq_one_of_pow_eq_pow
      (hbetaE.trans hyE.symm)
  obtain ⟨zeta, hzeta_mem⟩ := hmu
  have hzeta :
      IsPrimitiveRoot zeta (n : ℕ) :=
    (mem_primitiveRoots n.pos).mp hzeta_mem
  have hzetaE :
      IsPrimitiveRoot
        (algebraMap C E (algebraMap K C zeta))
        (n : ℕ) :=
    (hzeta.map_of_injective
        (algebraMap K C).injective).map_of_injective
      (algebraMap C E).injective
  have hq_val :
      (q : E) ^ (n : ℕ) = 1 := by
    simpa using congrArg Units.val hq
  obtain ⟨i, _hi, hzetaq⟩ :=
    hzetaE.eq_pow_of_pow_eq_one hq_val
  have hbeta_base :
      toE (beta : L) ∈
        Set.range (algebraMap C E) := by
    refine
      ⟨(algebraMap K C zeta) ^ i * (yC : C), ?_⟩
    calc
      algebraMap C E
            ((algebraMap K C zeta) ^ i * (yC : C)) =
          (algebraMap C E (algebraMap K C zeta)) ^ i *
            algebraMap C E (yC : C) := by
        rw [map_mul, map_pow]
      _ = (q : E) * (yE : E) := by
        rw [hzetaq]
        rfl
      _ = toE (beta : L) := by
        simpa [betaE] using
          congrArg Units.val
            (show q * yE = betaE by simp [q])
  have hcomap :
      (beta : L) ∈
        ((algebraMap C E).fieldRange).comap toE :=
    hbeta_base
  rw [
    localizedCompletion_baseField_comap_eq_fixedField_decompositionGroup
      vK hvK w] at hcomap
  simpa [C, E, toE] using hcomap

omit [FiniteDimensional K L] in
/-- A Kummer radicand is an `n`-th power in the finite-place completion
exactly when its chosen root belongs to the decomposition field at the
chosen extension of that place. -/
theorem
    finitePlaceKummerRadicand_mem_nthPowerSubgroup_iff_root_mem_decompositionFixedField
    (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a : Kˣ) (beta : Lˣ)
    (hbeta :
      beta ^ (n : ℕ) =
        Units.map (algebraMap K L).toMonoidHom a) :
    Units.map
          (algebraMap K (v.adicCompletion K)).toMonoidHom a ∈
        (powMonoidHom (n : ℕ) :
          (v.adicCompletion K)ˣ →*
            (v.adicCompletion K)ˣ).range ↔
      (beta : L) ∈
        IntermediateField.fixedField
          (absoluteValueDecompositionGroup K
            (chosenFinitePlaceExtension (L := L) v).1) := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let vK := HeightOneSpectrum.adicAbv K v
  let w := chosenFinitePlaceExtension (L := L) v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let := localizedCompletionGlobalAlgebra vK w
  let := localizedCompletionIsScalarTower vK w
  let C := vK.Completion
  let E := LocalizedCompletion vK w
  let toE :=
    AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
  let e :
      Cˣ ≃ₜ* (v.adicCompletion K)ˣ :=
    finitePlaceCompletionUnitsContinuousMulEquiv v
  let aC : Cˣ :=
    Units.map (algebraMap K C).toMonoidHom a
  have he_base (u : Kˣ) :
      e (Units.map (algebraMap K C).toMonoidHom u) =
        Units.map
          (algebraMap K (v.adicCompletion K)).toMonoidHom u := by
    apply Units.ext
    let x : WithAbs vK :=
      (WithAbs.equiv vK).symm (u : K)
    change
      finitePlaceCompletionRingHom v (x : C) =
        algebraMap K (v.adicCompletion K) (u : K)
    rw [finitePlaceCompletionRingHom_coe]
    rfl
  have hbeta_val :
      (beta : L) ^ (n : ℕ) =
        algebraMap K L (a : K) := by
    simpa using congrArg Units.val hbeta
  constructor
  · intro ha
    apply
      kummerRadicand_root_mem_decompositionFixedField_of_mem_nthPowerSubgroup
        (K := K) (L := L) vK hvK w n hmu a beta hbeta
    obtain ⟨y, hy⟩ :=
      (MonoidHom.mem_range
        (G := (v.adicCompletion K)ˣ)).mp ha
    rw [powMonoidHom_apply] at hy
    apply
      (MonoidHom.mem_range
        (G := Cˣ)).mpr
    refine ⟨e.symm y, ?_⟩
    rw [powMonoidHom_apply]
    apply e.injective
    calc
      e ((e.symm y) ^ (n : ℕ)) =
          (e (e.symm y)) ^ (n : ℕ) :=
        map_pow e (e.symm y) (n : ℕ)
      _ = y ^ (n : ℕ) := by
        rw [e.apply_symm_apply]
      _ =
          Units.map
            (algebraMap K
              (v.adicCompletion K)).toMonoidHom a := hy
      _ = e aC := (he_base a).symm
  · intro hfixed
    have hcomap :
        (beta : L) ∈
          ((algebraMap C E).fieldRange).comap toE := by
      rw [
        localizedCompletion_baseField_comap_eq_fixedField_decompositionGroup
          vK hvK w]
      simpa [vK, w] using hfixed
    change
      toE (beta : L) ∈ Set.range (algebraMap C E)
      at hcomap
    obtain ⟨y, hy⟩ := hcomap
    have hy_ne : y ≠ 0 := by
      intro hy_zero
      have hbeta_zero : (beta : L) = 0 := by
        apply toE.injective
        calc
          toE (beta : L) =
              algebraMap C E y := hy.symm
          _ = 0 := by rw [hy_zero, map_zero]
          _ = toE 0 := (map_zero toE).symm
      exact beta.ne_zero hbeta_zero
    let yC : Cˣ := Units.mk0 y hy_ne
    have hyC : yC ^ (n : ℕ) = aC := by
      apply Units.ext
      apply (algebraMap C E).injective
      change
        algebraMap C E (y ^ (n : ℕ)) =
          algebraMap C E (algebraMap K C (a : K))
      calc
        algebraMap C E (y ^ (n : ℕ)) =
            (algebraMap C E y) ^ (n : ℕ) := by
          exact
            map_pow (algebraMap C E) y (n : ℕ)
        _ = toE (beta : L) ^ (n : ℕ) := by
          rw [hy]
        _ = toE ((beta : L) ^ (n : ℕ)) := by
          exact
            (map_pow toE (beta : L) (n : ℕ)).symm
        _ = toE (algebraMap K L (a : K)) := by
          rw [hbeta_val]
        _ = algebraMap C E (algebraMap K C (a : K)) :=
          AbsoluteValue.toAlgebraicLocalization_algebraMap
            vK w.1 w.2 (a : K)
    apply
      (MonoidHom.mem_range
        (G := (v.adicCompletion K)ˣ)).mpr
    refine ⟨e yC, ?_⟩
    rw [powMonoidHom_apply]
    calc
      (e yC) ^ (n : ℕ) =
          e (yC ^ (n : ℕ)) := by
        exact
          (map_pow e yC (n : ℕ)).symm
      _ = e aC := by rw [hyC]
      _ =
          Units.map
            (algebraMap K
              (v.adicCompletion K)).toMonoidHom a :=
        he_base a

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.KummerTheory_Concrete_SUnitPreparation_SUnitLocalPowerKernel
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.chosenFinitePlaceCompletionAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# The local-power kernel of S-units

The localization map on `S`-units, its kernel, its quotient by global powers, and the associated Kummer radical.
-/

open scoped NumberField Classical IsMulCommutative NNReal ValuativeRel
open NumberField IsDedekindDomain
open LocalFieldTheory

noncomputable section

namespace KummerTheory

variable {K : Type*} [Field K]
    [numberFieldK : NumberField K]

/-- Elementwise description of the local-power kernel `Δ`. -/
theorem mem_sUnitLocalPowerKernel_iff
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (x : SUnitGroup (K := K) S) :
    x ∈ sUnitLocalPowerKernel (K := K) n S T ↔
      ∀ v : T,
        Units.map
            (algebraMap K
              ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)).toMonoidHom
            (x : Kˣ) ∈
          (powMonoidHom (n : ℕ) :
            ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)ˣ →*
              ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)ˣ).range := by
  rw [sUnitLocalPowerKernel, MonoidHom.mem_ker]
  constructor
  · intro hx v
    have hv := congrFun hx v
    rw [Pi.one_apply] at hv
    exact (QuotientGroup.eq_one_iff _).mp hv
  · intro hx
    funext v
    exact (QuotientGroup.eq_one_iff _).mpr (hx v)

/-- Global `n`-th powers are local `n`-th powers at every place. -/
theorem nthPowerSubgroup_le_sUnitLocalPowerKernel
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    (powMonoidHom (n : ℕ) :
        SUnitGroup (K := K) S →*
          SUnitGroup (K := K) S).range ≤
      sUnitLocalPowerKernel (K := K) n S T := by
  intro x hx
  obtain ⟨y, hy⟩ :=
    (MonoidHom.mem_range
      (G := SUnitGroup (K := K) S)).mp hx
  rw [powMonoidHom_apply] at hy
  subst x
  rw [sUnitLocalPowerKernel, MonoidHom.mem_ker, map_pow]
  change (sUnitLocalPowerMap (K := K) n S T y) ^ (n : ℕ) = 1
  funext v
  exact (QuotientGroup.eq_one_iff _).mpr
    ((MonoidHom.mem_range
      (G :=
        ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)ˣ)).mpr
      ⟨_, by rw [powMonoidHom_apply]⟩)

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PadicField
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instDiscreteTopology _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.standardLubinTateLevelCompleteDVF_hasExtensionInstance _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.LubinTateSeries.standardLubinTateSeries_toPowerSeries _root_.LubinTate.SameUniformizer.coeff_recursiveIntertwiner _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.LubinTate.SameUniformizer.intertwinerApproximation_zero _root_.LubinTate.SameUniformizer.standardLubinTateEndomorphism_coeff_one _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTateLevelCoefficientHom_apply _root_.LubinTate.standardLubinTateLevelGenerator_coe _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_C _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_X _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_coe _root_.LubinTate.standardLubinTatePolynomialIterateOverSeparableClosure_eval _root_.LubinTate.standardLubinTatePolynomialIterate_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_zero _root_.LubinTate.standardLubinTatePolynomial_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomial_eval _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries_eq_series _root_.LubinTate.standardLubinTatePrimitivePointInteger_coe _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTatePrimitivePolynomial_coeff_zero _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_algebraMap _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.galEquivDecompositionGroup_coe _root_.RamificationTheory.HilbertRamification.CompleteDVF.residueAction_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The concrete p-adic field `ℚ_[p]`

This file is the first concrete example leaf for the DVF navigation library.
It deliberately uses mathlib's public p-adic objects directly in theorem
statements instead of introducing public aliases for `ℚ_[p]` or its unit group.
-/

noncomputable section

namespace LocalFieldTheory.DiscreteValuationField
namespace Examples
namespace Qp

open Filter
open scoped Topology
open scoped WithZero

open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField

/-- The local-field structure theory, the local-field structure classification, `p`-adic base-field direction:
`ℚ_[p]` is a local field in the chosen-complete-DVF sense used in this
formalization. -/
noncomputable def padicLocalField
    (p : ℕ) [Fact p.Prime] :
    LocalField ℚ_[p] := by
  let F : CompleteDVF ℚ_[p] := padicCompleteDVF p
  haveI : Finite F.residueField := by
    simpa [F] using padicCompleteDVF_residueField_finite p
  exact { toCompleteDVF := F }

end Qp
end Examples
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_ChangedUniformizerCoefficient
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.standardLubinTateLevelCompleteDVF_hasExtensionInstance _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHomOfMaximalIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.LubinTateSeries.standardLubinTateSeries_toPowerSeries _root_.LubinTate.SameUniformizer.coeff_recursiveIntertwiner _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.LubinTate.SameUniformizer.intertwinerApproximation_zero _root_.LubinTate.SameUniformizer.standardLubinTateEndomorphism_coeff_one _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTateLevelCoefficientHom_apply _root_.LubinTate.standardLubinTateLevelGenerator_coe _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_C _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_X _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_coe _root_.LubinTate.standardLubinTatePolynomialIterateOverSeparableClosure_eval _root_.LubinTate.standardLubinTatePolynomialIterate_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_zero _root_.LubinTate.standardLubinTatePolynomial_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomial_eval _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries_eq_series _root_.LubinTate.standardLubinTatePrimitivePointInteger_coe _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTatePrimitivePolynomial_coeff_zero _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_algebraMap _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.residueAction_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.intrinsicRamificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberDepthOfUniqueExtension_depth _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The coefficient source for the p-adic changed-uniformizer intertwiner

Let `k` be an algebraic closure of `ZMod p`.  The Witt ring `W(k)` is the
integer ring of the completed maximal-unramified coefficient field used in
the changed-uniformizer construction. Mathlib's `WittVector.frobeniusRotation` supplies the
actual unit `ε ∈ W(k)ˣ` satisfying

`φ(ε) = ε u`

for every p-adic integer unit `u`.  This is precisely the linear-coefficient
equation for the semilinear changed-uniformizer intertwiner.

No second p-adic integer ring or Frobenius is introduced here: the base map
uses mathlib's equivalence `W(ZMod p) ≃+* ℤ_[p]`, and `φ` is
`WittVector.frobenius`.
-/

noncomputable section

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp

/-- The chosen valuation ring of `ℚ_[p]` maps canonically into the
completed-unramified Witt ring. -/
noncomputable def padicValuationSubringToCompletedUnramifiedWittRing
    (p : ℕ) [Fact p.Prime] :
    (padicLocalField p).valuationSubring →+*
      padicCompletedUnramifiedWittRing p := by
  change (padicDVRValuation p).valuationSubring →+*
    padicCompletedUnramifiedWittRing p
  exact
    (padicIntToCompletedUnramifiedWittRing p).comp
      (padicIntEquivValuationSubring p).symm.toRingHom

/-- The canonical map from the valuation ring of `ℚ_[p]` sends its standard
uniformizer to the Witt-vector prime. -/
@[simp]
theorem padicValuationSubringToCompletedUnramifiedWittRing_uniformizer
    (p : ℕ) [Fact p.Prime] :
    padicValuationSubringToCompletedUnramifiedWittRing p
        (padicIntEquivValuationSubring p (p : ℤ_[p])) =
      (p : padicCompletedUnramifiedWittRing p) := by
  change
    padicIntToCompletedUnramifiedWittRing p
        ((padicIntEquivValuationSubring p).symm
          (padicIntEquivValuationSubring p (p : ℤ_[p]))) =
      (p : padicCompletedUnramifiedWittRing p)
  rw [RingEquiv.symm_apply_apply, map_natCast]

end LubinTate

end
end


