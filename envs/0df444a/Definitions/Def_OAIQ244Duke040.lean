-- Prove2me | Definitions.Def_OAIQ244Duke040
-- name    : OAIQ244Duke040
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:43:18.504185+00:00
-- url     : https://prove2.me/theorems/d76e7af9-3ec7-4964-97bb-efe52ce17ed8
-- title:
--   Definitions bundle OAIQ244Duke040 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 71 declarations of OpenAI's Lean: 15 definitions and 56 theorems. The definitions and types are `GlobalClassFieldTheory.ClassFieldAxiom.realInfinitePositiveQuotientEquivSign`, `LocalClassFieldTheory.completionProductUnitsEquivLocalPlaceBlock`, `LocalClassFieldTheory.infinitePlaceAbsoluteValueExtension`, `LocalClassFieldTheory.integerUnitsModPrincipalUnitsToSubgroupQuotient`, `LocalClassFieldTheory.integerUnitsPrincipalUnitsQuotientMap`, `LocalClassFieldTheory.localTensorDetNorm`, `LocalClassFieldTheory.localTensorNormSubgroup`, `LocalClassFieldTheory.localTensorUnitsEquivChosenCoordinates`, `RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF`, `cyclicPrimeSubextensionDecompositionGroup`, `finitePlaceDecompositionGroupInQuotient`, `finitePlaceLocalDegree`, `finitePlaceLocalTensorAlgEquiv`, `finitePlaceLocalTensorUnitsAction`, `finitePlaceLocalTensorUnitsEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Adele_FinitePlaceTensorBlock`, `AlgebraicNumberTheory_Galois_CyclicPrimeSubextension`, `AlgebraicNumberTheory_Idele_Extension_LocalNorm`, `AlgebraicNumberTheory_Idele_NormApproximation_InfinitePlaces`, `AlgebraicNumberTheory_Idele_Relative_FinitePlaceTensorNorm`, `AlgebraicNumberTheory_Ramification_Splitting_FinitePlace`, `GlobalClassFieldTheory_ClassFieldAxiom_IdeleClassPowerLocalUnitQuotient_ArchimedeanPowerIndex`, `GlobalClassFieldTheory_Cohomology_CyclicPrimePowerFullDecomposition`, `KummerTheory_Concrete_SUnitPreparation_FullSUnitKummerExtension`, `LocalClassFieldTheory_ClassFormation_ArchimedeanNormQuotient`, `LocalClassFieldTheory_ClassFormation_LocalBlocks_Tensor`, `LocalClassFieldTheory_ClassFormation_LocalBlocks_TensorNorm`, `LocalClassFieldTheory_ClassFormation_LocalizedCompletionCohomology_Algebra`, `LocalClassFieldTheory_ClassFormation_NormalBasis`, `LocalClassFieldTheory_ClassFormation_NormalBasisCohomology`, `LocalClassFieldTheory_ClassFormation_NormalBasisFiniteQuotient`, `LocalClassFieldTheory_ClassFormation_NormalBasisGradedLifting`, `LocalClassFieldTheory_ClassFormation_NormalBasisInfiniteProduct`, `LocalClassFieldTheory_ClassFormation_NormalBasisRecursiveLifting`, `LocalClassFieldTheory_ClassFormation_PrincipalUnitGraded`, `LocalClassFieldTheory_ClassFormation_ValueGroupCohomology`, `LocalClassFieldTheory_Finite_LocalReciprocity_FiniteResidueValuationComparison`, `LocalClassFieldTheory_Finite_LocalReciprocity_SeparableUnitsNorm`, `LocalClassFieldTheory_Finite_Unramified_Cohomology`, `LocalField_DiscreteValuationField_PrincipalUnitPadicAction_FiniteQuotientPadicModule`, `LocalField_DiscreteValuationField_RamificationIdeal`, `LocalField_DiscreteValuationField_RamificationInvariants`, `LocalField_NonarchimedeanLocalField_NormQuotient`, `LocalField_NonarchimedeanLocalField_PrincipalUnitQuotients`, `Ramification_GaloisValuation_AbsoluteGalois_AbsoluteRamification`, `Valuation_DiscreteValuationField_FiniteExtension_Uniqueness`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke025`, `OAIQ244Duke026`, `OAIQ244Duke027`, `OAIQ244Duke028`, `OAIQ244Duke029`, `OAIQ244Duke030` and `OAIQ244Duke031` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke047`, `OAIQ244Duke048`, `OAIQ244Duke049`, `OAIQ244Duke050`, `OAIQ244Duke051` and `OAIQ244Duke052`.
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
import Mathlib.RingTheory.LocalRing.Module
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
import Definitions.Def_OAIQ244Duke025
import Definitions.Def_OAIQ244Duke026
import Definitions.Def_OAIQ244Duke027
import Definitions.Def_OAIQ244Duke028
import Definitions.Def_OAIQ244Duke029
import Definitions.Def_OAIQ244Duke030
import Definitions.Def_OAIQ244Duke031

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_PrincipalUnitQuotients
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelConcreteEquiv_mk _root_.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelLift_mk _root_.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelMk_eq_iff_div_mem _root_.CyclicCohomology.principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_mk _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSequenceAsPrincipalUnits_val _root_.LocalFieldTheory.integerUnitsModPrincipalUnitsConcreteEquiv_mk _root_.LocalFieldTheory.integerUnitsModPrincipalUnitsLift_mk _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.principalUnitsMapOfUnramifiedValuation_apply _root_.LocalFieldTheory.principalUnitsSuccQuotAddEquivResidueOfIrreducible_symm_residue _root_.LocalFieldTheory.principalUnitsSuccQuotMapOfUnramifiedValuation_mk _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
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

/-- Additive form of the correction-product tail control. This is the form
needed by the additive uniformity on the valuation integer ring. -/
theorem principalUnitsCorrectionProduct_sub_mem
    (K : Type u) [Field K] [ValuativeRel K] (n m d : Nat)
    (z : ∀ d : Nat, principalUnits K (n + d)) :
    ((principalUnitsCorrectionProduct K n z (m + d) : 𝒪[K]ˣ) : 𝒪[K]) -
        ((principalUnitsCorrectionProduct K n z m : 𝒪[K]ˣ) : 𝒪[K]) ∈
      (𝓂[K] ^ (n + m) : Ideal 𝒪[K]) := by
  let a : 𝒪[K]ˣ := principalUnitsCorrectionProduct K n z (m + d)
  let b : 𝒪[K]ˣ := principalUnitsCorrectionProduct K n z m
  have htail : (((a / b : 𝒪[K]ˣ) : 𝒪[K]) - 1) ∈
      (𝓂[K] ^ (n + m) : Ideal 𝒪[K]) := by
    simpa [a, b] using principalUnitsCorrectionProduct_div_sub_one_mem K n m d z
  rw [unit_sub_eq_mul_div_sub_one K a b]
  exact Ideal.mul_mem_left _ _ htail

/-- Uniform-tail algebraic input: two sufficiently late correction products
are congruent modulo any fixed earlier level of the maximal-ideal filtration. -/
theorem principalUnitsCorrectionProduct_sub_mem_of_le
    (K : Type u) [Field K] [ValuativeRel K] (n N i j : Nat)
    (z : ∀ d : Nat, principalUnits K (n + d))
    (hi : N ≤ i) (hj : N ≤ j) :
    ((principalUnitsCorrectionProduct K n z i : 𝒪[K]ˣ) : 𝒪[K]) -
        ((principalUnitsCorrectionProduct K n z j : 𝒪[K]ˣ) : 𝒪[K]) ∈
      (𝓂[K] ^ (n + N) : Ideal 𝒪[K]) := by
  by_cases hji : j ≤ i
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hji
    exact Ideal.pow_le_pow_right (Nat.add_le_add_left hj n)
      (principalUnitsCorrectionProduct_sub_mem K n j d z)
  · have hij : i ≤ j := Nat.le_of_not_ge hji
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
    have hdiff :
        ((principalUnitsCorrectionProduct K n z (i + d) : 𝒪[K]ˣ) : 𝒪[K]) -
            ((principalUnitsCorrectionProduct K n z i : 𝒪[K]ˣ) : 𝒪[K]) ∈
          (𝓂[K] ^ (n + N) : Ideal 𝒪[K]) := by
      exact Ideal.pow_le_pow_right (Nat.add_le_add_left hi n)
        (principalUnitsCorrectionProduct_sub_mem K n i d z)
    have hEq :
        ((principalUnitsCorrectionProduct K n z i : 𝒪[K]ˣ) : 𝒪[K]) -
            ((principalUnitsCorrectionProduct K n z (i + d) : 𝒪[K]ˣ) : 𝒪[K]) =
          -(((principalUnitsCorrectionProduct K n z (i + d) : 𝒪[K]ˣ) : 𝒪[K]) -
            ((principalUnitsCorrectionProduct K n z i : 𝒪[K]ˣ) : 𝒪[K])) := by
      ring
    rw [hEq]
    exact (𝓂[K] ^ (n + N) : Ideal 𝒪[K]).neg_mem hdiff

/-- The finite correction products form a Cauchy sequence in the valuation
integer ring. This is the first complete-side output of the tail estimates. -/
theorem principalUnitsCorrectionProduct_cauchySeq
    (K : Type u) [Field K] [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K]
    [IsNonarchimedeanLocalField K] (n : Nat)
    (z : ∀ d : Nat, principalUnits K (n + d)) :
    CauchySeq fun d : Nat =>
      ((principalUnitsCorrectionProduct K n z d : 𝒪[K]ˣ) : 𝒪[K]) := by
  rw [cauchySeq_iff]
  intro V hV
  rw [uniformity_eq_comap_nhds_zero 𝒪[K]] at hV
  rw [mem_comap] at hV
  rcases hV with ⟨s, hs, hsub⟩
  rcases eventually_maximalIdeal_pow_subset_nhds_zero K s hs with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro i hi j hj
  apply hsub
  exact hN (n + N) (Nat.le_add_left N n)
    (principalUnitsCorrectionProduct_sub_mem_of_le K n N j i z hj hi)

/-- Completeness of the valuation integer ring gives a limit for the finite
correction products. The statement deliberately stops at an `𝒪[K]`-valued
limit; proving that the limit is a unit and remains in the intended
principal-unit level is the next frontier. -/
theorem exists_tendsto_principalUnitsCorrectionProduct
    (K : Type u) [Field K] [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K]
    [IsNonarchimedeanLocalField K] (n : Nat)
    (z : ∀ d : Nat, principalUnits K (n + d)) :
    ∃ x : 𝒪[K], Tendsto
      (fun d : Nat => ((principalUnitsCorrectionProduct K n z d : 𝒪[K]ˣ) : 𝒪[K]))
      atTop (nhds x) :=
  cauchySeq_tendsto_of_complete
    (principalUnitsCorrectionProduct_cauchySeq K n z)

/-- Any limit of the correction-product sequence still satisfies the defining
congruence of `U^n`, viewed inside the valuation integer ring. -/
theorem principalUnitsCorrectionProduct_limit_sub_one_mem
    (K : Type u) [Field K] [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K]
    [IsNonarchimedeanLocalField K] (n : Nat)
    (z : ∀ d : Nat, principalUnits K (n + d)) (x : 𝒪[K])
    (hx : Tendsto
      (fun d : Nat => ((principalUnitsCorrectionProduct K n z d : 𝒪[K]ˣ) : 𝒪[K]))
      atTop (nhds x)) :
    x - 1 ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) := by
  have hclosed := isClosed_maximalIdeal_pow K n
  refine hclosed.mem_of_tendsto
    (f := fun d : Nat =>
      ((principalUnitsCorrectionProduct K n z d : 𝒪[K]ˣ) : 𝒪[K]) - 1)
    (b := (atTop : Filter Nat)) (x := x - 1) ?_ ?_
  · exact hx.sub tendsto_const_nhds
  · exact Eventually.of_forall fun d =>
      (mem_principalUnits_iff K (principalUnitsCorrectionProduct K n z d) n).1
        (principalUnitsCorrectionProduct_mem K n z d)

/-- Complete-side output with the retained principal-unit congruence: the
finite correction products have an `𝒪[K]`-valued limit whose difference from
`1` lies in `𝓂^n`. -/
theorem exists_tendsto_principalUnitsCorrectionProduct_sub_one_mem
    (K : Type u) [Field K] [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K]
    [IsNonarchimedeanLocalField K] (n : Nat)
    (z : ∀ d : Nat, principalUnits K (n + d)) :
    ∃ x : 𝒪[K], Tendsto
        (fun d : Nat => ((principalUnitsCorrectionProduct K n z d : 𝒪[K]ˣ) : 𝒪[K]))
        atTop (nhds x) ∧
      x - 1 ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) := by
  rcases exists_tendsto_principalUnitsCorrectionProduct K n z with ⟨x, hx⟩
  exact ⟨x, hx, principalUnitsCorrectionProduct_limit_sub_one_mem K n z x hx⟩

/-- For `n ≥ 1`, the complete limit of finite correction products can be
viewed as an element of the principal-unit subgroup `U^n`. -/
theorem exists_tendsto_principalUnitsCorrectionProduct_principalUnit
    (K : Type u) [Field K] [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K]
    [IsNonarchimedeanLocalField K] (n : Nat) (hn : 1 ≤ n)
    (z : ∀ d : Nat, principalUnits K (n + d)) :
    ∃ x : principalUnits K n, Tendsto
      (fun d : Nat => ((principalUnitsCorrectionProduct K n z d : 𝒪[K]ˣ) : 𝒪[K]))
      atTop (nhds (((x : principalUnits K n) : 𝒪[K]ˣ) : 𝒪[K])) := by
  rcases exists_tendsto_principalUnitsCorrectionProduct_sub_one_mem K n z with
    ⟨x, hx, hmem⟩
  let u : principalUnits K n :=
    principalUnitOneAddOfMemPowSubgroup K hn (x - 1) hmem
  refine ⟨u, ?_⟩
  have huval : (((u : principalUnits K n) : 𝒪[K]ˣ) : 𝒪[K]) = x := by
    change ((principalUnitOneAddOfMemPow K hn (x - 1) hmem : 𝒪[K]ˣ) : 𝒪[K]) = x
    rw [principalUnitOneAddOfMemPow_val]
    ring
  simpa [huval] using hx

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_NormQuotient
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-!
# Quotients by local norm subgroups

Constructs `Kˣ/N(Lˣ)`, its universal maps and comparison equivalences, and
relates its finite cardinality to the index of the norm subgroup.
-/

namespace LocalFieldTheory

noncomputable section

universe u v

/-- The kernel of the norm-class homomorphism is the local norm subgroup. -/
theorem normClass_ker (K L : Type u) [Field K] [Field L] [Algebra K L] :
    MonoidHom.ker (normClass K L) = localNormSubgroup K L :=
  by
    let N := localNormSubgroup K L
    exact QuotientGroup.ker_mk' (N := N)

/-- Membership in the kernel of the norm-class map is equivalent to membership in the local norm
subgroup. -/
theorem normClass_mem_ker_iff (K L : Type u) [Field K] [Field L]
    [Algebra K L] (x : Kˣ) :
    x ∈ MonoidHom.ker (normClass K L) ↔ x ∈ localNormSubgroup K L := by
  rw [normClass_ker K L]

/-- A norm class is one exactly when its representative is a local norm. -/
theorem normClass_eq_one_iff_mem (K L : Type u) [Field K] [Field L]
    [Algebra K L] (x : Kˣ) :
    normClass K L x = 1 ↔ x ∈ localNormSubgroup K L := by
  rw [← normClass_mem_ker_iff K L x]
  rfl

/-! ### Surjectivity and equality refinements for norm quotients -/

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_FiniteExtension_Uniqueness
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotCommGroup _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-! Provides the public declarations in the `ValuationTheory.DiscreteValuationField.FiniteExtension.Uniqueness` Lean module. -/

namespace ValuationTheory

noncomputable section

universe u v w x y

namespace DiscreteValuationField
namespace ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L] [FiniteDimensional K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

/-- The canonical ramification index times residue degree is the field degree for a
finite separable extension, with no separate integral-closure certificate. -/
theorem ramificationIndex_mul_residueDegree_eq_degree_of_finite_separable

    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    (ValuedExtension.ramificationIndex base.toDVF target.toDVF) * (ValuedExtension.residueDegree base.toDVF target.toDVF) = (ValuedExtension.degree base.toDVF target.toDVF) := by
  let : IsIntegralClosure target.valuationSubring base.valuationSubring L :=
    (target_valuationSubring_isIntegralClosure_of_finite_separable base target)
  exact (ramificationIndex_mul_residueDegree_eq_degree_of_isIntegralClosure base target)

end ValuedExtension
end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_ValueGroupCohomology
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
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

/-- Value-group factor for the local class-field axiom: `H⁻¹(G,ℤ)` is trivial. -/
theorem galoisGroupValueGroup_herbrandHMinusOne_card_eq_one
    (σ : Gal(L / K)) :
    letI := galoisGroupValueGroupMulDistribMulAction K L
    letI := galoisGroupValueGroupHerbrandHMinusOneFinite K L σ
    Nat.card
      (HerbrandHMinusOne (Gal(L / K)) (Multiplicative Int) σ) = 1 := by
  let := galoisGroupValueGroupMulDistribMulAction K L
  have : Subsingleton
      (normKernelSubgroup (Gal(L / K)) (Multiplicative Int)) := by
    rw [galoisGroupValueGroup_normKernelSubgroup_eq_bot K L]
    infer_instance
  let : Subsingleton
      (HerbrandHMinusOne (Gal(L / K)) (Multiplicative Int) σ) :=
    ⟨fun q =>
      HerbrandHMinusOne.inductionOn σ
        (motive := fun q => ∀ r, q = r) q fun x r =>
          HerbrandHMinusOne.inductionOn σ
            (motive := fun r => HerbrandHMinusOne.mk σ x = r) r fun y =>
              congrArg (fun z => HerbrandHMinusOne.mk σ z)
                (Subsingleton.elim x y)⟩
  exact Nat.card_unique

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_NormalBasisFiniteQuotient
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

/-- Since the normal-basis lattices `π_K^n M` are open for high `n`, each
corresponding `V^n` contains an ordinary principal-unit subgroup. -/
theorem exists_principalUnits_le_chosenNormalBasisPrincipalUnitSet :
    ∃ c : Nat, ∀ n : Nat, c ≤ n →
      ∃ m : Nat, (principalUnits L m : Set 𝒪[L]ˣ) ⊆
        chosenNormalBasisPrincipalUnitSet K L n := by
  rcases exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_mem_nhds_zero
      (K := K) (L := L) with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro n hcn
  let S : Set L :=
    (chosenBaseUniformizerPowSubmodule K L n
      (chosenNormalBasisIntegerLattice K L) : Set L)
  have hS : S ∈ nhds (0 : L) := hc n hcn
  have hSO : {x : 𝒪[L] | (x : L) ∈ S} ∈ nhds (0 : 𝒪[L]) := by
    exact continuous_subtype_val.continuousAt hS
  rcases exists_maximalIdeal_pow_subset_nhds_zero L
      {x : 𝒪[L] | (x : L) ∈ S} hSO with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  intro a ha
  rw [mem_chosenNormalBasisPrincipalUnitSet_iff]
  change
    (((((a : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L)) ∈ S
  exact hm ((mem_principalUnits_iff L a m).1 ha)

/-- The canonical map from `𝒪_Lˣ/U_L^m` onto `𝒪_Lˣ/V` whenever
`U_L^m ≤ V`. -/
def integerUnitsModPrincipalUnitsToSubgroupQuotient
    (m : Nat) (V : Subgroup 𝒪[L]ˣ) (h : principalUnits L m ≤ V) :
    IntegerUnitsModPrincipalUnitsAtLevel L m →* (𝒪[L]ˣ ⧸ V) :=
  integerUnitsModPrincipalUnitsAtLevelLift m (QuotientGroup.mk' V)
    (by
      intro a ha
      rw [MonoidHom.mem_ker]
      change (QuotientGroup.mk a : 𝒪[L]ˣ ⧸ V) = 1
      exact (QuotientGroup.eq_one_iff a).2 (h ha))

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
/-- States the theorem `integerUnitsModPrincipalUnitsToSubgroupQuotient_surjective`. -/
theorem integerUnitsModPrincipalUnitsToSubgroupQuotient_surjective
    (m : Nat) (V : Subgroup 𝒪[L]ˣ) (h : principalUnits L m ≤ V) :
    Function.Surjective
      (integerUnitsModPrincipalUnitsToSubgroupQuotient L m V h) := by
  intro q
  refine Quotient.inductionOn' q ?_
  intro a
  refine ⟨integerUnitsModPrincipalUnitsAtLevelMk L m a, ?_⟩
  rfl

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_NormalBasisInfiniteProduct
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelConcreteEquiv_mk _root_.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelLift_mk _root_.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelMk_eq_iff_div_mem _root_.CyclicCohomology.principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_mk _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.chosenNormalBasisIntegerLatticeBasis_apply _root_.LocalClassFieldTheory.chosenNormalBasisIntegerLatticeMulPowLinearEquiv_apply _root_.LocalClassFieldTheory.chosenNormalBasisLatticeSuccQuotRightRegularAddEquiv_mk_mulPow _root_.LocalClassFieldTheory.chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv_galoisGroup _root_.LocalClassFieldTheory.chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv_mk_mulPow _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction_smul _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroup_sigmaMinusOne_coe _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroup_tateNorm_coe _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSuccQuotMulDistribMulAction_smul_mk _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSuccQuotMulEquivLatticeSuccQuot_mk _root_.LocalClassFieldTheory.galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv_apply_coe _root_.LocalClassFieldTheory.galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv_mul_apply _root_.LocalClassFieldTheory.galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv_one_apply _root_.LocalClassFieldTheory.galoisGroupChosenNormalBasisIntegerLatticeQuotLinearEquiv_mk _root_.LocalClassFieldTheory.galoisGroupChosenNormalBasisLatticeSuccQuotAddEquiv_mk_mulPow _root_.LocalClassFieldTheory.galoisGroupChosenNormalBasisLatticeSuccQuotDistribMulAction_smul_mk_mulPow _root_.LocalClassFieldTheory.mem_chosenNormalBasisIntegerLatticeUniformizerSubmodule_iff _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.principalUnitsMapOfUnramifiedValuation_apply _root_.LocalFieldTheory.principalUnitsSuccQuotMapOfUnramifiedValuation_mk _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
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

/-- Once the normal-basis lattice has entered `𝒪_L`, a sequence whose
`i`-th term lies in `V^(n+i)` converges to `1` in `𝒪_L`. -/
theorem tendsto_chosenNormalBasisPrincipalUnitSequence_one_of_lattice_bound
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    {b n : Nat}
    (hb : chosenBaseUniformizerPowSubmodule K L b
        (chosenNormalBasisIntegerLattice K L) ≤
      integerRingFieldSubmodule K L)
    (hbn : b + 1 ≤ n) (z : Nat → 𝒪[L]ˣ)
    (hz : ∀ i : Nat, z i ∈ chosenNormalBasisPrincipalUnitSet K L (n + i)) :
    Tendsto (fun i : Nat => ((z i : 𝒪[L]ˣ) : 𝒪[L])) atTop
      (nhds (1 : 𝒪[L])) := by
  have hsub : Tendsto
      (fun i : Nat => ((z i : 𝒪[L]ˣ) : 𝒪[L]) - 1) atTop
      (nhds (0 : 𝒪[L])) := by
    rw [tendsto_def]
    intro s hs
    rcases eventually_maximalIdeal_pow_subset_nhds_zero L s hs with ⟨N, hN⟩
    filter_upwards [eventually_ge_atTop N] with i hi
    apply hN (1 + i)
    · exact le_trans hi (Nat.le_add_left i 1)
    · exact (mem_principalUnits_iff L (z i) (1 + i)).1
        (chosenNormalBasisPrincipalUnitSet_mem_principalUnits_succ_of_lattice_bound
          (K := K) (L := L) hb hbn (hz i))
  simpa using hsub.const_add (1 : 𝒪[L])

/-- Completeness of `𝒪_L` gives a unit-valued limit for the normal-basis
partial products once the lattice sequence has been embedded in
`U_L^(i+1)`. -/
theorem exists_tendsto_chosenNormalBasisPrincipalUnitCorrectionProduct_principalUnit
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    {b n : Nat}
    (hb : chosenBaseUniformizerPowSubmodule K L b
        (chosenNormalBasisIntegerLattice K L) ≤
      integerRingFieldSubmodule K L)
    (hbn : b + 1 ≤ n) (z : Nat → 𝒪[L]ˣ)
    (hz : ∀ i : Nat, z i ∈ chosenNormalBasisPrincipalUnitSet K L (n + i)) :
    ∃ x : principalUnits L 1,
      Tendsto
        (fun d : Nat =>
          ((chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d : 𝒪[L]ˣ) :
            𝒪[L]))
        atTop (nhds (((x : principalUnits L 1) : 𝒪[L]ˣ) : 𝒪[L])) := by
  let zU : ∀ i : Nat, principalUnits L (1 + i) :=
    chosenNormalBasisPrincipalUnitSequenceAsPrincipalUnits K L hb hbn z hz
  rcases exists_tendsto_principalUnitsCorrectionProduct_principalUnit
      L 1 (by rfl) zU with ⟨x, hx⟩
  refine ⟨x, hx.congr' (Eventually.of_forall ?_)⟩
  intro d
  exact congrArg (fun q : 𝒪[L]ˣ => (q : 𝒪[L]))
    (chosenNormalBasisPrincipalUnitCorrectionProduct_eq_principalUnitsCorrectionProduct
      (K := K) (L := L) hb hbn z hz d).symm

/-- Infinite-product boundary for the local class-field axiom: for all sufficiently large
`n`, every sequence `z_i ∈ V^(n+i)` has partial products converging to an
actual unit of `V^n`. -/
theorem exists_tendsto_chosenNormalBasisPrincipalUnitCorrectionProduct
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    [Module.Finite 𝒪[K] 𝒪[L]] :
    ∃ c : Nat, ∀ n : Nat, c ≤ n →
      ∀ z : Nat → 𝒪[L]ˣ,
        (∀ i : Nat, z i ∈ chosenNormalBasisPrincipalUnitSet K L (n + i)) →
          ∃ x : 𝒪[L]ˣ,
            Tendsto
                (fun d : Nat =>
                  ((chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d :
                    𝒪[L]ˣ) : 𝒪[L]))
                atTop (nhds ((x : 𝒪[L]ˣ) : 𝒪[L])) ∧
              x ∈ chosenNormalBasisPrincipalUnitSet K L n := by
  rcases exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_le_integerRingFieldSubmodule
      (K := K) (L := L) with ⟨b, hb⟩
  rcases exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_mul_mul_mem_self
      (K := K) (L := L) with ⟨cMul, hcMul⟩
  rcases exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_isClosed
      (K := K) (L := L) with ⟨cClosed, hcClosed⟩
  refine ⟨max (b + 1) (max cMul cClosed), ?_⟩
  intro n hn z hz
  have hbn : b + 1 ≤ n :=
    le_trans (le_max_left (b + 1) (max cMul cClosed)) hn
  have hrest : max cMul cClosed ≤ max (b + 1) (max cMul cClosed) :=
    le_max_right (b + 1) (max cMul cClosed)
  have hcMuln : cMul ≤ n :=
    le_trans (le_trans (le_max_left cMul cClosed) hrest) hn
  have hcClosedn : cClosed ≤ n :=
    le_trans (le_trans (le_max_right cMul cClosed) hrest) hn
  let hmulLattice := hcMul n hcMuln
  have hmul : ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
      ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
        u * v ∈ chosenNormalBasisPrincipalUnitSet K L n := by
    intro u hu v hv
    exact chosenNormalBasisPrincipalUnitSet_mul_mem
      (K := K) (L := L) hmulLattice hu hv
  rcases exists_tendsto_chosenNormalBasisPrincipalUnitCorrectionProduct_principalUnit
      (K := K) (L := L) hb hbn z hz with ⟨x, hx⟩
  let xu : 𝒪[L]ˣ := (x : principalUnits L 1)
  refine ⟨xu, ?_, ?_⟩
  · exact hx
  · exact chosenNormalBasisPrincipalUnitCorrectionProduct_limit_mem
      (K := K) (L := L) (hcClosed n hcClosedn) hmul z hz xu hx

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_NormalBasis
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-! Provides the public declarations in the `LocalClassFieldTheory.ClassFormation.NormalBasis` Lean module. -/

namespace LocalClassFieldTheory

open LocalFieldTheory

open CyclicCohomology

noncomputable section

universe u

open scoped ValuativeRel

variable (K L : Type u) [Field K] [ValuativeRel K] [Field L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

section GradedCoordinates

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-! ### The actual `Gal(L / K)` action and right-regular equivariance -/

/-- Cyclic Herbrand `H⁻¹` vanishes on every additive normal-basis lattice
graded piece. -/
theorem chosenNormalBasisLatticeSuccQuot_herbrandHMinusOne_subsingleton
    (n : Nat) (τ : Gal(L / K))
    (hgen : ∀ g : Gal(L / K), g ∈ Subgroup.zpowers τ) :
    letI := galoisGroupChosenNormalBasisLatticeSuccQuotDistribMulAction K L n
    letI :=
      CyclicCohomology.ProfiniteCohomology.Herbrand.multiplicativeMulDistribMulActionOfDistribMulAction
        Gal(L / K) (chosenNormalBasisLatticeSuccQuot K L n)
    Subsingleton (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandHMinusOne
      Gal(L / K) (Multiplicative (chosenNormalBasisLatticeSuccQuot K L n)) τ) := by
  let := galoisGroupChosenNormalBasisLatticeSuccQuotDistribMulAction K L n
  exact
    CyclicCohomology.ProfiniteCohomology.Herbrand.herbrandHMinusOne_subsingleton_of_addEquiv_rightRegularFunction
      (G := Gal(L / K)) (M := chosenNormalBasisLatticeSuccQuot K L n) (D := 𝓀[K])
      τ hgen (chosenNormalBasisLatticeSuccQuotRightRegularAddEquiv K L n)
      (chosenNormalBasisLatticeSuccQuotRightRegularAddEquiv_commutes K L n)

end GradedCoordinates

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_PrincipalUnitGraded
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-! Provides the public declarations in the `LocalClassFieldTheory.ClassFormation.PrincipalUnitGraded` Lean module. -/

namespace LocalClassFieldTheory

open CyclicCohomology LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel
open IsNonarchimedeanLocalField

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

/-- Existential high-degree boundary used in the proof of the local class-field-axiom theorem:
for every sufficiently large `n`, the actual successive principal-unit
quotient is isomorphic to the corresponding normal-basis lattice quotient. -/
theorem exists_chosenNormalBasisPrincipalUnitSuccQuotMulEquivLatticeSuccQuot
    [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Module.Finite 𝒪[K] 𝒪[L]] :
    ∃ c : Nat, ∀ n : Nat, c ≤ n →
      ∃ Vn Vsucc : Subgroup 𝒪[L]ˣ,
        ∃ hV : Vsucc ≤ Vn,
          ∃ hVn : (Vn : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n,
            (Vsucc : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L (n + 1) ∧
              ∃ Φ : chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV ≃*
                  Multiplicative (chosenNormalBasisLatticeSuccQuot K L n),
                Vn ≤ principalUnits L 1 ∧
                  ∀ u : Vn,
                    Φ (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV u) =
                      Multiplicative.ofAdd
                        (chosenNormalBasisPrincipalUnitLatticeClass K L n
                          (u : 𝒪[L]ˣ) (by exact hVn ▸ u.2)) := by
  rcases exists_chosenNormalBasisPrincipalUnitSubgroupSuccPair
      (K := K) (L := L) with ⟨c₁, hc₁⟩
  rcases exists_chosenNormalBasisPrincipalUnitSet_mul_error_mem_succ
      (K := K) (L := L) with ⟨c₂, hc₂⟩
  rcases exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_le_maximalIdeal_and_mul_closed
      (K := K) (L := L) with ⟨c₃, hc₃⟩
  refine ⟨max c₁ (max c₂ c₃), ?_⟩
  intro n hn
  have hc₁n : c₁ ≤ n :=
    le_trans (le_max_left c₁ (max c₂ c₃)) hn
  have hcrest : max c₂ c₃ ≤ max c₁ (max c₂ c₃) :=
    le_max_right c₁ (max c₂ c₃)
  have hc₂n : c₂ ≤ n :=
    le_trans (le_trans (le_max_left c₂ c₃) hcrest) hn
  have hc₃n : c₃ ≤ n :=
    le_trans (le_trans (le_max_right c₂ c₃) hcrest) hn
  rcases hc₁ n hc₁n with ⟨Vn, Vsucc, hVn, hVsucc, hV, hVnle⟩
  let hmul_error := hc₂ n hc₂n
  let hle := (hc₃ n hc₃n).1
  let Φ : chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV ≃*
      Multiplicative (chosenNormalBasisLatticeSuccQuot K L n) :=
    chosenNormalBasisPrincipalUnitSuccQuotMulEquivLatticeSuccQuot
      K L hVn hVsucc hV hmul_error hle
  refine ⟨Vn, Vsucc, hV, hVn, hVsucc, Φ, hVnle, ?_⟩
  intro u
  rfl

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_NormalBasisGradedLifting
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.HilbertRamification.Dedekind.inertiaSubgroupOfDecomposition_normal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.CyclicCohomology.fixedPiEquiv_apply_coe _root_.CyclicCohomology.herbrandH0EquivariantMulEquiv_mk _root_.CyclicCohomology.inducedFixedEquiv_apply_coe _root_.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelConcreteEquiv_mk _root_.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelLift_mk _root_.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelMk_eq_iff_div_mem _root_.CyclicCohomology.normKernelPiEquiv_apply_coe _root_.CyclicCohomology.principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_mk _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSequenceAsPrincipalUnits_val _root_.LocalClassFieldTheory.fixedUnitToInvariantsNormQuotientMonoidHom_apply _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.principalUnitsMapOfUnramifiedValuation_apply _root_.LocalFieldTheory.principalUnitsSuccQuotMapOfUnramifiedValuation_mk _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RelativeIdeleGroup.Cohomology.baseIdeleClassEquivFixed_coe _root_.RelativeIdeleGroup.Cohomology.baseIdeleClassToFixed_coe _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-! Provides the public declarations in the `LocalClassFieldTheory.ClassFormation.NormalBasisGradedLifting` Lean module. -/

namespace LocalClassFieldTheory

open LocalFieldTheory

open CyclicCohomology

noncomputable section

universe u

open scoped BigOperators ValuativeRel
open IsNonarchimedeanLocalField
open CyclicCohomology.ProfiniteCohomology.Herbrand

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L]

/-- One-step `H⁰` lifting: sufficiently deep fixed units are
a norm from the same level times a fixed unit one level deeper. -/
theorem exists_chosenNormalBasisPrincipalUnit_h0_oneStep_lifting
    [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Module.Finite 𝒪[K] 𝒪[L]] :
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    ∃ c : Nat, ∀ k : Nat, c ≤ k → ∀ a : 𝒪[L]ˣ,
      a ∈ chosenNormalBasisPrincipalUnitSet K L k →
      (∀ sigma : Gal(L / K), sigma • a = a) →
      ∃ b a' : 𝒪[L]ˣ,
        b ∈ chosenNormalBasisPrincipalUnitSet K L k ∧
        a' ∈ chosenNormalBasisPrincipalUnitSet K L (k + 1) ∧
        (∀ sigma : Gal(L / K), sigma • a' = a') ∧
        a = tateNorm (Gal(L / K)) 𝒪[L]ˣ b * a' := by
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  rcases exists_chosenNormalBasisPrincipalUnitSuccQuotMulEquivLatticeSuccQuot
      (K := K) (L := L) with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro k hck a ha hfixed
  rcases hc k hck with
    ⟨Vn, Vsucc, hV, hVn, hVsucc, Phi, _hVnle, hPhi⟩
  let := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction
    K L k Vn hVn
  let := chosenNormalBasisPrincipalUnitSuccQuotMulDistribMulAction
    K L k hV hVn hVsucc
  let := galoisGroupChosenNormalBasisLatticeSuccQuotDistribMulAction K L k
  let := multiplicativeMulDistribMulActionOfDistribMulAction
    (Gal(L / K)) (chosenNormalBasisLatticeSuccQuot K L k)
  let av : Vn := ⟨a, by
    change a ∈ (Vn : Set 𝒪[L]ˣ)
    rw [hVn]
    exact ha⟩
  let q : Multiplicative (chosenNormalBasisLatticeSuccQuot K L k) :=
    Phi (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV av)
  have hqfixed : ∀ sigma : Gal(L / K), sigma • q = q := by
    intro sigma
    dsimp [q]
    calc
      sigma • Phi (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV av) =
          Phi (sigma • chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV av) :=
        (chosenNormalBasisPrincipalUnitSuccQuotMulEquiv_galoisGroup
          (K := K) (L := L) k hV hVn hVsucc Phi hPhi sigma _).symm
      _ = Phi (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV (sigma • av)) := by
        rw [chosenNormalBasisPrincipalUnitSuccQuotMulDistribMulAction_smul_mk]
      _ = Phi (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV av) := by
        congr 2
        apply Subtype.ext
        exact hfixed sigma
  let qfixed : fixedSubgroup (Gal(L / K))
      (Multiplicative (chosenNormalBasisLatticeSuccQuot K L k)) :=
    ⟨q, hqfixed⟩
  have hH0 := chosenNormalBasisLatticeSuccQuot_herbrandH0_subsingleton K L k
  have hqone :
      QuotientGroup.mk'
          ((tateNormSubgroup (Gal(L / K))
            (Multiplicative (chosenNormalBasisLatticeSuccQuot K L k))).subgroupOf
              (fixedSubgroup (Gal(L / K))
                (Multiplicative (chosenNormalBasisLatticeSuccQuot K L k))))
          qfixed = 1 :=
    @Subsingleton.elim _ hH0 _ _
  have hqmem : q ∈ tateNormSubgroup (Gal(L / K))
      (Multiplicative (chosenNormalBasisLatticeSuccQuot K L k)) := by
    have hm := (QuotientGroup.eq_one_iff _).1 hqone
    exact hm
  rcases hqmem with ⟨y, hy⟩
  rcases Phi.surjective y with ⟨qb, hqb⟩
  rcases chosenNormalBasisPrincipalUnitSuccQuotMk_surjective
      (L := L) hV qb with
    ⟨bv, hbvmk⟩
  change chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV bv = qb at hbvmk
  have hPhiNorm :
      Phi (tateNorm (Gal(L / K))
        (chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV)
        (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV bv)) = q := by
    calc
      Phi (tateNorm (Gal(L / K))
          (chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV)
          (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV bv)) =
          tateNorm (Gal(L / K))
            (Multiplicative (chosenNormalBasisLatticeSuccQuot K L k))
            (Phi (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV bv)) :=
        map_tateNorm Phi.toMonoidHom
          (fun sigma z => chosenNormalBasisPrincipalUnitSuccQuotMulEquiv_galoisGroup
            (K := K) (L := L) k hV hVn hVsucc Phi hPhi sigma z) _
      _ = tateNorm (Gal(L / K))
          (Multiplicative (chosenNormalBasisLatticeSuccQuot K L k)) y := by
        rw [hbvmk, hqb]
      _ = q := hy
  have hquotNorm :
      tateNorm (Gal(L / K))
          (chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV)
          (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV bv) =
        chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV av := by
    apply Phi.injective
    simpa [q] using hPhiNorm
  let bn : Vn := tateNorm (Gal(L / K)) Vn bv
  have hmkbn : chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV bn =
      chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV av := by
    calc
      chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV bn =
          tateNorm (Gal(L / K))
            (chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV)
            (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV bv) := by
        exact map_tateNorm
          (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV)
          (fun sigma z =>
            (chosenNormalBasisPrincipalUnitSuccQuotMulDistribMulAction_smul_mk
              (K := K) (L := L) k hV hVn hVsucc sigma z).symm) bv
      _ = chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV av := hquotNorm
  let aprimev : Vn := av / bn
  have haprimeSucc : (aprimev : 𝒪[L]ˣ) ∈ Vsucc := by
    apply (chosenNormalBasisPrincipalUnitSuccQuotMk_eq_one_iff
      (L := L) hV aprimev).1
    dsimp [aprimev]
    rw [map_div, hmkbn]
    simp
  have havfixed : ∀ sigma : Gal(L / K), sigma • av = av := by
    intro sigma
    apply Subtype.ext
    exact hfixed sigma
  have hbnfixed : ∀ sigma : Gal(L / K), sigma • bn = bn := by
    intro sigma
    exact smul_tateNorm_eq (G := Gal(L / K)) (A := Vn) sigma bv
  have haprimefixed : ∀ sigma : Gal(L / K), sigma • aprimev = aprimev := by
    intro sigma
    dsimp [aprimev]
    have ha' := havfixed sigma
    have hb' := hbnfixed sigma
    change (MulDistribMulAction.toMonoidHom Vn sigma) av = av at ha'
    change (MulDistribMulAction.toMonoidHom Vn sigma) bn = bn at hb'
    change (MulDistribMulAction.toMonoidHom Vn sigma) (av / bn) = av / bn
    rw [map_div, ha', hb']
  refine ⟨(bv : 𝒪[L]ˣ), (aprimev : 𝒪[L]ˣ), ?_, ?_, ?_, ?_⟩
  · exact hVn ▸ bv.2
  · exact hVsucc ▸ haprimeSucc
  · intro sigma
    exact congrArg (fun z : Vn => (z : 𝒪[L]ˣ)) (haprimefixed sigma)
  · have hbnval : (bn : 𝒪[L]ˣ) =
        tateNorm (Gal(L / K)) 𝒪[L]ˣ (bv : 𝒪[L]ˣ) := by
      exact map_tateNorm
        (chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) Vn)
        (fun sigma z => chosenNormalBasisPrincipalUnitSubgroupInclusion_equivariant
          (K := K) (L := L) k Vn hVn sigma z) bv
    change a = tateNorm (Gal(L / K)) 𝒪[L]ˣ (bv : 𝒪[L]ˣ) *
      (aprimev : 𝒪[L]ˣ)
    rw [← hbnval]
    dsimp [aprimev, av]
    simp

/-- One-step `H⁻¹` lifting: for a chosen generator, every
sufficiently deep norm-one unit is a coboundary from the same level times a
norm-one unit one level deeper. -/
theorem exists_chosenNormalBasisPrincipalUnit_hMinusOne_oneStep_lifting
    [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    (g : Gal(L / K)) (hgen : ∀ sigma : Gal(L / K),
      sigma ∈ Subgroup.zpowers g) :
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    ∃ c : Nat, ∀ k : Nat, c ≤ k → ∀ a : 𝒪[L]ˣ,
      a ∈ chosenNormalBasisPrincipalUnitSet K L k →
      tateNorm (Gal(L / K)) 𝒪[L]ˣ a = 1 →
      ∃ b a' : 𝒪[L]ˣ,
        b ∈ chosenNormalBasisPrincipalUnitSet K L k ∧
        a' ∈ chosenNormalBasisPrincipalUnitSet K L (k + 1) ∧
        tateNorm (Gal(L / K)) 𝒪[L]ˣ a' = 1 ∧
        a = sigmaMinusOne (Gal(L / K)) 𝒪[L]ˣ g b * a' := by
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  rcases exists_chosenNormalBasisPrincipalUnitSuccQuotMulEquivLatticeSuccQuot
      (K := K) (L := L) with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro k hck a ha hnorm
  rcases hc k hck with
    ⟨Vn, Vsucc, hV, hVn, hVsucc, Phi, _hVnle, hPhi⟩
  let := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction
    K L k Vn hVn
  let := chosenNormalBasisPrincipalUnitSuccQuotMulDistribMulAction
    K L k hV hVn hVsucc
  let := galoisGroupChosenNormalBasisLatticeSuccQuotDistribMulAction K L k
  let := multiplicativeMulDistribMulActionOfDistribMulAction
    (Gal(L / K)) (chosenNormalBasisLatticeSuccQuot K L k)
  let av : Vn := ⟨a, by
    change a ∈ (Vn : Set 𝒪[L]ˣ)
    rw [hVn]
    exact ha⟩
  have hnormv : tateNorm (Gal(L / K)) Vn av = 1 := by
    apply Subtype.ext
    have hmap := map_tateNorm
      (chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) Vn)
      (fun sigma z => chosenNormalBasisPrincipalUnitSubgroupInclusion_equivariant
        (K := K) (L := L) k Vn hVn sigma z) av
    change ((chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) Vn)
      (tateNorm (Gal(L / K)) Vn av) : 𝒪[L]ˣ) =
        tateNorm (Gal(L / K)) 𝒪[L]ˣ a at hmap
    rw [hnorm] at hmap
    exact hmap
  let q : Multiplicative (chosenNormalBasisLatticeSuccQuot K L k) :=
    Phi (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV av)
  have hqnorm : tateNorm (Gal(L / K))
      (Multiplicative (chosenNormalBasisLatticeSuccQuot K L k)) q = 1 := by
    dsimp [q]
    calc
      tateNorm (Gal(L / K))
          (Multiplicative (chosenNormalBasisLatticeSuccQuot K L k))
          (Phi (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV av)) =
          Phi (tateNorm (Gal(L / K))
            (chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV)
            (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV av)) :=
        (map_tateNorm Phi.toMonoidHom
          (fun sigma z => chosenNormalBasisPrincipalUnitSuccQuotMulEquiv_galoisGroup
            (K := K) (L := L) k hV hVn hVsucc Phi hPhi sigma z) _).symm
      _ = Phi (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV
          (tateNorm (Gal(L / K)) Vn av)) := by
        congr 1
        exact (map_tateNorm
          (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV)
          (fun sigma z =>
            (chosenNormalBasisPrincipalUnitSuccQuotMulDistribMulAction_smul_mk
              (K := K) (L := L) k hV hVn hVsucc sigma z).symm) av).symm
      _ = 1 := by rw [hnormv]; simp
  let qker : normKernelSubgroup (Gal(L / K))
      (Multiplicative (chosenNormalBasisLatticeSuccQuot K L k)) :=
    ⟨q, hqnorm⟩
  have hHm := chosenNormalBasisLatticeSuccQuot_herbrandHMinusOne_subsingleton
    K L k g hgen
  have hqone :
      QuotientGroup.mk'
          ((augmentationSubgroup (Gal(L / K))
            (Multiplicative (chosenNormalBasisLatticeSuccQuot K L k)) g).subgroupOf
              (normKernelSubgroup (Gal(L / K))
                (Multiplicative (chosenNormalBasisLatticeSuccQuot K L k))))
          qker = 1 :=
    @Subsingleton.elim _ hHm _ _
  have hqmem : q ∈ augmentationSubgroup (Gal(L / K))
      (Multiplicative (chosenNormalBasisLatticeSuccQuot K L k)) g := by
    have hm := (QuotientGroup.eq_one_iff _).1 hqone
    exact hm
  rcases hqmem with ⟨y, hy⟩
  rcases Phi.surjective y with ⟨qb, hqb⟩
  rcases chosenNormalBasisPrincipalUnitSuccQuotMk_surjective
      (L := L) hV qb with
    ⟨bv, hbvmk⟩
  change chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV bv = qb at hbvmk
  have hPhiCoboundary :
      Phi (sigmaMinusOne (Gal(L / K))
        (chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV) g
        (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV bv)) = q := by
    calc
      Phi (sigmaMinusOne (Gal(L / K))
          (chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV) g
          (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV bv)) =
          sigmaMinusOne (Gal(L / K))
            (Multiplicative (chosenNormalBasisLatticeSuccQuot K L k)) g
            (Phi (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV bv)) :=
        map_sigmaMinusOne Phi.toMonoidHom
          (fun sigma z => chosenNormalBasisPrincipalUnitSuccQuotMulEquiv_galoisGroup
            (K := K) (L := L) k hV hVn hVsucc Phi hPhi sigma z) g _
      _ = sigmaMinusOne (Gal(L / K))
          (Multiplicative (chosenNormalBasisLatticeSuccQuot K L k)) g y := by
        rw [hbvmk, hqb]
      _ = q := hy
  have hquotCoboundary :
      sigmaMinusOne (Gal(L / K))
          (chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV) g
          (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV bv) =
        chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV av := by
    apply Phi.injective
    simpa [q] using hPhiCoboundary
  let cobv : Vn := sigmaMinusOne (Gal(L / K)) Vn g bv
  have hmkcob : chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV cobv =
      chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV av := by
    calc
      chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV cobv =
          sigmaMinusOne (Gal(L / K))
            (chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV) g
            (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV bv) := by
        exact map_sigmaMinusOne
          (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV)
          (fun sigma z =>
            (chosenNormalBasisPrincipalUnitSuccQuotMulDistribMulAction_smul_mk
              (K := K) (L := L) k hV hVn hVsucc sigma z).symm) g bv
      _ = chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV av := hquotCoboundary
  let aprimev : Vn := av / cobv
  have haprimeSucc : (aprimev : 𝒪[L]ˣ) ∈ Vsucc := by
    apply (chosenNormalBasisPrincipalUnitSuccQuotMk_eq_one_iff
      (L := L) hV aprimev).1
    dsimp [aprimev]
    rw [map_div, hmkcob]
    simp
  have haprimeNormV : tateNorm (Gal(L / K)) Vn aprimev = 1 := by
    dsimp [aprimev, cobv]
    rw [div_eq_mul_inv, tateNorm_mul, tateNorm_inv, hnormv,
      tateNorm_sigmaMinusOne_eq_one]
    simp
  have haprimeNorm : tateNorm (Gal(L / K)) 𝒪[L]ˣ
      (aprimev : 𝒪[L]ˣ) = 1 := by
    have hmap := map_tateNorm
      (chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) Vn)
      (fun sigma z => chosenNormalBasisPrincipalUnitSubgroupInclusion_equivariant
        (K := K) (L := L) k Vn hVn sigma z) aprimev
    have hleft :
        chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) Vn
          (tateNorm (Gal(L / K)) Vn aprimev) = 1 :=
      (congrArg
        (chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) Vn)
        haprimeNormV).trans
          (chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) Vn).map_one
    exact (congrArg (tateNorm (Gal(L / K)) 𝒪[L]ˣ)
      (chosenNormalBasisPrincipalUnitSubgroupInclusion_apply
        (L := L) Vn aprimev)).symm.trans (hmap.symm.trans hleft)
  refine ⟨(bv : 𝒪[L]ˣ), (aprimev : 𝒪[L]ˣ), ?_, ?_, haprimeNorm, ?_⟩
  · exact hVn ▸ bv.2
  · exact hVsucc ▸ haprimeSucc
  · have hcobval : (cobv : 𝒪[L]ˣ) =
        sigmaMinusOne (Gal(L / K)) 𝒪[L]ˣ g (bv : 𝒪[L]ˣ) := by
      exact map_sigmaMinusOne
        (chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) Vn)
        (fun sigma z => chosenNormalBasisPrincipalUnitSubgroupInclusion_equivariant
          (K := K) (L := L) k Vn hVn sigma z) g bv
    change a = sigmaMinusOne (Gal(L / K)) 𝒪[L]ˣ g (bv : 𝒪[L]ˣ) *
      (aprimev : 𝒪[L]ˣ)
    rw [← hcobval]
    dsimp [aprimev, av]
    simp

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_NormalBasisRecursiveLifting
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseIsValuativeTopology _root_.chosenFinitePlaceBaseValued _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
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
# Infinite lifting on the normal-basis principal-unit filtration

This is the recursive core of the local class-field-axiom theorem.  The one-step graded
lifting is iterated, its correction factors are multiplied, and completeness
of the local field turns the resulting formal recursion into an actual norm
or coboundary in the initial subgroup.
-/

noncomputable section

universe u

open scoped ValuativeRel
open Filter IsNonarchimedeanLocalField
open CyclicCohomology.ProfiniteCohomology.Herbrand

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
  [IsNonarchimedeanLocalField L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]

omit [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L] in
theorem filteredCorrectionProduct_eq_chosenNormalBasisProduct
    (z : Nat → 𝒪[L]ˣ) (d : Nat) :
    filteredCorrectionProduct z d =
      chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d := by
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [filteredCorrectionProduct_succ,
        chosenNormalBasisPrincipalUnitCorrectionProduct_succ, ih]

/-- Recursive `H⁰` lifting.  At every sufficiently deep
normal-basis level, an actually fixed unit is the norm of a unit at the same
level. -/
theorem exists_chosenNormalBasisPrincipalUnit_fixed_is_tateNorm :
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    ∃ c : Nat, ∀ n : Nat, c ≤ n → ∀ a : 𝒪[L]ˣ,
      a ∈ chosenNormalBasisPrincipalUnitSet K L n →
      (∀ sigma : Gal(L / K), sigma • a = a) →
      ∃ b : 𝒪[L]ˣ, b ∈ chosenNormalBasisPrincipalUnitSet K L n ∧
        a = tateNorm (Gal(L / K)) 𝒪[L]ˣ b := by
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  rcases exists_chosenNormalBasisPrincipalUnit_h0_oneStep_lifting
      (K := K) (L := L) with ⟨cStep, hStep⟩
  rcases exists_tendsto_chosenNormalBasisPrincipalUnitCorrectionProduct
      (K := K) (L := L) with ⟨cProd, hProd⟩
  rcases exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_le_integerRingFieldSubmodule
      (K := K) (L := L) with ⟨b, hb⟩
  refine ⟨max cStep (max cProd (b + 1)), ?_⟩
  intro n hn a ha hfixed
  have hcStep : cStep ≤ n :=
    le_trans (le_max_left cStep (max cProd (b + 1))) hn
  have hrest : max cProd (b + 1) ≤ max cStep (max cProd (b + 1)) :=
    le_max_right cStep (max cProd (b + 1))
  have hcProd : cProd ≤ n :=
    le_trans (le_trans (le_max_left cProd (b + 1)) hrest) hn
  have hbn : b + 1 ≤ n :=
    le_trans (le_trans (le_max_right cProd (b + 1)) hrest) hn
  let P : Nat → 𝒪[L]ˣ → Prop := fun k x =>
    x ∈ chosenNormalBasisPrincipalUnitSet K L k
  let R : 𝒪[L]ˣ → Prop := fun x =>
    ∀ sigma : Gal(L / K), sigma • x = x
  let F : 𝒪[L]ˣ →* 𝒪[L]ˣ :=
    tateNormHom (G := Gal(L / K)) (A := 𝒪[L]ˣ)
  let initial : FilteredLiftState 𝒪[L]ˣ P R n 0 :=
    ⟨a, by simpa [P] using ha, hfixed⟩
  let step : ∀ i (s : FilteredLiftState 𝒪[L]ˣ P R n i),
      Nonempty (FilteredLiftStep 𝒪[L]ˣ P R F n i s) := by
    intro i s
    have hlevel : cStep ≤ n + i :=
      le_trans hcStep (Nat.le_add_right n i)
    rcases hStep (n + i) hlevel s.value (by simpa [P] using s.mem)
        (by simpa [R] using s.stable) with
      ⟨z, a', hz, ha', hfixed', heq⟩
    refine ⟨⟨z, ?_, ⟨a', ?_, ?_⟩, ?_⟩⟩
    · simpa [P] using hz
    · simpa [P, Nat.add_assoc] using ha'
    · simpa [R] using hfixed'
    · simpa [F] using heq
  let states : (i : Nat) → FilteredLiftState 𝒪[L]ˣ P R n i :=
    chosenFilteredLiftStateSequence 𝒪[L]ˣ P R F n initial step
  let z : Nat → 𝒪[L]ˣ :=
    chosenFilteredLiftCorrectionSequence 𝒪[L]ˣ P R F n initial step
  have hz (i : Nat) : z i ∈ chosenNormalBasisPrincipalUnitSet K L (n + i) := by
    exact chosenFilteredLiftCorrectionSequence_mem
      𝒪[L]ˣ P R F n initial step i
  rcases hProd n hcProd z hz with ⟨x, hx, hxmem⟩
  have hstates (i : Nat) :
      (states i).value ∈ chosenNormalBasisPrincipalUnitSet K L (n + i) := by
    exact (states i).mem
  have hrem : Tendsto
      (fun i : Nat => (((states i).value : 𝒪[L]ˣ) : 𝒪[L])) atTop
      (nhds (1 : 𝒪[L])) :=
    tendsto_chosenNormalBasisPrincipalUnitSequence_one_of_lattice_bound
      (K := K) (L := L) hb hbn (fun i => (states i).value) hstates
  have hnorm := tendsto_galoisGroupIntegerUnits_tateNorm_of_tendsto
    (K := K) (L := L)
    (fun d => chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d) x hx
  have hrec (d : Nat) :
      a = tateNorm (Gal(L / K)) 𝒪[L]ˣ
          (chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d) *
        (states d).value := by
    have h := filteredLift_initial_eq_correctionProduct_mul_state
      𝒪[L]ˣ P R F n initial step d
    rw [filteredCorrectionProduct_eq_chosenNormalBasisProduct
      (L := L) z d] at h
    simpa [initial, states, F] using h
  have hmul : Tendsto
      (fun d : Nat =>
        ((tateNorm (Gal(L / K)) 𝒪[L]ˣ
            (chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d) :
          𝒪[L]ˣ) : 𝒪[L]) * (((states d).value : 𝒪[L]ˣ) : 𝒪[L]))
      atTop
      (nhds (((tateNorm (Gal(L / K)) 𝒪[L]ˣ x : 𝒪[L]ˣ) : 𝒪[L]) * 1)) :=
    hnorm.mul hrem
  have hconst : Tendsto (fun _d : Nat => ((a : 𝒪[L]ˣ) : 𝒪[L])) atTop
      (nhds ((a : 𝒪[L]ˣ) : 𝒪[L])) := tendsto_const_nhds
  have heqO : ((a : 𝒪[L]ˣ) : 𝒪[L]) =
      ((tateNorm (Gal(L / K)) 𝒪[L]ˣ x : 𝒪[L]ˣ) : 𝒪[L]) * 1 := by
    apply tendsto_nhds_unique hconst
    exact hmul.congr' (Eventually.of_forall (fun d => by
      simpa using congrArg (fun q : 𝒪[L]ˣ => (q : 𝒪[L])) (hrec d).symm))
  refine ⟨x, hxmem, ?_⟩
  apply Units.ext
  simpa using heqO

/-- Recursive `H⁻¹` lifting.  For a chosen generator,
every sufficiently deep norm-one unit is an actual coboundary from the same
normal-basis level. -/
theorem exists_chosenNormalBasisPrincipalUnit_normOne_is_sigmaMinusOne
    (g : Gal(L / K)) (hgen : ∀ sigma : Gal(L / K),
      sigma ∈ Subgroup.zpowers g) :
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    ∃ c : Nat, ∀ n : Nat, c ≤ n → ∀ a : 𝒪[L]ˣ,
      a ∈ chosenNormalBasisPrincipalUnitSet K L n →
      tateNorm (Gal(L / K)) 𝒪[L]ˣ a = 1 →
      ∃ b : 𝒪[L]ˣ, b ∈ chosenNormalBasisPrincipalUnitSet K L n ∧
        a = sigmaMinusOne (Gal(L / K)) 𝒪[L]ˣ g b := by
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  rcases exists_chosenNormalBasisPrincipalUnit_hMinusOne_oneStep_lifting
      (K := K) (L := L) g hgen with ⟨cStep, hStep⟩
  rcases exists_tendsto_chosenNormalBasisPrincipalUnitCorrectionProduct
      (K := K) (L := L) with ⟨cProd, hProd⟩
  rcases exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_le_integerRingFieldSubmodule
      (K := K) (L := L) with ⟨b, hb⟩
  refine ⟨max cStep (max cProd (b + 1)), ?_⟩
  intro n hn a ha hnorma
  have hcStep : cStep ≤ n :=
    le_trans (le_max_left cStep (max cProd (b + 1))) hn
  have hrest : max cProd (b + 1) ≤ max cStep (max cProd (b + 1)) :=
    le_max_right cStep (max cProd (b + 1))
  have hcProd : cProd ≤ n :=
    le_trans (le_trans (le_max_left cProd (b + 1)) hrest) hn
  have hbn : b + 1 ≤ n :=
    le_trans (le_trans (le_max_right cProd (b + 1)) hrest) hn
  let P : Nat → 𝒪[L]ˣ → Prop := fun k x =>
    x ∈ chosenNormalBasisPrincipalUnitSet K L k
  let R : 𝒪[L]ˣ → Prop := fun x =>
    tateNorm (Gal(L / K)) 𝒪[L]ˣ x = 1
  let F : 𝒪[L]ˣ →* 𝒪[L]ˣ :=
    sigmaMinusOneHom (G := Gal(L / K)) (A := 𝒪[L]ˣ) g
  let initial : FilteredLiftState 𝒪[L]ˣ P R n 0 :=
    ⟨a, by simpa [P] using ha, hnorma⟩
  let step : ∀ i (s : FilteredLiftState 𝒪[L]ˣ P R n i),
      Nonempty (FilteredLiftStep 𝒪[L]ˣ P R F n i s) := by
    intro i s
    have hlevel : cStep ≤ n + i :=
      le_trans hcStep (Nat.le_add_right n i)
    rcases hStep (n + i) hlevel s.value (by simpa [P] using s.mem)
        (by simpa [R] using s.stable) with
      ⟨z, a', hz, ha', hnorm', heq⟩
    refine ⟨⟨z, ?_, ⟨a', ?_, ?_⟩, ?_⟩⟩
    · simpa [P] using hz
    · simpa [P, Nat.add_assoc] using ha'
    · simpa [R] using hnorm'
    · simpa [F] using heq
  let states : (i : Nat) → FilteredLiftState 𝒪[L]ˣ P R n i :=
    chosenFilteredLiftStateSequence 𝒪[L]ˣ P R F n initial step
  let z : Nat → 𝒪[L]ˣ :=
    chosenFilteredLiftCorrectionSequence 𝒪[L]ˣ P R F n initial step
  have hz (i : Nat) : z i ∈ chosenNormalBasisPrincipalUnitSet K L (n + i) := by
    exact chosenFilteredLiftCorrectionSequence_mem
      𝒪[L]ˣ P R F n initial step i
  rcases hProd n hcProd z hz with ⟨x, hx, hxmem⟩
  have hstates (i : Nat) :
      (states i).value ∈ chosenNormalBasisPrincipalUnitSet K L (n + i) :=
    (states i).mem
  have hrem : Tendsto
      (fun i : Nat => (((states i).value : 𝒪[L]ˣ) : 𝒪[L])) atTop
      (nhds (1 : 𝒪[L])) :=
    tendsto_chosenNormalBasisPrincipalUnitSequence_one_of_lattice_bound
      (K := K) (L := L) hb hbn (fun i => (states i).value) hstates
  have hcob := tendsto_galoisGroupIntegerUnits_sigmaMinusOne_of_tendsto
    (K := K) (L := L) g
    (fun d => chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d) x hx
  have hrec (d : Nat) :
      a = sigmaMinusOne (Gal(L / K)) 𝒪[L]ˣ g
          (chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d) *
        (states d).value := by
    have h := filteredLift_initial_eq_correctionProduct_mul_state
      𝒪[L]ˣ P R F n initial step d
    rw [filteredCorrectionProduct_eq_chosenNormalBasisProduct
      (L := L) z d] at h
    simpa [initial, states, F] using h
  have hmul : Tendsto
      (fun d : Nat =>
        ((sigmaMinusOne (Gal(L / K)) 𝒪[L]ˣ g
            (chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d) :
          𝒪[L]ˣ) : 𝒪[L]) * (((states d).value : 𝒪[L]ˣ) : 𝒪[L]))
      atTop
      (nhds (((sigmaMinusOne (Gal(L / K)) 𝒪[L]ˣ g x : 𝒪[L]ˣ) : 𝒪[L]) * 1)) :=
    hcob.mul hrem
  have hconst : Tendsto (fun _d : Nat => ((a : 𝒪[L]ˣ) : 𝒪[L])) atTop
      (nhds ((a : 𝒪[L]ˣ) : 𝒪[L])) := tendsto_const_nhds
  have heqO : ((a : 𝒪[L]ˣ) : 𝒪[L]) =
      ((sigmaMinusOne (Gal(L / K)) 𝒪[L]ˣ g x : 𝒪[L]ˣ) : 𝒪[L]) * 1 := by
    apply tendsto_nhds_unique hconst
    exact hmul.congr' (Eventually.of_forall (fun d => by
      simpa using congrArg (fun q : 𝒪[L]ˣ => (q : 𝒪[L])) (hrec d).symm))
  refine ⟨x, hxmem, ?_⟩
  apply Units.ext
  simpa using heqO

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_NormalBasisCohomology
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
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
# Low-degree cohomology of a deep normal-basis unit subgroup

The recursive norm and coboundary constructions are converted here into the
actual quotient statements `H⁰(G,V)=H⁻¹(G,V)=1` used in the local class-field-axiom theorem.
-/

noncomputable section

universe u

open scoped ValuativeRel
open IsNonarchimedeanLocalField
open CyclicCohomology.ProfiniteCohomology.Herbrand

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
  [IsNonarchimedeanLocalField L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]

/-- The local class-field-axiom theorem: for every sufficiently deep chosen normal-basis subgroup
`V`, both low-degree Herbrand quotients are trivial. -/
theorem exists_chosenNormalBasisPrincipalUnit_herbrand_subsingleton
    (g : Gal(L / K))
    (hgen : ∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g) :
    ∃ c : Nat, ∀ n : Nat, c ≤ n →
      ∀ (V : Subgroup 𝒪[L]ˣ)
        (hV : (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n),
        letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction
          K L n V hV
        Subsingleton (HerbrandH0 (Gal(L / K)) V) ∧
          Subsingleton (HerbrandHMinusOne (Gal(L / K)) V g) := by
  rcases exists_chosenNormalBasisPrincipalUnit_fixed_is_tateNorm
      (K := K) (L := L) with ⟨c0, hc0⟩
  rcases exists_chosenNormalBasisPrincipalUnit_normOne_is_sigmaMinusOne
      (K := K) (L := L) g hgen with ⟨cm, hcm⟩
  refine ⟨max c0 cm, ?_⟩
  intro n hn V hV
  have hc0n : c0 ≤ n := le_trans (le_max_left c0 cm) hn
  have hcmn : cm ≤ n := le_trans (le_max_right c0 cm) hn
  let := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction
    K L n V hV
  have hfixed : fixedSubgroup (Gal(L / K)) V ≤
      tateNormSubgroup (Gal(L / K)) V := by
    intro a ha
    have haSet : ((a : V) : 𝒪[L]ˣ) ∈ (V : Set 𝒪[L]ˣ) := (a : V).2
    have haLevel : ((a : V) : 𝒪[L]ˣ) ∈
        chosenNormalBasisPrincipalUnitSet K L n := by
      rw [← hV]
      exact haSet
    have haFixed : ∀ sigma : Gal(L / K),
        letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
        sigma • ((a : V) : 𝒪[L]ˣ) = ((a : V) : 𝒪[L]ˣ) := by
      intro sigma
      exact congrArg (fun z : V => (z : 𝒪[L]ˣ)) (ha sigma)
    rcases hc0 n hc0n ((a : V) : 𝒪[L]ˣ) haLevel haFixed with
      ⟨b, hb, hab⟩
    let bv : V := ⟨b, by
      change b ∈ (V : Set 𝒪[L]ˣ)
      rw [hV]
      exact hb⟩
    refine ⟨bv, ?_⟩
    apply Subtype.ext
    rw [tateNormHom_apply,
      chosenNormalBasisPrincipalUnitSubgroup_tateNorm_coe K L n V hV]
    exact hab.symm
  have hkernel : normKernelSubgroup (Gal(L / K)) V ≤
      augmentationSubgroup (Gal(L / K)) V g := by
    intro a ha
    have haLevel : ((a : V) : 𝒪[L]ˣ) ∈
        chosenNormalBasisPrincipalUnitSet K L n := by
      rw [← hV]
      exact (a : V).2
    have haNorm :
        letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
        tateNorm (Gal(L / K)) 𝒪[L]ˣ ((a : V) : 𝒪[L]ˣ) = 1 := by
      rw [← chosenNormalBasisPrincipalUnitSubgroup_tateNorm_coe K L n V hV]
      exact congrArg (fun z : V => (z : 𝒪[L]ˣ)) ha
    rcases hcm n hcmn ((a : V) : 𝒪[L]ˣ) haLevel haNorm with
      ⟨b, hb, hab⟩
    let bv : V := ⟨b, by
      change b ∈ (V : Set 𝒪[L]ˣ)
      rw [hV]
      exact hb⟩
    refine ⟨bv, ?_⟩
    apply Subtype.ext
    rw [sigmaMinusOneHom_apply,
      chosenNormalBasisPrincipalUnitSubgroup_sigmaMinusOne_coe K L n V hV]
    exact hab.symm
  exact ⟨
    herbrandH0_subsingleton_of_fixed_le_tateNormSubgroup hfixed,
    herbrandHMinusOne_subsingleton_of_normKernel_le_augmentationSubgroup
      g hkernel⟩

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_LocalizedCompletionCohomology_Algebra
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Algebra for localized completion cohomology

This file provides named algebra, finite-dimensional, Galois, scalar-tower, and
global-to-local embedding providers for localized completions.
-/

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand
open scoped TensorProduct

noncomputable section

namespace LocalClassFieldTheory

universe u v

variable {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]

theorem localizedCompletionIsScalarTower
    (vK : AbsoluteValue K ℝ)
    (w : AbsoluteValueExtension vK L) :
    letI : Algebra vK.Completion (LocalizedCompletion vK w) :=
      localizedCompletionBaseAlgebra vK w
    letI := localizedCompletionGlobalAlgebra vK w
    IsScalarTower K vK.Completion
      (LocalizedCompletion vK w) := by
  let _ : Algebra vK.Completion (LocalizedCompletion vK w) :=
    localizedCompletionBaseAlgebra vK w
  let _ := localizedCompletionGlobalAlgebra vK w
  exact IsScalarTower.of_algebraMap_eq' rfl


end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_SeparableUnitsNorm
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

section EmbeddedFiniteGaloisExtension

variable (L : Type) [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  (i : L →ₐ[K] Ω)

attribute [local instance] LocalClassFieldTheory.embeddedFieldRangeFiniteDimensional
attribute [local instance] LocalClassFieldTheory.embeddedFieldRangeIsGalois
omit [IsGalois K Ω] [FiniteDimensional K L] [IsGalois K L] in

/-- The ordinary norm subgroups are independent of the chosen realization of
the finite extension inside the ambient Galois extension. -/
theorem localNormSubgroup_fieldRange_eq :
    localNormSubgroup K (AlgHom.fieldRange i) = localNormSubgroup K L := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    let z : Lˣ := Units.mapEquiv
      (AlgEquiv.ofInjectiveField i).symm.toMulEquiv y
    refine ⟨z, ?_⟩
    have hz : Units.mapEquiv
        (AlgEquiv.ofInjectiveField i).toMulEquiv z = y := by
      exact (Units.mapEquiv
        (AlgEquiv.ofInjectiveField i).toMulEquiv).apply_symm_apply y
    rw [← hz, normUnits_embeddedExtensionAlgEquiv]
  · rintro ⟨x, rfl⟩
    refine ⟨Units.mapEquiv
      (AlgEquiv.ofInjectiveField i).toMulEquiv x, ?_⟩
    exact normUnits_embeddedExtensionAlgEquiv K Ω L i x

end EmbeddedFiniteGaloisExtension

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_GaloisValuation_AbsoluteGalois_AbsoluteRamification
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace RamificationTheory

open ValuationTheory

/-!
# Absolute Galois ramification

This file develops the decomposition and inertia subgroups of an absolute
Galois group after the finite-level valuation-restriction layer.
-/

noncomputable section

universe u v w z

namespace Field
namespace absoluteGaloisGroup

open scoped Topology Pointwise
open CategoryTheory

section AbsoluteRamification

variable (K : Type u) [Field K]

/-- Proof-dependent Henselian-DVF-facing absolute residue action.  The
Henselian top theorem is kept as an explicit argument; once
`decompositionSubgroup_eq_top_of_henselianDVF` is available, this is the stable
name used downstream without changing the residue-action target. -/
noncomputable def absoluteResidueActionOfHenselianDVF
    (F : ValuationTheory.DiscreteValuationField.HenselianDVF.{u, v} K)
    (A : ValuationSubring (AlgebraicClosure K))
    [_root_.Valuation.HasExtension F.valuation A.valuation]
    (hA : decompositionSubgroup K A = ⊤) :
    MonoidHom (Field.absoluteGaloisGroup K)
      (RingEquiv (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A)) :=
  absoluteResidueActionOfDecompositionSubgroupEqTop K A hA

/-- States the theorem `absoluteResidueActionOfHenselianDVF_apply`. -/
@[simp] theorem absoluteResidueActionOfHenselianDVF_apply
    (F : ValuationTheory.DiscreteValuationField.HenselianDVF.{u, v} K)
    (A : ValuationSubring (AlgebraicClosure K))
    [_root_.Valuation.HasExtension F.valuation A.valuation]
    (hA : decompositionSubgroup K A = ⊤)
    (sigma : Field.absoluteGaloisGroup K) :
    absoluteResidueActionOfHenselianDVF K F A hA sigma =
      absoluteResidueActionOfDecompositionSubgroupEqTop K A hA sigma :=
  rfl

end AbsoluteRamification

end absoluteGaloisGroup
end Field

end

end RamificationTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FiniteResidueValuationComparison
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory

open ValuationTheory RamificationTheory

/-!
# Finite-separable comparison of restricted valuation rings

The valuation on an algebraic ambient field can be restricted to a finite
intermediate field.  Over a complete discrete valuation field this
restriction is the unique extension valuation ring, so it agrees with any
other extension valuation ring on the finite field.  This is the
valuation-ring comparison used in the finite local reciprocity construction before comparing residue
degrees.
-/

noncomputable section

universe u v w

open DiscreteValuationField

/-- Over a complete discrete valuation field, restricting an ambient
extension valuation ring to a finite separable intermediate field gives the
same valuation ring as any independently constructed extension valuation on
that intermediate field. -/
theorem ValuationSubring.restrictIntermediateField_eq_of_finite_separable
    {K : Type u} {Omega : Type v} [Field K] [Field Omega] [Algebra K Omega]
    (base : CompleteDVF K)
    (A : ValuationSubring Omega) [base.valuation.HasExtension A.valuation]
    (E : IntermediateField K Omega) [FiniteDimensional K E]
    [Algebra.IsSeparable K E]
    (C : ValuationSubring E) [base.valuation.HasExtension C.valuation] :
    A.restrictIntermediateField E = C := by
  let B := A.restrictIntermediateField E
  let : base.valuation.HasExtension B.valuation :=
    RamificationTheory.ValuationSubring.restrictIntermediateField_hasExtension
      base.valuation A E
  obtain ⟨target, hExt, _hIntegralClosure, _hFundamental⟩ :=
    DiscreteValuationField.ValuedExtension.exists_integralClosure_standard_fundamental_identity
      (K := K) (L := E) base
  let : base.valuation.HasExtension target.valuation := hExt
  have hB : target.valuation.valuationSubring = B :=
    DiscreteValuationField.ValuedExtension.target_valuationSubring_eq_of_finite_separable
      base target B
  have hC : target.valuation.valuationSubring = C :=
    DiscreteValuationField.ValuedExtension.target_valuationSubring_eq_of_finite_separable
      base target C
  exact hB.symm.trans hC

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Extension_LocalNorm
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.HilbertRamification.decompositionField_decompositionField_integerMap_isLocalHom _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Local components of the idele norm

The local algebra at a place of the base field is a finite product of the
completions above it. This file proves that the determinant norm on a finite
product is the product of the norms of its factors. The last theorem applies
this calculation to the canonical completion decomposition.
-/

open scoped BigOperators TensorProduct

noncomputable section


namespace RelativeIdeleGroup

open AlgebraicNumberTheory.Valuations
open ValuationTheory.Completion

universe u v

/-- At one place of the base field, under the
canonical isomorphism

`K_v ⊗[K] L ≃ ∏_{w ∣ v} L_w`,

the determinant norm of an arbitrary local component is the product of
the field norms of its components above `v`. -/
theorem localNorm_eq_prod
    {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (z : vK.Completion ⊗[K] L) :
    letI :=
      completionTensorDecomposition_extensionFintype
        (K := K) (L := L) vK hvK
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : ∀ w : AbsoluteValueExtension vK L,
        Module.Finite vK.Completion w.1.Completion :=
      fun w ↦ completionModuleFinite vK hvK w
    _root_.Algebra.norm vK.Completion z =
      ∏ w : AbsoluteValueExtension vK L,
        _root_.Algebra.norm vK.Completion
          (completionTensorDecomposition_left
            (K := K) (L := L) vK hvK z w) := by
  classical
  let :=
    completionTensorDecomposition_extensionFintype
      (K := K) (L := L) vK hvK
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  let : ∀ w : AbsoluteValueExtension vK L,
      Module.Free vK.Completion w.1.Completion :=
    fun w ↦ Module.Free.of_divisionRing
      vK.Completion w.1.Completion
  let : ∀ w : AbsoluteValueExtension vK L,
      Module.Finite vK.Completion w.1.Completion :=
    fun w ↦ completionModuleFinite vK hvK w
  let e :=
    completionTensorDecomposition_left
      (K := K) (L := L) vK hvK
  calc
    _root_.Algebra.norm vK.Completion z =
        _root_.Algebra.norm vK.Completion (e z) :=
      (_root_.Algebra.norm_eq_of_algEquiv e z).symm
    _ = ∏ w : AbsoluteValueExtension vK L,
        _root_.Algebra.norm vK.Completion (e z w) :=
      algebra_norm_pi_apply
        (R := vK.Completion)
        (fun w : AbsoluteValueExtension vK L ↦
          w.1.Completion) (e z)

/-- The unit-valued version of `localNorm_eq_prod`, which is the formula
used for local components of ideles. -/
theorem localNorm_units_eq_prod
    {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (z : (vK.Completion ⊗[K] L)ˣ) :
    letI :=
      completionTensorDecomposition_extensionFintype
        (K := K) (L := L) vK hvK
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : ∀ w : AbsoluteValueExtension vK L,
        Module.Finite vK.Completion w.1.Completion :=
      fun w ↦ completionModuleFinite vK hvK w
    ((Units.map (_root_.Algebra.norm vK.Completion) z :
        vK.Completionˣ) : vK.Completion) =
      ∏ w : AbsoluteValueExtension vK L,
        _root_.Algebra.norm vK.Completion
          (completionTensorDecomposition_left
            (K := K) (L := L) vK hvK (z : _) w) := by
  exact localNorm_eq_prod vK hvK (z : vK.Completion ⊗[K] L)

end RelativeIdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_LocalBlocks_Tensor
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.HilbertRamification.decompositionField_decompositionField_integerMap_isLocalHom _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

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
open HilbertRamification
open CyclicCohomology

universe u v

variable {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [IsGalois K L]

section ProductEquivalences

variable (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)

/-- The product of completions above `v` is the induced block from the
decomposition group.  This form is valid for an arbitrary finite Galois
extension; the decomposition group need not be normal. -/
noncomputable def completionProductUnitsEquivLocalPlaceBlock :
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    (∀ w' : AbsoluteValueExtension vK L, w'.1.Completionˣ) ≃*
      LocalPlaceBlock vK hvK w := by
  letI :=
    decompositionGroupLocalUnitsAction vK hvK w
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  exact
    (completionProductUnitsEquivRightCosets vK hvK w).trans
      (inducedRightCosetCoordinates
        (absoluteValueDecompositionGroup K w.1)).symm

end ProductEquivalences

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_LocalBlocks_TensorNorm
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The norm image of a local tensor factor

For a finite Galois extension `L / K`, the completion tensor-product theorem decomposes

`K_v ⊗[K] L`

as the product of the completions above `v`.  After choosing one extension
`w`, Galois conjugation identifies every factor with `L_w`.  Consequently
the image of the determinant norm on the tensor algebra is exactly the field
norm subgroup of `L_w / K_v`.

This is the concrete norm-subgroup form of the local calculation used in
the local-block norm calculation, and it is also the bridge between the local cohomology
calculation and multiplicative weak approximation.
-/

open scoped BigOperators TensorProduct

noncomputable section

namespace LocalClassFieldTheory

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalFieldTheory
open ValuationTheory.Completion

universe u

variable {K L : Type u}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The determinant norm on the unit group of a local tensor algebra. -/
def localTensorDetNorm
    (vK : AbsoluteValue K ℝ) :
    (LocalTensorAlgebra (L := L) vK)ˣ →*
      vK.Completionˣ :=
  Units.map (Algebra.norm vK.Completion)

/-- The image of the determinant norm on a local tensor algebra. -/
def localTensorNormSubgroup
    (vK : AbsoluteValue K ℝ) :
    Subgroup vK.Completionˣ :=
  (localTensorDetNorm (K := K) (L := L) vK).range

section ChosenCompletion

variable (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)

/-- The completion tensor-product decomposition, with all factors transported to the one
chosen algebraic localization. -/
noncomputable def localTensorUnitsEquivChosenCoordinates :
    letI hK :=
      AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : ∀ w' : AbsoluteValueExtension vK L,
        Algebra vK.Completion w'.1.Completion :=
      fun w' ↦ AbsoluteValue.completionAlgebra vK w'.1 w'.2
    (LocalTensorAlgebra (L := L) vK)ˣ ≃*
      (InducedRightCosets
          (absoluteValueDecompositionGroup K w.1) →
        (LocalizedCompletion vK w)ˣ) := by
  letI hK :=
    AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  letI : ∀ w' : AbsoluteValueExtension vK L,
      Algebra vK.Completion w'.1.Completion :=
    fun w' ↦ AbsoluteValue.completionAlgebra vK w'.1 w'.2
  exact
    (localTensorUnitsEquivCompletionProduct
      vK hvK).trans
      (completionProductUnitsEquivRightCosets
        vK hvK w)

end ChosenCompletion

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Relative_FinitePlaceTensorNorm
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.scaledRelativeIntegerLatticeQuotientFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Tensor norm images at actual finite places

This file specializes the local tensor norm calculation to a height-one
prime of a number field.  The canonical comparison

`(K, |·|_v)^∧ ≃ K_v`

identifies the determinant norm on
`(K, |·|_v)^∧ ⊗[K] L` with the determinant norm on the concrete tensor
factor `K_v ⊗[K] L` used by relative ideles.  Consequently its image is
the chosen open local norm subgroup from `LocalNormApproximation`.

The finite component of every global relative-idele norm therefore lies
in that subgroup, and its corresponding local quotient class is one.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

open LocalClassFieldTheory


open AlgebraicNumberTheory.Valuations
open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- Base change of the first tensor factor gives the concrete tensor
algebra at `v`. -/
noncomputable def finitePlaceLocalTensorAlgEquiv
    (v : HeightOneSpectrum (𝓞 K)) :
    LocalTensorAlgebra (L := L)
        (NumberField.HeightOneSpectrum.adicAbv K v) ≃ₐ[K]
      v.adicCompletion K ⊗[K] L :=
  Algebra.TensorProduct.congr
    (finitePlaceCompletionAlgEquiv v)
    (AlgEquiv.refl : L ≃ₐ[K] L)

/-- The induced equivalence on tensor-algebra unit groups. -/
noncomputable def finitePlaceLocalTensorUnitsEquiv
    (v : HeightOneSpectrum (𝓞 K)) :
    (LocalTensorAlgebra (L := L)
      (NumberField.HeightOneSpectrum.adicAbv K v))ˣ ≃*
      (v.adicCompletion K ⊗[K] L)ˣ :=
  Units.mapEquiv
    (finitePlaceLocalTensorAlgEquiv
      (K := K) (L := L) v).toMulEquiv

omit [NumberField L] [IsGalois K L] in
/-- The completed-base comparison intertwines the two determinant norm
maps. -/
theorem finitePlaceLocalTensorNorm_commutes
    (v : HeightOneSpectrum (𝓞 K))
    (z :
      (LocalTensorAlgebra (L := L)
        (NumberField.HeightOneSpectrum.adicAbv K v))ˣ) :
    finitePlaceCompletionUnitsContinuousMulEquiv v
        (localTensorDetNorm
          (K := K) (L := L)
          (NumberField.HeightOneSpectrum.adicAbv K v) z) =
      _root_.localTensorNorm
        (K := K) (L := L) v
        (finitePlaceLocalTensorUnitsEquiv
          (K := K) (L := L) v z) := by
  apply Units.ext
  exact
    _root_.map_norm_tensorProduct_baseChange
      (K := K) (L := L)
      (finitePlaceCompletionAlgEquiv v).toAlgHom
      (z : LocalTensorAlgebra (L := L)
        (NumberField.HeightOneSpectrum.adicAbv K v))

omit [NumberField L] [IsGalois K L] in
/-- Before choosing a localization, the concrete determinant-norm
image is the transport of the absolute-value tensor norm image. -/
theorem finitePlaceLocalTensorNorm_range_eq_transport
    (v : HeightOneSpectrum (𝓞 K)) :
    (_root_.localTensorNorm
        (K := K) (L := L) v).range =
      (localTensorNormSubgroup
        (K := K) (L := L)
        (NumberField.HeightOneSpectrum.adicAbv K v)).map
          (finitePlaceCompletionUnitsContinuousMulEquiv
            v).toMonoidHom := by
  let T :=
    finitePlaceLocalTensorUnitsEquiv
      (K := K) (L := L) v
  let e :=
    finitePlaceCompletionUnitsContinuousMulEquiv v
  ext x
  constructor
  · rintro ⟨z, hz⟩
    refine
      ⟨localTensorDetNorm
          (K := K) (L := L)
          (NumberField.HeightOneSpectrum.adicAbv K v)
          (T.symm z),
        ⟨T.symm z, rfl⟩, ?_⟩
    calc
      e
          (localTensorDetNorm
            (K := K) (L := L)
            (NumberField.HeightOneSpectrum.adicAbv K v)
            (T.symm z)) =
          _root_.localTensorNorm
            (K := K) (L := L) v
            (T (T.symm z)) :=
        finitePlaceLocalTensorNorm_commutes
          (K := K) (L := L) v (T.symm z)
      _ =
          _root_.localTensorNorm
            (K := K) (L := L) v z := by
        rw [T.apply_symm_apply]
      _ = x := hz
  · rintro ⟨y, ⟨z, hz⟩, hy⟩
    refine ⟨T z, ?_⟩
    calc
      _root_.localTensorNorm
          (K := K) (L := L) v (T z) =
          e
            (localTensorDetNorm
              (K := K) (L := L)
              (NumberField.HeightOneSpectrum.adicAbv K v) z) :=
        (finitePlaceLocalTensorNorm_commutes
          (K := K) (L := L) v z).symm
      _ = e y := congrArg e hz
      _ = x := hy
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_FinitePlaceTensorBlock
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.scaledRelativeIntegerLatticeQuotientFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite-place tensor factors as induced local blocks

This file is the finite-place counterpart of
`InfinitePlaceTensorBlock`.  It compares the concrete completion
`K_v` used by the idele restricted product with the absolute-value
completion used by the canonical local tensor decomposition, and records equivariance for
conjugation on the second tensor factor.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

open LocalClassFieldTheory


open AlgebraicNumberTheory.Valuations
open HilbertRamification

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

section Equivariance

variable
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L)

attribute [local instance] finitePlaceScalarTensorUnitsAction
local instance finitePlaceLocalTensorUnitsAction :
    MulDistribMulAction
      (L ≃ₐ[K] L)
      (LocalTensorAlgebra (L := L)
        (HeightOneSpectrum.adicAbv K v))ˣ :=
  localTensorUnitsAction
    (K := K) (L := L)
    (HeightOneSpectrum.adicAbv K v)

end Equivariance
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Ramification_Splitting_FinitePlace
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.scaledRelativeIntegerLatticeQuotientFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Decomposition groups and complete splitting at finite places

For a finite Galois extension of number fields `L / K`, this file
attaches an actual decomposition subgroup to every finite place of
`K`.  The extension of the adic absolute value is the one constructed
in `LocalNormApproximation`; no place above `v` is supplied as an
additional hypothesis.

The stabilizer is identified with the automorphism group of the algebraic
localization. The finite-localization theorem supplies finite dimensionality,
so the order of
the decomposition group is exactly the local degree.  Consequently
complete splitting is equivalent both to cardinality one and to local
degree one.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The local degree at `v`, defined using the actual algebraic
localization selected above. -/
noncomputable def finitePlaceLocalDegree
    (v : HeightOneSpectrum (𝓞 K)) : ℕ := by
  let vK :=
    NumberField.HeightOneSpectrum.adicAbv K v
  let w :=
    chosenFinitePlaceExtension (L := L) v
  letI hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  exact
    Module.finrank vK.Completion
      (LocalizedCompletion vK w)

/-- The decomposition-group localization equivalence together with the finite-localization theorem
the finite-localization theorem: the order of the decomposition group equals the local
degree. -/
theorem finitePlaceDecompositionGroup_card_eq_localDegree
    (v : HeightOneSpectrum (𝓞 K)) :
    Nat.card
        (finitePlaceDecompositionGroup
          (K := K) (L := L) v) =
      finitePlaceLocalDegree
        (K := K) (L := L) v := by
  let vK :=
    NumberField.HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let w :=
    chosenFinitePlaceExtension (L := L) v
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let :=
    localizedCompletionGlobalAlgebra vK w
  let :=
    localizedCompletionIsScalarTower vK w
  let E :=
    LocalizedCompletion vK w
  let : FiniteDimensional vK.Completion E :=
    localizedCompletionModuleFinite vK hvK w
  let : IsGalois vK.Completion E :=
    HilbertRamification.algebraicLocalization_isGalois vK w
  calc
    Nat.card
        (finitePlaceDecompositionGroup
          (K := K) (L := L) v) =
        Nat.card
          (E ≃ₐ[vK.Completion] E) :=
      Nat.card_congr
        (decompositionGroupEquivAlgebraicLocalizationAut
          vK hvK w).toEquiv
    _ = Module.finrank vK.Completion E :=
      IsGalois.card_aut_eq_finrank
        vK.Completion E
    _ = finitePlaceLocalDegree
        (K := K) (L := L) v := rfl

section Quotient

/-- The image of the finite-place decomposition subgroup in a group
quotient.  In the Galois correspondence this is the decomposition
group in the corresponding intermediate extension. -/
noncomputable def finitePlaceDecompositionGroupInQuotient
    (v : HeightOneSpectrum (𝓞 K))
    (P : Subgroup (L ≃ₐ[K] L))
    [P.Normal] :
    Subgroup ((L ≃ₐ[K] L) ⧸ P) :=
  (finitePlaceDecompositionGroup
    (K := K) (L := L) v).map
      (QuotientGroup.mk' P)

omit [FiniteDimensional K L] in
/-- The quotient decomposition group is trivial exactly when the
original decomposition group is contained in the quotient kernel. -/
theorem finitePlaceDecompositionGroupInQuotient_eq_bot_iff
    (v : HeightOneSpectrum (𝓞 K))
    (P : Subgroup (L ≃ₐ[K] L))
    [P.Normal] :
    finitePlaceDecompositionGroupInQuotient
        (K := K) (L := L) v P = ⊥ ↔
      finitePlaceDecompositionGroup
          (K := K) (L := L) v ≤ P := by
  rw [finitePlaceDecompositionGroupInQuotient,
    Subgroup.map_eq_bot_iff,
    QuotientGroup.ker_mk']

end Quotient
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Galois_CyclicPrimeSubextension
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.finiteNormalClosure_isGalois
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.completionProductUnitsEquivRightCosets_apply_coe _root_.LocalClassFieldTheory.conjugateCompletionRingEquiv_toCompletion _root_.LocalClassFieldTheory.conjugateExtensionCompletionRingEquiv_toCompletion _root_.LocalClassFieldTheory.localTensorEvaluation_tmul _root_.LocalClassFieldTheory.mem_decompositionRightCosetsFinset _root_.LocalClassFieldTheory.rightCosetCompletionUnitsEquiv_apply_coe _root_.LocalClassFieldTheory.rightCosetExtensionEquiv_apply _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The prime-degree subextension of a cyclic prime-power extension

This file constructs a prime-degree intermediate field.
For a nontrivial cyclic Galois extension whose group has order
`p ^ exponent`, the index-`p` subgroup constructed in
`SplittingGroupTheory` is sent through the finite Galois
correspondence.  Its fixed field is an actual cyclic Galois extension
of the base of degree `p`.

The finite-place decomposition group in that subextension is obtained
by restricting the decomposition group of `L / K`.  Thus complete
splitting descends to the prime-degree subextension, and nonsplitting
there ascends to `L`.
-/

open scoped NumberField Classical IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open HilbertRamification

section ValuationRestriction

variable {F E : Type}
    [Field F] [Field E] [Algebra F E]

/-- For a normal subextension represented by a field type, its
decomposition group is the restriction image of the decomposition
group upstairs.

The reverse inclusion uses valuation-extension counting over the subextension: a
lift of a valuation-preserving automorphism is corrected by an
automorphism fixing that field. -/
theorem absoluteValueDecompositionGroup_map_restrictNormalHom
    {M : Type*}
    [Field M] [Algebra F M] [Algebra M E]
    [IsScalarTower F M E]
    [IsGalois F E]
    [Normal F M]
    (vF : AbsoluteValue F ℝ)
    (hvF : vF.IsNontrivial)
    (w : AbsoluteValueExtension vF E) :
    (absoluteValueDecompositionGroup F w.1).map
        (AlgEquiv.restrictNormalHom
          (F := F) (K₁ := E) M) =
      absoluteValueDecompositionGroup F
        (w.1.comp (f := algebraMap M E)
          (algebraMap M E).injective) := by
  let : IsGalois M E :=
    IsGalois.tower_top_of_isGalois F M E
  let vM : AbsoluteValueExtension vF M :=
    { val :=
        w.1.comp (f := algebraMap M E)
          (algebraMap M E).injective
      property := by
        intro x
        change
          w.1 (algebraMap M E (algebraMap F M x)) =
            vF x
        rw [← IsScalarTower.algebraMap_apply F M E]
        exact w.2 x }
  let q :=
    AlgEquiv.restrictNormalHom
      (F := F) (K₁ := E) M
  ext τ
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    change
      ∀ x : E,
        w.1 (σ x) < 1 ↔ w.1 x < 1
      at hσ
    change
      ∀ x : M,
        vM.1 ((q σ) x) < 1 ↔
          vM.1 x < 1
    intro x
    have hleft :
        vM.1 ((q σ) x) =
          w.1 (σ (algebraMap M E x)) := by
      change
        w.1 (algebraMap M E ((q σ) x)) =
          w.1 (σ (algebraMap M E x))
      exact congrArg w.1
        (AlgEquiv.restrictNormal_commutes
          σ M x)
    have hright :
        vM.1 x = w.1 (algebraMap M E x) :=
      rfl
    rw [hleft, hright]
    exact hσ (algebraMap M E x)
  · intro hτ
    obtain ⟨σ : E ≃ₐ[F] E, hσ⟩ :=
      (AlgEquiv.restrictNormalHom_surjective
        (F := F) (K₁ := M) (E := E)) τ
    have hτext :
        absoluteValueExtensionConjugate
            vF vM τ = vM :=
      (mem_absoluteValueDecompositionGroup_iff_extensionConjugate_eq
        vF hvF vM τ).mp hτ
    let wSigma :
        AbsoluteValueExtension vM.1 E :=
      { val :=
          absoluteValueConjugate w.1 σ
        property := by
          intro x
          calc
            w.1 (σ (algebraMap M E x)) =
                vM.1 ((q σ) x) := by
              change
                w.1 (σ (algebraMap M E x)) =
                  w.1 (algebraMap M E ((q σ) x))
              exact congrArg w.1
                (AlgEquiv.restrictNormal_commutes
                  σ M x).symm
            _ = vM.1 (τ x) := by
              rw [hσ]
            _ = vM.1 x := by
              have hx :=
                congrArg
                  (fun e :
                    AbsoluteValueExtension vF M =>
                      e.1 x)
                  hτext
              exact hx }
    let wOverM : AbsoluteValueExtension vM.1 E :=
      { val := w.1
        property := by
          intro x
          rfl }
    let hvM : vM.1.IsNontrivial := by
      rcases hvF with ⟨a, ha, hva⟩
      refine
        ⟨algebraMap F M a,
          (map_ne_zero (algebraMap F M)).2 ha, ?_⟩
      simpa only [vM.2 a] using hva
    obtain ⟨ηM, hηM⟩ :=
      absoluteValueConjugacy vM.1 hvM
        wOverM wSigma
    let η : E ≃ₐ[F] E :=
      ηM.restrictScalars F
    have hqη : q η = 1 := by
      apply AlgEquiv.ext
      intro x
      apply (algebraMap M E).injective
      calc
        algebraMap M E ((q η) x) =
            η (algebraMap M E x) :=
          AlgEquiv.restrictNormal_commutes
            η M x
        _ = algebraMap M E x :=
          ηM.commutes x
    let δ : E ≃ₐ[F] E :=
      σ * η⁻¹
    have hδ :
        δ ∈ absoluteValueDecompositionGroup F w.1 := by
      change
        ∀ x : E,
          w.1 (δ x) < 1 ↔
            w.1 x < 1
      intro x
      have hx :=
        congrArg
          (fun e : AbsoluteValueExtension vM.1 E =>
            e.1 (ηM⁻¹ x))
          hηM
      change
        w.1 (σ (ηM⁻¹ x)) =
          w.1 (ηM (ηM⁻¹ x))
        at hx
      have hvalue :
          w.1 (δ x) = w.1 x := by
        simpa [δ, η] using hx
      rw [hvalue]
    refine ⟨δ, hδ, ?_⟩
    change q δ = τ
    rw [show δ = σ * η⁻¹ from rfl,
      map_mul, map_inv, hqη, inv_one,
      mul_one, hσ]

end ValuationRestriction

section ValuationRestriction

variable {F E : Type}
    [Field F] [Field E] [Algebra F E]

/-- Triviality of a decomposition group is preserved when the chosen
extension is conjugated. -/
theorem absoluteValueDecompositionGroup_conjugate_eq_bot
    (vF : AbsoluteValue F ℝ)
    (w : AbsoluteValueExtension vF E)
    (ρ : E ≃ₐ[F] E)
    (hbot :
      absoluteValueDecompositionGroup F w.1 = ⊥) :
    absoluteValueDecompositionGroup F
        (absoluteValueExtensionConjugate
          vF w ρ).1 = ⊥ := by
  apply le_bot_iff.mp
  intro τ hτ
  rw [Subgroup.mem_bot]
  change
    ∀ x : E,
      w.1 (ρ (τ x)) < 1 ↔
        w.1 (ρ x) < 1
    at hτ
  let δ : E ≃ₐ[F] E :=
    ρ * τ * ρ⁻¹
  have hδ :
      δ ∈ absoluteValueDecompositionGroup F w.1 := by
    change
      ∀ x : E,
        w.1 (δ x) < 1 ↔
          w.1 x < 1
    intro x
    simpa [δ] using hτ (ρ⁻¹ x)
  have hδOne : δ = 1 :=
    Subgroup.mem_bot.mp (hbot ▸ hδ)
  have hconj :=
    congrArg (fun z : E ≃ₐ[F] E =>
      ρ⁻¹ * z * ρ) hδOne
  simpa [δ, mul_assoc] using hconj

/-- For a Galois extension, triviality of the decomposition group is
independent of the chosen extension of the base absolute value. -/
theorem absoluteValueDecompositionGroup_eq_bot_independent_extension
    [IsGalois F E]
    (vF : AbsoluteValue F ℝ)
    (hvF : vF.IsNontrivial)
    (w w' : AbsoluteValueExtension vF E)
    (hbot :
      absoluteValueDecompositionGroup F w.1 = ⊥) :
    absoluteValueDecompositionGroup F w'.1 = ⊥ := by
  obtain ⟨ρ, hρ⟩ :=
    absoluteValueConjugacy vF hvF w w'
  rw [hρ]
  exact
    absoluteValueDecompositionGroup_conjugate_eq_bot
      vF w ρ hbot

end ValuationRestriction

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)]

/-- The decomposition subgroup in the constructed subextension,
obtained by restricting the decomposition subgroup in `L / K`. -/
noncomputable def cyclicPrimeSubextensionDecompositionGroup
    {p exponent : ℕ}
    (hp : p.Prime)
    (hexponent : 0 < exponent)
    (hcard :
      Nat.card (L ≃ₐ[K] L) =
        p ^ exponent)
    (v : HeightOneSpectrum (𝓞 K)) :
    Subgroup
      (cyclicPrimeSubextension
          (K := K) (L := L)
          hp hexponent hcard ≃ₐ[K]
        cyclicPrimeSubextension
          (K := K) (L := L)
          hp hexponent hcard) := by
  let M :=
    cyclicPrimeSubextension
      (K := K) (L := L)
      hp hexponent hcard
  letI : IsGalois K M :=
    cyclicPrimeSubextension_isGalois
      (K := K) (L := L)
      hp hexponent hcard
  exact
    (finitePlaceDecompositionGroup
      (K := K) (L := L) v).map
        (AlgEquiv.restrictNormalHom M)

omit [NumberField L] in
/-- The restricted decomposition group agrees with the quotient
decomposition group transported by the fixed-field Galois
correspondence. -/
theorem cyclicPrimeSubextensionDecompositionGroup_eq_quotient_image
    {p exponent : ℕ}
    (hp : p.Prime)
    (hexponent : 0 < exponent)
    (hcard :
      Nat.card (L ≃ₐ[K] L) =
        p ^ exponent)
    (v : HeightOneSpectrum (𝓞 K)) :
    cyclicPrimeSubextensionDecompositionGroup
        (K := K) (L := L)
        hp hexponent hcard v =
      (finitePlaceDecompositionGroupInQuotient
        (K := K) (L := L) v
        (cyclicPrimeIndexSubgroup
          (K := K) (L := L)
          hp hexponent hcard)).map
        (IsGalois.normalAutEquivQuotient
          (cyclicPrimeIndexSubgroup
            (K := K) (L := L)
            hp hexponent hcard)).toMonoidHom := by
  let P :=
    cyclicPrimeIndexSubgroup
      (K := K) (L := L)
      hp hexponent hcard
  let M :=
    cyclicPrimeSubextension
      (K := K) (L := L)
      hp hexponent hcard
  let : P.Normal :=
    cyclicPrimeIndexSubgroup_normal
      (K := K) (L := L)
      hp hexponent hcard
  let : IsGalois K M :=
    cyclicPrimeSubextension_isGalois
      (K := K) (L := L)
      hp hexponent hcard
  change
    (finitePlaceDecompositionGroup
      (K := K) (L := L) v).map
        (AlgEquiv.restrictNormalHom M) =
      ((finitePlaceDecompositionGroup
        (K := K) (L := L) v).map
          (QuotientGroup.mk' P)).map
        (IsGalois.normalAutEquivQuotient P).toMonoidHom
  rw [Subgroup.map_map]
  congr 1
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_NormApproximation_InfinitePlaces
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Archimedean norm approximation

This file supplies the archimedean source used in the norm-approximation
argument. At a real place the positive units have
an `n`-th root, while at a complex place every unit has one.  Consequently
the standard positive subgroup is contained in the determinant-norm image
of every scalar extension of positive degree.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain
open LocalFieldTheory

noncomputable section

open LocalClassFieldTheory

universe u v

section ArchimedeanNorm

variable {K : Type u} [Field K] [NumberField K]

omit [NumberField K] in
/-- Every element of the archimedean positive subgroup has an `n`-th
root for `n > 0`.  At complex places the positivity condition is
vacuous and algebraic closedness supplies the root. -/
theorem exists_infinitePositiveSubgroup_nthRoot
    (v : InfinitePlace K)
    (n : ℕ) (hn : 0 < n)
    (x : v.Completionˣ)
    (hx : x ∈ RayClass.infinitePositiveSubgroup v) :
    ∃ y : v.Completionˣ, y ^ n = x := by
  by_cases hv : v.IsReal
  · let e : v.Completion ≃+* ℝ :=
      InfinitePlace.Completion.ringEquivRealOfIsReal hv
    let eu : v.Completionˣ ≃* ℝˣ :=
      Units.mapEquiv e.toMulEquiv
    have hxpos : 0 < ((eu x : ℝˣ) : ℝ) := by
      exact
        ((RayClass.mem_infinitePositiveSubgroup_iff v x).mp hx) hv
    let yr : ℝ :=
      ((eu x : ℝˣ) : ℝ) ^ ((n : ℝ)⁻¹)
    have hyrpow :
        yr ^ n = ((eu x : ℝˣ) : ℝ) := by
      exact Real.rpow_inv_natCast_pow hxpos.le hn.ne'
    have hyrne : yr ≠ 0 := by
      intro hyr
      rw [hyr, zero_pow hn.ne'] at hyrpow
      exact (eu x).ne_zero hyrpow.symm
    let yu : ℝˣ := Units.mk0 yr hyrne
    refine ⟨eu.symm yu, ?_⟩
    apply eu.injective
    simp only [map_pow, eu.apply_symm_apply]
    apply Units.ext
    exact hyrpow
  · have hvc : v.IsComplex :=
      InfinitePlace.not_isReal_iff_isComplex.mp hv
    let e : v.Completion ≃+* ℂ :=
      InfinitePlace.Completion.ringEquivComplexOfIsComplex hvc
    let eu : v.Completionˣ ≃* ℂˣ :=
      Units.mapEquiv e.toMulEquiv
    obtain ⟨z, hz⟩ :=
      IsAlgClosed.exists_pow_nat_eq
        ((eu x : ℂˣ) : ℂ) hn
    have hz0 : z ≠ 0 := by
      intro hzero
      rw [hzero, zero_pow hn.ne'] at hz
      exact (eu x).ne_zero hz.symm
    let zu : ℂˣ := Units.mk0 z hz0
    refine ⟨eu.symm zu, ?_⟩
    apply eu.injective
    simp only [map_pow, eu.apply_symm_apply]
    apply Units.ext
    exact hz

variable {L : Type v} [Field L] [Algebra K L]
    [FiniteDimensional K L]

/-- The positive subgroup at an infinite place lies in the determinant
norm image of the corresponding local tensor algebra. -/
theorem infinitePositiveSubgroup_le_infiniteTensorNormSubgroup
    (v : InfinitePlace K) :
    RayClass.infinitePositiveSubgroup v ≤
      infiniteTensorNormSubgroup (K := K) (L := L) v := by
  intro x hx
  let n := Module.finrank K L
  have hn : 0 < n :=
    Module.finrank_pos
  obtain ⟨y, hy⟩ :=
    exists_infinitePositiveSubgroup_nthRoot
      v n hn x hx
  let z : (v.Completion ⊗[K] L)ˣ :=
    Units.map
      (algebraMap v.Completion
        (v.Completion ⊗[K] L)).toMonoidHom y
  refine ⟨z, ?_⟩
  apply Units.ext
  change
    Algebra.norm v.Completion
        (algebraMap v.Completion
          (v.Completion ⊗[K] L)
          (y : v.Completion)) =
      (x : v.Completion)
  rw [Algebra.norm_algebraMap,
    Module.finrank_baseChange]
  exact congrArg Units.val hy

end ArchimedeanNorm
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_IdeleClassPowerLocalUnitQuotient_ArchimedeanPowerIndex
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

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

omit [NumberField K] in
/-- If the exponent is even, or the place is complex, every local
`n`-th power is positive in the archimedean sense. -/
theorem nthPowerSubgroup_le_infinitePositiveSubgroup
    (n : ℕ+)
    (w : InfinitePlace K)
    (harch : Even (n : ℕ) ∨ ¬ w.IsReal) :
    (powMonoidHom (n : ℕ) :
        w.Completionˣ →* w.Completionˣ).range ≤
      RayClass.infinitePositiveSubgroup w := by
  intro x hx
  obtain ⟨y, hy⟩ :=
    (MonoidHom.mem_range
      (G := w.Completionˣ)).mp hx
  rw [powMonoidHom_apply] at hy
  subst x
  rw [RayClass.mem_infinitePositiveSubgroup_iff]
  intro hw
  rcases harch with hnEven | hwNotReal
  · rcases hnEven with ⟨m, hm⟩
    let emb :=
      NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
    have hyne : emb (y : w.Completion) ≠ 0 := by
      intro hzero
      apply y.ne_zero
      apply emb.injective
      simp at hzero
    change 0 < emb (((y ^ (n : ℕ) : w.Completionˣ) : w.Completion))
    rw [Units.val_pow_eq_pow_val, map_pow, hm, pow_add, ← pow_two]
    exact sq_pos_of_ne_zero (pow_ne_zero m hyne)
  · exact False.elim (hwNotReal hw)

omit [NumberField K] in
/-- The positive subgroup at a real infinite place is exactly the kernel
of the sign homomorphism. -/
theorem realInfinitePlaceSignHom_ker
    (w : InfinitePlace K)
    (hw : w.IsReal) :
    (realInfinitePlaceSignHom w hw).ker =
      RayClass.infinitePositiveSubgroup w := by
  ext x
  change
    realInfinitePlaceSignHom w hw x = 1 ↔
      x ∈ RayClass.infinitePositiveSubgroup w
  rw [RayClass.mem_infinitePositiveSubgroup_iff]
  constructor
  · intro hx hw'
    have hxval := congrArg Units.val hx
    have hxsign :
        SignType.sign
          (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
            hw (x : w.Completion)) =
          1 := by
      simpa [realInfinitePlaceSignHom] using hxval
    have hproof : hw' = hw := Subsingleton.elim _ _
    subst hproof
    exact sign_eq_one_iff.mp hxsign
  · intro hx
    have hxsign :
        SignType.sign
            (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
              hw (x : w.Completion)) =
          1 :=
      sign_eq_one_iff.mpr (hx hw)
    apply Units.ext
    simpa [realInfinitePlaceSignHom] using hxsign

/-- The quotient by positive units at a real place is its two-element
sign group. -/
noncomputable def realInfinitePositiveQuotientEquivSign
    (w : InfinitePlace K)
    (hw : w.IsReal) :
    w.Completionˣ ⧸ RayClass.infinitePositiveSubgroup w ≃*
      SignTypeˣ := by
  rw [← realInfinitePlaceSignHom_ker w hw]
  exact
    QuotientGroup.quotientKerEquivOfSurjective
      (realInfinitePlaceSignHom w hw)
      (realInfinitePlaceSignHom_surjective w hw)

omit [NumberField K] in
/-- The positive-unit quotient at a real place has order two. -/
theorem card_realInfinitePositiveQuotient
    (w : InfinitePlace K)
    (hw : w.IsReal) :
    Nat.card
        (w.Completionˣ ⧸
          RayClass.infinitePositiveSubgroup w) =
      2 := by
  calc
    Nat.card
        (w.Completionˣ ⧸
          RayClass.infinitePositiveSubgroup w) =
        Nat.card SignTypeˣ :=
      Nat.card_congr
        (realInfinitePositiveQuotientEquivSign w hw).toEquiv
    _ = 2 := by
      rw [Nat.card_eq_fintype_card]
      decide

omit [NumberField K] in
/-- In the even-real or complex cases, the local power subgroup is
exactly the usual archimedean positive subgroup. -/
theorem nthPowerSubgroup_eq_infinitePositiveSubgroup
    (n : ℕ+)
    (w : InfinitePlace K)
    (harch : Even (n : ℕ) ∨ ¬ w.IsReal) :
    (powMonoidHom (n : ℕ) :
        w.Completionˣ →* w.Completionˣ).range =
      RayClass.infinitePositiveSubgroup w := by
  apply le_antisymm
  · exact
      nthPowerSubgroup_le_infinitePositiveSubgroup
        n w harch
  · intro x hx
    obtain ⟨y, hy⟩ :=
      _root_.exists_infinitePositiveSubgroup_nthRoot
        w (n : ℕ) n.pos x hx
    exact
      (MonoidHom.mem_range
        (G := w.Completionˣ)).mpr ⟨y, by
          rw [powMonoidHom_apply]
          exact hy⟩

omit [NumberField K] in
/-- At a real place an odd power map on local units is surjective. -/
theorem nthPowerSubgroup_eq_top_of_real_odd
    (n : ℕ+)
    (w : InfinitePlace K)
    (hw : w.IsReal)
    (hn : Odd (n : ℕ)) :
    (powMonoidHom (n : ℕ) :
        w.Completionˣ →* w.Completionˣ).range =
      ⊤ := by
  apply top_unique
  intro x hx
  apply
    (MonoidHom.mem_range
      (G := w.Completionˣ)).mpr
  let emb :=
    NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
  have hx0 : emb (x : w.Completion) ≠ 0 := by
    intro hzero
    apply x.ne_zero
    simp at hzero
  by_cases hxpos : 0 < emb (x : w.Completion)
  · have hxPositive :
        x ∈ RayClass.infinitePositiveSubgroup w := by
      rw [RayClass.mem_infinitePositiveSubgroup_iff]
      intro hw'
      have hproof : hw' = hw := Subsingleton.elim _ _
      subst hproof
      exact hxpos
    obtain ⟨y, hy⟩ :=
      _root_.exists_infinitePositiveSubgroup_nthRoot
        w (n : ℕ) n.pos x hxPositive
    exact ⟨y, by
      rw [powMonoidHom_apply]
      exact hy⟩
  · have hxneg : emb (x : w.Completion) < 0 :=
      lt_of_le_of_ne (le_of_not_gt hxpos) hx0
    have hnegPositive :
        -x ∈ RayClass.infinitePositiveSubgroup w := by
      rw [RayClass.mem_infinitePositiveSubgroup_iff]
      intro hw'
      have hproof : hw' = hw := Subsingleton.elim _ _
      subst hproof
      change 0 < emb ((-x : w.Completionˣ) : w.Completion)
      simp [hxneg]
    obtain ⟨y, hy⟩ :=
      _root_.exists_infinitePositiveSubgroup_nthRoot
        w (n : ℕ) n.pos (-x) hnegPositive
    refine ⟨-y, ?_⟩
    rw [powMonoidHom_apply, hn.neg_pow, hy]
    simp

omit [NumberField K] in
/-- The archimedean factor in the local power-index product: it is `2`
exactly for an even exponent at a real place, and `1` otherwise. -/
theorem card_infinitePlace_nthPowerQuotient
    (n : ℕ+)
    (w : InfinitePlace K) :
    Nat.card
        (w.Completionˣ ⧸
          (powMonoidHom (n : ℕ) :
            w.Completionˣ →* w.Completionˣ).range) =
      if w.IsReal ∧ Even (n : ℕ) then 2 else 1 := by
  classical
  by_cases hw : w.IsReal
  · by_cases hn : Even (n : ℕ)
    · rw [
        nthPowerSubgroup_eq_infinitePositiveSubgroup
          n w (Or.inl hn)]
      simpa [hw, hn] using
        card_realInfinitePositiveQuotient w hw
    · have hodd : Odd (n : ℕ) :=
        (Nat.even_or_odd (n : ℕ)).resolve_left hn
      rw [nthPowerSubgroup_eq_top_of_real_odd n w hw hodd]
      let :
          Subsingleton
            (w.Completionˣ ⧸ (⊤ : Subgroup w.Completionˣ)) :=
        QuotientGroup.subsingleton_quotient_top
      simp [hw, hn]
  · have hpower :
        (powMonoidHom (n : ℕ) :
            w.Completionˣ →* w.Completionˣ).range =
          RayClass.infinitePositiveSubgroup w :=
      nthPowerSubgroup_eq_infinitePositiveSubgroup
        n w (Or.inr hw)
    have hpositive :
        RayClass.infinitePositiveSubgroup w = ⊤ := by
      ext x
      simp [RayClass.mem_infinitePositiveSubgroup_iff, hw]
    rw [hpower, hpositive]
    let :
        Subsingleton
          (w.Completionˣ ⧸ (⊤ : Subgroup w.Completionˣ)) :=
      QuotientGroup.subsingleton_quotient_top
    simp [hw]


end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_Unramified_Cohomology
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Tate cohomology of units in unramified extensions

For an unramified extension of local fields the actual low-degree Tate
cohomology of the integer units and of every principal-unit group is trivial.
The norm statements are the corresponding actual norm surjections.
-/

noncomputable section

universe u

namespace LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField
open CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand

/-- Quotient map in the actual short exact sequence
`1 → U_L^n → 𝒪_Lˣ → 𝒪_Lˣ/U_L^n → 1`. -/
def integerUnitsPrincipalUnitsQuotientMap
    (L : Type u) [Field L] [ValuativeRel L] (n : Nat) :
    𝒪[L]ˣ →* IntegerUnitsModPrincipalUnitsAtLevel L n :=
  integerUnitsModPrincipalUnitsAtLevelMk L n

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_RamificationInvariants
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotCommGroup _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Canonical ramification invariants

The ramification index and residue degree are the ideal-theoretic invariants of
the chosen valuation rings.  Every theorem below is stated directly in the
ambient valued-extension context; there are no compatibility aliases or
extension-marker arguments.
-/

noncomputable section

universe u v w x

namespace LocalFieldTheory.DiscreteValuationField

open ValuationTheory.DiscreteValuationField

namespace ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

variable [FiniteDimensional K L]

/--
Establishes the identity `ValuationTheory.DiscreteValuationField.ValuedExtension.degree base.toDVF
target.toDVF = ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex base.toDVF
target.toDVF * ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree base.toDVF
target.toDVF`.
-/
theorem degree_eq_ramificationIndex_mul_residueDegree_of_finite_separable
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    ValuationTheory.DiscreteValuationField.ValuedExtension.degree
        base.toDVF target.toDVF =
      ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
          base.toDVF target.toDVF *
        ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
          base.toDVF target.toDVF :=
  (ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex_mul_residueDegree_eq_degree_of_finite_separable
      base target).symm

end ValuedExtension
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_RamificationIdeal
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotCommGroup _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.coe_valuationSubringUnitFieldUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_coord _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotLift_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_map_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerFieldHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltration_subgroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModPrincipalUnitEquivOfPreserves_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitEquivOfPreserves_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.zero_eq_top _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Ramification ideals in finite complete-DVF extensions

This file records the ideal-theoretic source behind the local-field structure theory.
The base maximal ideal maps to the `e`-th power of the target maximal ideal, where
`e` is the canonical ramification index.  Every statement is expressed directly
in the ambient valued-extension context; no extension marker is involved.
-/

noncomputable section

universe u v w x

namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField
namespace ValuedExtension
open ValuationTheory.DiscreteValuationField.ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

/-- The image of a base uniformizer generates the `e`-th target maximal-ideal
power. -/
theorem span_base_uniformizer_image_eq_target_maximalIdeal_pow_ramificationIndex
    {ϖ : base.valuationSubring}
    (hϖ : base.valuation.IsUniformizer (ϖ : K)) :
    Ideal.span ({integerMap base.toDVF target.toDVF ϖ} :
        Set target.valuationSubring) =
      target.maximalIdeal ^ ramificationIndex base.toDVF target.toDVF := by
  calc
    Ideal.span ({integerMap base.toDVF target.toDVF ϖ} :
        Set target.valuationSubring) =
        Ideal.map (integerMap base.toDVF target.toDVF)
          (Ideal.span ({ϖ} : Set base.valuationSubring)) := by
      rw [Ideal.map_span, Set.image_singleton]
    _ = Ideal.map (integerMap base.toDVF target.toDVF) base.maximalIdeal := by
      rw [base.maximalIdeal_eq_span_uniformizer hϖ]
    _ = target.maximalIdeal ^ ramificationIndex base.toDVF target.toDVF :=
      maximalIdeal_map_eq_target_maximalIdeal_pow_ramificationIndex base target

/-- The image of a base uniformizer lies in the `e`-th target maximal-ideal
power. -/
theorem base_uniformizer_image_mem_target_maximalIdeal_pow_ramificationIndex
    {ϖ : base.valuationSubring}
    (hϖ : base.valuation.IsUniformizer (ϖ : K)) :
    integerMap base.toDVF target.toDVF ϖ ∈
      target.maximalIdeal ^ ramificationIndex base.toDVF target.toDVF := by
  rw [← span_base_uniformizer_image_eq_target_maximalIdeal_pow_ramificationIndex
    base target hϖ]
  exact Ideal.mem_span_singleton_self (integerMap base.toDVF target.toDVF ϖ)

/-- The image of a base uniformizer is a unit multiple of the `e`-th power of
any target uniformizer. -/
theorem exists_unit_mul_target_uniformizer_pow_eq_base_uniformizer_image
    {ϖ : base.valuationSubring} {π : target.valuationSubring}
    (hϖ : base.valuation.IsUniformizer (ϖ : K))
    (hπ : target.valuation.IsUniformizer (π : L)) :
    ∃ u : target.valuationSubringˣ,
      integerMap base.toDVF target.toDVF ϖ =
        (u : target.valuationSubring) *
          π ^ ramificationIndex base.toDVF target.toDVF := by
  have hspan :
      Ideal.span ({integerMap base.toDVF target.toDVF ϖ} :
          Set target.valuationSubring) =
        target.maximalIdeal ^ ramificationIndex base.toDVF target.toDVF :=
    span_base_uniformizer_image_eq_target_maximalIdeal_pow_ramificationIndex
      base target hϖ
  have hx_mem :
      integerMap base.toDVF target.toDVF ϖ ∈
        target.maximalIdeal ^ ramificationIndex base.toDVF target.toDVF :=
    base_uniformizer_image_mem_target_maximalIdeal_pow_ramificationIndex
      base target hϖ
  rcases
      (target.mem_maximalIdeal_pow_iff_uniformizer_pow_dvd hπ
        (ramificationIndex base.toDVF target.toDVF)).1 hx_mem with
    ⟨u, hu⟩
  have hu_unit : IsUnit u := by
    by_contra hnot_unit
    have hu_mem : u ∈ target.maximalIdeal := by
      by_contra hnot_mem
      exact hnot_unit ((IsLocalRing.notMem_maximalIdeal (x := u)).1 hnot_mem)
    have hπpow_mem :
        π ^ ramificationIndex base.toDVF target.toDVF ∈
          target.maximalIdeal ^ ramificationIndex base.toDVF target.toDVF := by
      rw [target.maximalIdeal_pow_eq_span_uniformizer_pow hπ
        (ramificationIndex base.toDVF target.toDVF)]
      exact Ideal.mem_span_singleton_self
        (π ^ ramificationIndex base.toDVF target.toDVF)
    have hx_deep :
        integerMap base.toDVF target.toDVF ϖ ∈
          target.maximalIdeal ^
            (ramificationIndex base.toDVF target.toDVF + 1) := by
      rw [hu]
      have hmul :
          π ^ ramificationIndex base.toDVF target.toDVF * u ∈
            target.maximalIdeal ^ ramificationIndex base.toDVF target.toDVF *
              target.maximalIdeal :=
        Ideal.mul_mem_mul hπpow_mem hu_mem
      simpa [pow_succ] using hmul
    have hspan_le :
        Ideal.span ({integerMap base.toDVF target.toDVF ϖ} :
            Set target.valuationSubring) ≤
          target.maximalIdeal ^
            (ramificationIndex base.toDVF target.toDVF + 1) := by
      rw [Ideal.span_le]
      intro y hy
      have hy_eq : y = integerMap base.toDVF target.toDVF ϖ := by
        simpa using hy
      simpa [hy_eq] using hx_deep
    exact target_maximalIdeal_pow_not_le_pow_succ target hπ
      (ramificationIndex base.toDVF target.toDVF)
      (by simpa [hspan] using hspan_le)
  rcases hu_unit with ⟨uunit, huunit⟩
  refine ⟨uunit, ?_⟩
  simpa [huunit, mul_comm] using hu

end ValuedExtension
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_ArchimedeanNormQuotient
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The real/complex norm quotient

At a ramified infinite place the local extension is `ℂ/ℝ`.  Its norm
subgroup consists exactly of the positive real units, so the sign map
identifies the norm quotient with `ℤˣ`, a group of order two.
-/

open LocalFieldTheory
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

noncomputable section

namespace LocalClassFieldTheory

universe u v w z

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open NumberField
open scoped Classical NumberField.LiesOver

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- An infinite place above another one, written in the absolute-value
extension format used by the algebraic-localization API. -/
def infinitePlaceAbsoluteValueExtension
    (v : InfinitePlace K) (w : InfinitePlace L)
    (hw : w.comap (algebraMap K L) = v) :
    AbsoluteValueExtension v.1 L :=
  ⟨w.1, fun x =>
    congrArg
      (fun q : InfinitePlace K => q.1 x) hw⟩

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Cohomology_CyclicPrimePowerFullDecomposition
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Full decomposition places in cyclic prime-power extensions

This file proves the infinitude of full-decomposition places in cyclic
prime-power extensions.  For a cyclic group of prime-power order, every
proper subgroup is contained in the
chosen subgroup of index `p`.  Consequently every finite place whose
decomposition group is proper splits completely in the chosen
degree-`p` subextension.

The second part records the idelic approximation argument: if all
finite places outside a finite set split completely, then the idele
class norm is surjective.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section

open RelativeIdeleGroup.Cohomology

namespace GlobalClassFieldTheory
namespace Cohomology

open AlgebraicNumberTheory.Valuations
open HilbertRamification

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)]

omit [NumberField L] in
/-- A proper decomposition group in the original cyclic
prime-power extension becomes trivial in the chosen degree-`p`
subextension. -/
theorem
    cyclicPrimeSubextensionDecompositionGroup_eq_bot_of_ne_top
    {p exponent : ℕ}
    (hp : p.Prime)
    (hexponent : 0 < exponent)
    (hcard : Nat.card (L ≃ₐ[K] L) = p ^ exponent)
    (v : HeightOneSpectrum (𝓞 K))
    (hproper :
      finitePlaceDecompositionGroup
          (K := K) (L := L) v ≠ ⊤) :
    cyclicPrimeSubextensionDecompositionGroup
        (K := K) (L := L)
        hp hexponent hcard v = ⊥ := by
  let P :=
    cyclicPrimeIndexSubgroup
      (K := K) (L := L)
      hp hexponent hcard
  let : P.Normal :=
    cyclicPrimeIndexSubgroup_normal
      (K := K) (L := L)
      hp hexponent hcard
  have hDP :
      finitePlaceDecompositionGroup
          (K := K) (L := L) v ≤ P :=
    subgroup_le_index_prime_subgroup_of_ne_top_cyclic_prime_power
      hp hcard P
      (finitePlaceDecompositionGroup
        (K := K) (L := L) v)
      (cyclicPrimeIndexSubgroup_index
        (K := K) (L := L)
        hp hexponent hcard)
      hproper
  have hquot :
      finitePlaceDecompositionGroupInQuotient
          (K := K) (L := L) v P = ⊥ :=
    (finitePlaceDecompositionGroupInQuotient_eq_bot_iff
      (K := K) (L := L) v P).2 hDP
  rw [
    cyclicPrimeSubextensionDecompositionGroup_eq_quotient_image
      (K := K) (L := L) hp hexponent hcard v,
    hquot]
  exact Subgroup.map_bot _

end Cohomology
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.KummerTheory_Concrete_SUnitPreparation_FullSUnitKummerExtension
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

/-- The extension `N = K(√[n]{Kˢ})` is finite-dimensional. -/
theorem fullSUnitKummerExtension_finiteDimensional
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    FiniteDimensional K
      (fullSUnitKummerExtension
        (K := K) (Omega := Omega) n S) := by
  let E :=
    fullSUnitKummerExtension (K := K) (Omega := Omega) n S
  let _ : IsGalois K E :=
    fullSUnitKummerExtension_isGalois
      (K := K) (Omega := Omega) n S
  let _ : Finite Gal(E/K) :=
    finite_fullSUnitKummerExtension_galois
      (K := K) (Omega := Omega) n hn hmu S
  exact IsGalois.finiteDimensional_of_finite K E

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PrincipalUnitPadicAction_FiniteQuotientPadicModule
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageClassInQuotient_normal _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageSubgroup_normal _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_principalUnitSubquotientEquivClassInQuotient_map _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_quotientModuloFiltrationPreimageClassEquivRange_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_quotientModuloFiltrationPreimageClassEquivRange_mk_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.mapLevelOfMapsFiltrationLevels_apply _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.mem_filtrationPreimageSubgroup_iff _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.principalUnitGradedPieceMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.principalUnitSubquotientMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientMapOfMapsFiltrationLevels_apply_mk' _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_mk_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict_mk _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# P-adic modules on finite principal-unit quotients

Finite principal-unit quotients have the expected residue-characteristic exponent.
Reduction of p-adic integers therefore supplies canonical module structures, compatible with
the transition maps.
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

/-! ## The finite-coordinate p-adic actions -/

/-- A wrapped level quotient has the expected local-field cardinality
`p^(f*n)`. -/
theorem card_discretePrincipalUnitQuotient_eq_residueCharacteristic_pow
    (F : LocalField.{u, v} K) (n : ℕ) :
    Nat.card (DiscretePrincipalUnitQuotient F.toCompleteDVF n) =
      F.residueCharacteristic ^ ((principalUnitResidueDegree F : ℕ) * n) := by
  rw [show
    Nat.card (DiscretePrincipalUnitQuotient F.toCompleteDVF n) =
        Nat.card
          (Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n)) by
    exact
      Nat.card_congr
        (DiscretePrincipalUnitQuotient.equiv F.toCompleteDVF n)]
  calc
    Nat.card
        (Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n)) =
        Nat.card
          (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) :=
      Nat.card_congr Additive.toMul
    _ = F.residueCharacteristic ^
        ((principalUnitResidueDegree F : ℕ) * n) :=
      Internal.card_principalUnitQuotientCarrier_eq_residueCharacteristic_pow F n

/-- The exact exponent bound, stated on the canonical discrete wrapper. -/
theorem discretePrincipalUnitQuotient_nsmul_residueCharacteristic_pow_eq_zero
    (F : LocalField.{u, v} K) (n : ℕ)
    (x : DiscretePrincipalUnitQuotient F.toCompleteDVF n) :
    (F.residueCharacteristic ^
        ((principalUnitResidueDegree F : ℕ) * n)) • x = 0 := by
  apply (DiscretePrincipalUnitQuotient.addEquiv F.toCompleteDVF n).injective
  simpa only [map_nsmul, map_zero,
    DiscretePrincipalUnitQuotient.addEquiv_apply] using
    Internal.principalUnitQuotientCarrier_nsmul_residueCharacteristic_pow_eq_zero
      F n x.val

/-- Joint continuity of the p-adic scalar action on one finite discrete
coordinate. -/
theorem Internal.continuous_principalUnitQuotientCarrierPadicScalar
    (F : LocalField.{u, v} K) (n : ℕ) :
    letI : TopologicalSpace
        (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) := ⊥
    Continuous fun z : ℤ_[F.residueCharacteristic] ×
        Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) =>
      principalUnitQuotientCarrierPadicScalar F n z.1 z.2 := by
  let p := F.residueCharacteristic
  let f : ℕ := principalUnitResidueDegree F
  let : TopologicalSpace
      (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) := ⊥
  let : DiscreteTopology
      (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) := ⟨rfl⟩
  let : TopologicalSpace (ZMod (p ^ (f * n))) := ⊥
  let : DiscreteTopology (ZMod (p ^ (f * n))) := ⟨rfl⟩
  let : Module (ZMod (p ^ (f * n)))
      (Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n)) := by
    simpa [p, f] using principalUnitQuotientCarrierZModModule F n
  have hred : Continuous fun z : ℤ_[F.residueCharacteristic] ×
      Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) =>
      PadicInt.toZModPow (f * n) z.1 :=
    (Internal.continuous_padicIntToZModPow p (f * n)).comp continuous_fst
  have hact : Continuous fun z : ZMod (p ^ (f * n)) ×
      Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) =>
      z.1 • z.2 :=
    continuous_of_discreteTopology
  change Continuous fun z : ℤ_[F.residueCharacteristic] ×
      Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) =>
    PadicInt.toZModPow (f * n) z.1 • z.2
  exact hact.comp (hred.prodMk continuous_snd)

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField
end
end


