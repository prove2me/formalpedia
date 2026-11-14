-- Prove2me | Definitions.Def_OAIQ244Duke033
-- name    : OAIQ244Duke033
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:34:00.93562+00:00
-- url     : https://prove2.me/theorems/e2b2cc59-223b-4d92-aab1-d09bf7189688
-- title:
--   Definitions bundle OAIQ244Duke033 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 64 declarations of OpenAI's Lean: 23 definitions, 1 inductive type or structure and 40 theorems. The definitions and types are `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicTorsionRestrictionEquiv`, `KummerTheory.ProfiniteUnitDecomposition.Internal.gatherFree`, `KummerTheory.primeCyclotomicPushoutAlgebra`, `KummerTheory.primeCyclotomicPushoutField`, `KummerTheory.primeCyclotomicPushoutGalEquivPiZMod`, `KummerTheory.rationalCyclotomicCharacter`, `KummerTheory.rationalCyclotomicCharacterContinuousMulEquiv`, `KummerTheory.torsionQuotientEquivOfZHatMulDecomposition`, `LocalClassFieldTheory.G`, `LocalClassFieldTheory.absoluteGalois`, `LocalClassFieldTheory.absoluteGalois`, `LocalClassFieldTheory.absoluteUnits`, `LocalClassFieldTheory.abstractBase`, `LocalClassFieldTheory.abstractBase`, `LocalFieldTheory.localIntegerValuationSubringEquiv`, `LubinTate.LubinTateSeries`, `LubinTate.SameUniformizer.Approximation`, `LubinTate.SameUniformizer.Intertwines`, `LubinTate.SameUniformizer.defect`, `LubinTate.SameUniformizer.inVariable`, `LubinTate.SameUniformizer.linearInVariable`, `LubinTate.SameUniformizer.linearInVariableStabilization`, `LubinTate.standardLubinTatePowerSeries`, `rootsOfUnityEquivSUnitTorsion`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Idele_ClassGroup_Tower`, `AlgebraicNumberTheory_Idele_SPlaces`, `AlgebraicNumberTheory_SUnit_Herbrand`, `GlobalClassFieldTheory_Reciprocity_CyclotomicTorsionFixedField`, `KummerTheory_Concrete_CyclotomicPrimeBaseChange`, `Kummer_Concrete_Cyclotomic_ProfiniteUnitDecomposition_Gather`, `Kummer_Concrete_Cyclotomic_ProfiniteUnitDecomposition_TorsionQuotientEquiv`, `Kummer_Concrete_Cyclotomic_ProfiniteUnitDecomposition_TorsionQuotientMk`, `Kummer_Concrete_Cyclotomic_RationalCyclotomicCharacter`, `Kummer_Concrete_Cyclotomic_RationalCyclotomicCharacterEquiv`, `Kummer_Concrete_SimpleExtension`, `LocalClassFieldTheory_Finite_LocalReciprocity_IntermediateFieldNormResidueNaturality`, `LocalClassFieldTheory_Finite_LocalReciprocity_ResidueAlgebraicClosureDegree`, `LocalClassFieldTheory_Finite_LocalReciprocity_UnramifiedComparison`, `LocalClassFieldTheory_Finite_LocalReciprocity_UnramifiedNormalization`, `LocalField_NonarchimedeanLocalField_NormalizedIntegerValuation`, `LocalField_Padic_UnitDecomposition`, `LubinTate_FormalModule_DegreeStabilization`, `LubinTate_FormalModule_Intertwiner`, `LubinTate_FormalModule_RecursiveCorrection`, `LubinTate_FormalModule_RecursiveIntertwiner`, `LubinTate_FormalModule_Reduction`, `LubinTate_FormalModule_Series`, `LubinTate_FormalModule_StandardSeries`, `Ramification_Different`, `Valuation_DiscreteValuationField_Basic`, `Valuation_DiscreteValuationField_Complete`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke015`, `OAIQ244Duke016`, `OAIQ244Duke017`, `OAIQ244Duke018`, `OAIQ244Duke019`, `OAIQ244Duke020` and `OAIQ244Duke021` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke038`, `OAIQ244Duke042`, `OAIQ244Duke043` and `OAIQ244Duke044`.
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
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.LinearDisjoint
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
import Mathlib.GroupTheory.Torsion
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
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
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
import Mathlib.RingTheory.DedekindDomain.Different
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
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPowerSeries.Expand
import Mathlib.RingTheory.MvPowerSeries.Order
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.MvPowerSeries.Trunc
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Polynomial.ContentIdeal
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Substitution
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
import Definitions.Def_OAIQ244Duke015
import Definitions.Def_OAIQ244Duke016
import Definitions.Def_OAIQ244Duke017
import Definitions.Def_OAIQ244Duke018
import Definitions.Def_OAIQ244Duke019
import Definitions.Def_OAIQ244Duke020
import Definitions.Def_OAIQ244Duke021

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_ClassGroup_Tower
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.principalQuotientAction _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

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

section NormQuotientSequence

attribute [local instance] instIsMulCommutativeTowerRelativeIdeleGroup
attribute [local instance] instIsMulCommutativeClassGroup
attribute [local instance] instIsMulCommutativeIdeleClassGroup
omit [NumberField M] [NumberField L] [Algebra K L] [IsScalarTower K M L] in
/-- Exactness of the concrete tower norm-quotient sequence. -/
theorem intermediateToCompositeNormQuotient_range_eq_ker :
    MonoidHom.range
        (intermediateToCompositeNormQuotient K M L) =
      MonoidHom.ker
        (compositeToBaseNormQuotient K M L) := by
  ext q
  constructor
  · rintro ⟨a, rfl⟩
    refine QuotientGroup.induction_on a ?_
    intro c
    change
      QuotientGroup.mk'
          (RelativeIdeleGroup.classNorm K M).range
          (RelativeIdeleGroup.classNorm K M c) = 1
    exact
      (QuotientGroup.eq_one_iff
        (RelativeIdeleGroup.classNorm K M c)).2 ⟨c, rfl⟩
  · intro hq
    refine QuotientGroup.induction_on q ?_ hq
    intro c hc
    change
      QuotientGroup.mk'
          (RelativeIdeleGroup.classNorm K M).range c = 1
      at hc
    have hcRange :
        c ∈ (RelativeIdeleGroup.classNorm K M).range :=
      (QuotientGroup.eq_one_iff c).1 hc
    obtain ⟨d, rfl⟩ := hcRange
    refine
      ⟨QuotientGroup.mk'
          (TowerRelativeIdeleGroup.classNorm K M L).range d,
        ?_⟩
    rfl

omit [NumberField M] [NumberField L] [Algebra K L] [IsScalarTower K M L] in
/-- The last map in the tower norm-quotient sequence is onto. -/
theorem compositeToBaseNormQuotient_surjective :
    Function.Surjective
      (compositeToBaseNormQuotient K M L) := by
  intro q
  refine QuotientGroup.induction_on q ?_
  intro c
  exact
    ⟨QuotientGroup.mk'
        (towerCompositeClassNorm K M L).range c,
      rfl⟩

omit [NumberField M] [NumberField L] [Algebra K L] [IsScalarTower K M L] in
/-- Cardinal bound supplied by the actual right-exact tower sequence:

`#(C_K / N_{L/K}C_L) ≤
  #(C_M / N_{L/M}C_L) · #(C_K / N_{M/K}C_M)`.

Only finiteness of the two outer quotients is required; finiteness of
the middle quotient is constructed from exactness. -/
theorem towerCompositeClassNormQuotient_card_le_mul
    [Finite (IntermediateClassNormQuotient K M L)]
    [Finite (RelativeIdeleGroup.ClassNormQuotient K M)] :
    Nat.card (TowerCompositeClassNormQuotient K M L) ≤
      Nat.card (IntermediateClassNormQuotient K M L) *
        Nat.card (RelativeIdeleGroup.ClassNormQuotient K M) := by
  let A := IntermediateClassNormQuotient K M L
  let B := TowerCompositeClassNormQuotient K M L
  let C := RelativeIdeleGroup.ClassNormQuotient K M
  let f : A →* B :=
    intermediateToCompositeNormQuotient K M L
  let g : B →* C :=
    compositeToBaseNormQuotient K M L
  let : Fintype A := Fintype.ofFinite A
  let : Fintype C := Fintype.ofFinite C
  let : Fintype B :=
    Group.fintypeOfKerEqRange f g
      (intermediateToCompositeNormQuotient_range_eq_ker
        K M L).symm
  have hg :
      Function.Surjective g :=
    compositeToBaseNormQuotient_surjective K M L
  have hquot :
      Nat.card (B ⧸ g.ker) = Nat.card C :=
    Nat.card_congr
      (QuotientGroup.quotientKerEquivOfSurjective
        g hg).toEquiv
  have hrange :
      Nat.card f.range ≤ Nat.card A :=
    Nat.card_le_card_of_surjective
      f.rangeRestrict
      f.rangeRestrict_surjective
  calc
    Nat.card B =
        Nat.card (B ⧸ g.ker) *
          Nat.card g.ker :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup
        g.ker
    _ = Nat.card C * Nat.card f.range := by
      rw [hquot,
        ← intermediateToCompositeNormQuotient_range_eq_ker
          K M L]
    _ ≤ Nat.card C * Nat.card A :=
      Nat.mul_le_mul_left (Nat.card C) hrange
    _ = Nat.card A * Nat.card C := Nat.mul_comm _ _

end NormQuotientSequence
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_SPlaces
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

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

namespace IdeleGroup

theorem supportedAt_mono {S T : Set (HeightOneSpectrum (𝓞 K))}
    (hST : S ⊆ T) :
    supportedAt (K := K) S ≤ supportedAt (K := K) T :=
  Subgroup.comap_mono
    (FiniteIdeleGroup.supportedAt_mono hST)

theorem supportedAt_empty :
    supportedAt (K := K)
      (∅ : Set (HeightOneSpectrum (𝓞 K))) =
      integralAtFinitePlaces (K := K) :=
  by
    ext a
    simp only [mem_supportedAt_iff, Set.mem_empty_iff_false,
      not_false_eq_true, forall_const]
    rfl

theorem isOpen_supportedAt
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IsOpen
      ((supportedAt (K := K) (S : Set _) :
        Subgroup (IdeleGroup K)) : Set (IdeleGroup K)) :=
  (FiniteIdeleGroup.isOpen_supportedAt S).preimage continuous_snd

end IdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_Basic
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply _root_.infinitePlace_mult_smul
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

/-- A uniformizer belongs to the maximal ideal but not to its square. -/
theorem uniformizer_not_mem_maximalIdeal_sq (F : DVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K)) :
    pi ∉ F.maximalIdeal ^ 2 := by
  simpa using F.uniformizer_pow_not_mem_maximalIdeal_pow_succ hpi 1

/-! ### Successive quotients of powers of the maximal ideal -/

end DVF
end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_Complete
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

end Valuation

namespace CompleteDVF

variable {K : Type u} [Field K]

/-- A uniformizer belongs to the maximal ideal but not to its square. -/
theorem uniformizer_not_mem_maximalIdeal_sq (F : CompleteDVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K)) :
    pi ∉ F.maximalIdeal ^ 2 :=
  F.toDVF.uniformizer_not_mem_maximalIdeal_sq hpi

end CompleteDVF
end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_ResidueAlgebraicClosureDegree
attribute [-instance] _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.adicCompletionProperSpace _root_.cyclicPrimeDegreeIntermediate_top_isGalois _root_.finiteLocalUnitsOpen _root_.primeOrderFixedField_isGalois _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.DegreeData.extensionNormalizedDegree_mk _root_.ClassFormation.DegreeData.fieldImageAdd_index _root_.ClassFormation.DegreeData.maximalUnramifiedDegreeEquiv_frobenius _root_.ClassFormation.DegreeData.maximalUnramifiedDegreeEquiv_mk _root_.ClassFormation.DegreeData.mem_maximalUnramifiedField_iff _root_.ClassFormation.DegreeData.normalizedDegree_apply_toAdd _root_.ClassFormation.DegreeData.restrictedDegreeInMulNatRange_coe _root_.ClassFormation.ValuationData.mem_unitAddSubgroup_iff _root_.ClassFormation.ValuationData.oneValue_coe _root_.ClassFormation.ValuationData.valuationAt_chosenPrimeElement _root_.ClassFormation.ValuationData.valuationAt_coe _root_.ClassFormation.ValuationData.valueModulo_apply _root_.ClassFormation.canonicalValueQuotientMap_mk _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.mem_nsmulImage_iff _root_.ClassFormation.nsmulImage_top _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatPowNat_apply_toAdd _root_.ClassFormation.zHatPowNat_one _root_.ClassFormation.zHatReductionMul_apply_toAdd _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
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

/-- Intrinsic residue degree is unchanged by simultaneous semilinear
equivalence of the finite residue base and its algebraic closure.  The
conjugate automorphism is written locally in the statement, so no parallel
restriction or automorphism-conjugation API is introduced. -/
theorem residueAbsoluteDegreeIn_semilinear_conjugation
    {k' : Type u} {Omega' : Type v}
    [Field k'] [Fintype k']
    [Field Omega'] [Algebra k' Omega']
    [Algebra.IsAlgebraic k' Omega'] [IsAlgClosed Omega']
    (tau : k ≃+* k') (e : Omega ≃+* Omega')
    (he : ∀ x : k,
      e (algebraMap k Omega x) = algebraMap k' Omega' (tau x))
    (sigma : Omega ≃ₐ[k] Omega) :
    let sigma' : Omega' ≃ₐ[k'] Omega' :=
      { e.symm.trans (sigma.toRingEquiv.trans e) with
        commutes' := fun x => by
          change e (sigma (e.symm (algebraMap k' Omega' x))) =
            algebraMap k' Omega' x
          have hpre :
              e.symm (algebraMap k' Omega' x) =
                algebraMap k Omega (tau.symm x) := by
            apply e.injective
            rw [e.apply_symm_apply, he, tau.apply_symm_apply]
          rw [hpre, sigma.commutes, he, tau.apply_symm_apply] }
    residueAbsoluteDegreeIn k' Omega' sigma' =
      residueAbsoluteDegreeIn k Omega sigma := by
  let conjugate (g : Omega ≃ₐ[k] Omega) :
      Omega' ≃ₐ[k'] Omega' :=
    AlgEquiv.ofRingEquiv
      (f := e.symm.trans (g.toRingEquiv.trans e)) (fun x => by
        change e (g (e.symm (algebraMap k' Omega' x))) =
          algebraMap k' Omega' x
        have hpre :
            e.symm (algebraMap k' Omega' x) =
              algebraMap k Omega (tau.symm x) := by
          apply e.injective
          rw [e.apply_symm_apply, he, tau.apply_symm_apply]
        rw [hpre, g.commutes, he, tau.apply_symm_apply])
  have conjugate_one : conjugate 1 = 1 := by
    apply AlgEquiv.ext
    intro x
    simp [conjugate]
  have conjugate_mul (g h : Omega ≃ₐ[k] Omega) :
      conjugate (g * h) = conjugate g * conjugate h := by
    apply AlgEquiv.ext
    intro x
    simp [conjugate, AlgEquiv.mul_apply]
  let conjugation :
      (Omega ≃ₐ[k] Omega) →* (Omega' ≃ₐ[k'] Omega') :=
    { toFun := conjugate
      map_one' := conjugate_one
      map_mul' := conjugate_mul }
  let conjugationContinuous :
      (Omega ≃ₐ[k] Omega) →ₜ* (Omega' ≃ₐ[k'] Omega') :=
    { toMonoidHom := conjugation
      continuous_toFun :=
        RamificationTheory.Field.absoluteGaloisGroup.semilinear_conjugation_continuous
          tau e he conjugation (fun _ => rfl) }
  let lhs : ZHatMul →ₜ* (Omega' ≃ₐ[k'] Omega') :=
    conjugationContinuous.comp (residueAbsoluteFrobenius k Omega)
  let rhs : ZHatMul →ₜ* (Omega' ≃ₐ[k'] Omega') :=
    residueAbsoluteFrobenius k' Omega'
  have hgenerator :
      lhs (Multiplicative.ofAdd (1 : ZHat)) =
        rhs (Multiplicative.ofAdd (1 : ZHat)) := by
    change conjugation
        (residueAbsoluteFrobenius k Omega
          (Multiplicative.ofAdd (1 : ZHat))) =
      residueAbsoluteFrobenius k' Omega'
        (Multiplicative.ofAdd (1 : ZHat))
    rw [residueAbsoluteFrobenius_one, residueAbsoluteFrobenius_one]
    apply AlgEquiv.ext
    intro x
    change e ((e.symm x) ^ Fintype.card k) =
      x ^ Fintype.card k'
    rw [map_pow, e.apply_symm_apply,
      Fintype.card_congr tau.toEquiv]
  let iota : Multiplicative ℤ →* ZHatMul :=
    AddMonoidHom.toMultiplicative
      (Int.castRingHom ZHat).toAddMonoidHom
  have hiota : DenseRange iota := by
    have hOfAdd :
        DenseRange (Multiplicative.ofAdd : ZHat → ZHatMul) :=
      (show Function.Surjective
          (Multiplicative.ofAdd : ZHat → ZHatMul) from
        fun x => ⟨Multiplicative.toAdd x, rfl⟩).denseRange
    have hCast :
        DenseRange
          (Multiplicative.ofAdd ∘ fun a : ℤ => (a : ZHat)) :=
      hOfAdd.comp denseRange_intCast_zHat continuous_id
    have hToAdd :
        DenseRange (Multiplicative.toAdd : Multiplicative ℤ → ℤ) :=
      (show Function.Surjective
          (Multiplicative.toAdd : Multiplicative ℤ → ℤ) from
        fun a => ⟨Multiplicative.ofAdd a, rfl⟩).denseRange
    simpa [iota, Function.comp_def] using
      hCast.comp hToAdd continuous_of_discreteTopology
  have hcomp :
      lhs.toMonoidHom.comp iota = rhs.toMonoidHom.comp iota := by
    apply MonoidHom.ext_mint
    simpa [iota] using hgenerator
  have heq (w : ZHatMul) : lhs w = rhs w := by
    have hfun :=
      hiota.equalizer lhs.continuous_toFun rhs.continuous_toFun <| by
        funext n
        exact DFunLike.congr_fun hcomp n
    exact congrFun hfun w
  let z := residueAbsoluteDegreeIn k Omega sigma
  have hz :
      conjugation (residueAbsoluteFrobenius k Omega z) =
        residueAbsoluteFrobenius k' Omega' z := by
    exact heq z
  apply (residueAbsoluteFrobeniusEquivIn k' Omega').injective
  change
    (residueAbsoluteFrobeniusEquivIn k' Omega')
        ((residueAbsoluteFrobeniusEquivIn k' Omega').symm
          (conjugation sigma)) =
      (residueAbsoluteFrobeniusEquivIn k' Omega')
        ((residueAbsoluteFrobeniusEquivIn k Omega).symm sigma)
  rw [(residueAbsoluteFrobeniusEquivIn k' Omega').apply_symm_apply]
  change conjugation sigma =
    residueAbsoluteFrobenius k' Omega' z
  have hsigma :
      sigma = residueAbsoluteFrobenius k Omega z := by
    change sigma =
      (residueAbsoluteFrobeniusEquivIn k Omega)
        ((residueAbsoluteFrobeniusEquivIn k Omega).symm sigma)
    exact
      ((residueAbsoluteFrobeniusEquivIn k Omega).apply_symm_apply sigma).symm
  exact (congrArg conjugation hsigma).trans hz

/-- Arithmetic Frobenius is compatible with changing the finite residue
base from `k` to a finite intermediate field `E`: after forgetting the
`E`-linear structure, the Frobenius coordinate is multiplied by
`[E : k]`. -/
theorem residueAbsoluteFrobenius_restrictScalars
    (E : IntermediateField k Omega) [FiniteDimensional k E]
    (z : ZHatMul) :
    letI : Finite E := Module.finite_of_finite k
    letI : Fintype E := Fintype.ofFinite E
    (residueAbsoluteFrobenius E Omega z).restrictScalars k =
      residueAbsoluteFrobenius k Omega
        (Multiplicative.ofAdd
          ((Module.finrank k E) • z.toAdd)) := by
  let : Finite E := Module.finite_of_finite k
  let : Fintype E := Fintype.ofFinite E
  let scaleHom : ZHatMul →* ZHatMul :=
    AddMonoidHom.toMultiplicative
      (zHatMulNat (Module.finrank k E)).toAddMonoidHom
  let scale : ZHatMul →ₜ* ZHatMul :=
    { toMonoidHom := scaleHom
      continuous_toFun :=
        continuous_ofAdd.comp
          ((zHatMulNat (Module.finrank k E)).continuous_toFun.comp
            continuous_toAdd) }
  let inclusion : (Omega ≃ₐ[E] Omega) →ₜ* (Omega ≃ₐ[k] Omega) :=
    { toMonoidHom := ofIntermediateFieldInExtension E
      continuous_toFun := ofIntermediateFieldInExtension_continuous E }
  let lhs : ZHatMul →ₜ* (Omega ≃ₐ[k] Omega) :=
    inclusion.comp (residueAbsoluteFrobenius E Omega)
  let rhs : ZHatMul →ₜ* (Omega ≃ₐ[k] Omega) :=
    (residueAbsoluteFrobenius k Omega).comp scale
  have hgenerator :
      lhs (Multiplicative.ofAdd (1 : ZHat)) =
        rhs (Multiplicative.ofAdd (1 : ZHat)) := by
    change
      (residueAbsoluteFrobenius E Omega
          (Multiplicative.ofAdd (1 : ZHat))).restrictScalars k =
        residueAbsoluteFrobenius k Omega
          (Multiplicative.ofAdd
            ((Module.finrank k E) • (1 : ZHat)))
    rw [residueAbsoluteFrobenius_one]
    have hscale :
        Multiplicative.ofAdd
            ((Module.finrank k E) • (1 : ZHat)) =
          (Multiplicative.ofAdd (1 : ZHat)) ^ Module.finrank k E := by
      apply Multiplicative.ext
      simp
    rw [hscale, map_pow, residueAbsoluteFrobenius_one]
    apply AlgEquiv.ext
    intro x
    change
      FiniteField.frobeniusAlgEquivOfAlgebraic E Omega x =
        (FiniteField.frobeniusAlgEquivOfAlgebraic k Omega ^
          Module.finrank k E) x
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic,
      AlgEquiv.coe_pow,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate,
      Module.card_eq_pow_finrank (K := k) (V := E)]
  let iota : Multiplicative ℤ →* ZHatMul :=
    AddMonoidHom.toMultiplicative
      (Int.castRingHom ZHat).toAddMonoidHom
  have hiota : DenseRange iota := by
    have hOfAdd :
        DenseRange (Multiplicative.ofAdd : ZHat → ZHatMul) :=
      (show Function.Surjective
          (Multiplicative.ofAdd : ZHat → ZHatMul) from
        fun x => ⟨Multiplicative.toAdd x, rfl⟩).denseRange
    have hCast :
        DenseRange
          (Multiplicative.ofAdd ∘ fun a : ℤ => (a : ZHat)) :=
      hOfAdd.comp denseRange_intCast_zHat continuous_id
    have hToAdd :
        DenseRange (Multiplicative.toAdd : Multiplicative ℤ → ℤ) :=
      (show Function.Surjective
          (Multiplicative.toAdd : Multiplicative ℤ → ℤ) from
        fun a => ⟨Multiplicative.ofAdd a, rfl⟩).denseRange
    simpa [iota, Function.comp_def] using
      hCast.comp hToAdd continuous_of_discreteTopology
  have hcomp :
      lhs.toMonoidHom.comp iota = rhs.toMonoidHom.comp iota := by
    apply MonoidHom.ext_mint
    simpa [iota] using hgenerator
  have heq (w : ZHatMul) : lhs w = rhs w := by
    have hfun :=
      hiota.equalizer lhs.continuous_toFun rhs.continuous_toFun <| by
        funext n
        exact DFunLike.congr_fun hcomp n
    exact congrFun hfun w
  exact heq z

/-- The intrinsic absolute residue degree has the corresponding
finite-base-change formula. -/
theorem residueAbsoluteDegreeIn_restrictScalars
    (E : IntermediateField k Omega) [FiniteDimensional k E]
    (sigma : Omega ≃ₐ[E] Omega) :
    letI : Finite E := Module.finite_of_finite k
    letI : Fintype E := Fintype.ofFinite E
    residueAbsoluteDegreeIn k Omega (sigma.restrictScalars k) =
      Multiplicative.ofAdd
        ((Module.finrank k E) •
          (residueAbsoluteDegreeIn E Omega sigma).toAdd) := by
  let : Finite E := Module.finite_of_finite k
  let : Fintype E := Fintype.ofFinite E
  apply (residueAbsoluteFrobeniusEquivIn k Omega).injective
  change
    (residueAbsoluteFrobeniusEquivIn k Omega)
        ((residueAbsoluteFrobeniusEquivIn k Omega).symm
          (sigma.restrictScalars k)) =
      (residueAbsoluteFrobeniusEquivIn k Omega)
        (Multiplicative.ofAdd
          ((Module.finrank k E) •
            ((residueAbsoluteFrobeniusEquivIn E Omega).symm sigma).toAdd))
  rw [(residueAbsoluteFrobeniusEquivIn k Omega).apply_symm_apply]
  change sigma.restrictScalars k =
    residueAbsoluteFrobenius k Omega
      (Multiplicative.ofAdd
        ((Module.finrank k E) •
          ((residueAbsoluteFrobeniusEquivIn E Omega).symm sigma).toAdd))
  rw [← residueAbsoluteFrobenius_restrictScalars]
  exact congrArg (fun g : Omega ≃ₐ[E] Omega => g.restrictScalars k)
    ((residueAbsoluteFrobeniusEquivIn E Omega).apply_symm_apply sigma).symm

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_SUnit_Herbrand
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The Herbrand quotient of the global S-unit group

This file computes the Herbrand quotient of the global `S`-unit group. It connects the actual
`S`-unit group to its logarithmic lattice, adds the invariant diagonal
integer direction, and combines the resulting exact sequences with the
permutation-lattice calculation.
-/

open scoped BigOperators Classical NumberField nonZeroDivisors Pointwise
open IsDedekindDomain Module

noncomputable section

open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

variable
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

section LogarithmicQuotient

/-- Ordinary roots of unity identify with the torsion subgroup of the
`S`-unit group. -/
noncomputable def rootsOfUnityEquivSUnitTorsion
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    NumberField.Units.torsion L ≃*
      CommGroup.torsion
        (SUnitGroup (K := L) S) :=
  ((NumberField.Units.torsion L).equivMapOfInjective
      (SUnitGroup.fromNumberFieldUnits (K := L) S)
      (SUnitGroup.fromNumberFieldUnits_injective
        (K := L) S)).trans
    (MulEquiv.subgroupCongr
      (SUnitGroup.torsion_eq_rootsOfUnity_range
        (K := L) S).symm)

/-- Torsion in an `S`-unit group over a number field is finite. -/
theorem sUnitTorsionFinite
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    Finite
      (CommGroup.torsion
        (SUnitGroup (K := L) S)) :=
  Finite.of_equiv
    (NumberField.Units.torsion L)
    (rootsOfUnityEquivSUnitTorsion L S).toEquiv

end LogarithmicQuotient
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Padic_UnitDecomposition
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseIsUltrametricDist _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Unit decomposition of the p-adic integers

This file constructs the reusable topological decomposition of
`ℤ_[p]ˣ` into its finite factor and its principal `p`-adic factor.
-/

open scoped Topology

noncomputable section

namespace LocalFieldTheory
namespace Padic

open scoped WithZero
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp

theorem padicDVRValued_uniformSpace_eq_standard
    (p : ℕ) [Fact p.Prime] :
    (Valued.mk' (padicDVRValuation p)).toUniformSpace =
      (inferInstance : UniformSpace ℚ_[p]) := by
  let v := padicDVRValuation p
  let standard : Valued ℚ_[p] NNReal :=
    NormedField.toValued
  let w : Valuation ℚ_[p] NNReal := standard.v
  have hvw : v.IsEquiv w := by
    apply Valuation.isEquiv_of_val_le_one
    intro x
    change v x ≤ 1 ↔ ‖x‖₊ ≤ 1
    rw [LocalField.padicDVRValuation_le_one_iff_norm_le_one]
    change
      (↑‖x‖₊ : ℝ) ≤ (↑(1 : NNReal) : ℝ) ↔ ‖x‖₊ ≤ 1
    exact NNReal.coe_le_coe
  have hmk :
      (Valued.mk' v).toUniformSpace =
        (Valued.mk' w).toUniformSpace := by
    apply le_antisymm
    · rw [le_iff_uniformContinuous_id]
      simpa using hvw.symm.uniformContinuous
    · rw [le_iff_uniformContinuous_id]
      simpa using hvw.uniformContinuous
  have hstandard :
      standard.toUniformSpace =
        (Valued.mk' w).toUniformSpace :=
    (@Valued.toUniformSpace_eq ℚ_[p] _ NNReal _ standard).trans
      (@Valued.toUniformSpace_eq ℚ_[p] _ NNReal _
        (Valued.mk' w)).symm
  exact hmk.trans hstandard.symm

end Padic
end LocalFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_Cyclotomic_ProfiniteUnitDecomposition_Gather
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ramificationQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.residueQuotientFinite _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Compiled free-coordinate gathering stage of the profinite-unit decomposition
-/

open scoped Topology

noncomputable section

namespace KummerTheory.ProfiniteUnitDecomposition.Internal

open ClassFormation
open LocalFieldTheory.Padic

/-- Reassemble the family of local additive coordinates into `ℤ̂`. -/
noncomputable def gatherFree :
    ((p : Nat.Primes) → Multiplicative ℤ_[p.1]) ≃ₜ*
      Multiplicative ZHat :=
  (continuousPiMultiplicative
      (fun p : Nat.Primes => ℤ_[p.1])).symm.trans
    (continuousMultiplicativeEquivOfAddEquiv
      zHatContinuousAddEquivPrimeProduct).symm

end KummerTheory.ProfiniteUnitDecomposition.Internal
end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_Cyclotomic_ProfiniteUnitDecomposition_TorsionQuotientEquiv
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ramificationQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.residueQuotientFinite _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup
attribute [-simp] _root_.ClassFormation.DegreeData.FiniteAbstractExtension.inertia_relIndex_eq_ramificationIndex _root_.ClassFormation.DegreeData.FiniteAbstractExtension.mapped_relIndex_eq_residueDegree _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ramificationIndex_coe _root_.ClassFormation.DegreeData.FiniteAbstractExtension.residueDegree_coe _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.DegreeData.extensionNormalizedDegree_mk _root_.ClassFormation.DegreeData.fieldImageAdd_index _root_.ClassFormation.DegreeData.maximalUnramifiedDegreeEquiv_frobenius _root_.ClassFormation.DegreeData.maximalUnramifiedDegreeEquiv_mk _root_.ClassFormation.DegreeData.mem_fieldInertiaWithin_iff _root_.ClassFormation.DegreeData.mem_fieldInertia_iff _root_.ClassFormation.DegreeData.mem_inertia_iff _root_.ClassFormation.DegreeData.mem_maximalUnramifiedField_iff _root_.ClassFormation.DegreeData.normalizedDegree_apply_toAdd _root_.ClassFormation.DegreeData.restrictedDegreeInMulNatRange_coe _root_.ClassFormation.DegreeData.restrictedDegree_apply _root_.ClassFormation.ValuationData.mem_unitAddSubgroup_iff _root_.ClassFormation.ValuationData.oneValue_coe _root_.ClassFormation.ValuationData.valuationAt_chosenPrimeElement _root_.ClassFormation.ValuationData.valuationAt_coe _root_.ClassFormation.ValuationData.valueModulo_apply _root_.ClassFormation.canonicalValueQuotientMap_mk _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.mem_nsmulImage_iff _root_.ClassFormation.nsmulImage_top _root_.ClassFormation.zHatPowNat_apply_toAdd _root_.ClassFormation.zHatPowNat_one _root_.ClassFormation.zHatReductionMul_apply_toAdd _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_apply _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_one _root_.LocalClassFieldTheory.residueAbsoluteDegreeIn_frobenius _root_.LocalClassFieldTheory.residueAbsoluteFrobenius_one _root_.LocalClassFieldTheory.residueFrobeniusToLimit_apply_component _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Torsion quotients of a profinite-integer product decomposition
-/

open scoped Topology

noncomputable section

namespace KummerTheory

open ClassFormation

/-- A topological decomposition `G ≃ ℤ̂ × T` with dense torsion in `T`
identifies the quotient of `G` by the closure of its torsion with `ℤ̂`. -/
noncomputable def torsionQuotientEquivOfZHatMulDecomposition
    (G T : Type*) [CommGroup G] [CommGroup T]
    [TopologicalSpace G] [TopologicalSpace T]
    [IsTopologicalGroup G] [IsTopologicalGroup T]
    [CompactSpace G]
    (E : G ≃ₜ* Multiplicative ZHat × T)
    (hT : Dense (CommGroup.torsion T : Set T)) :
    G ⧸ (CommGroup.torsion G).topologicalClosure ≃ₜ*
      Multiplicative ZHat := by
  let fstHom :
      Multiplicative ZHat × T →*
        Multiplicative ZHat :=
    MonoidHom.fst _ _
  let freePart : G →* Multiplicative ZHat :=
    fstHom.comp E.toMonoidHom
  have hpreTorsion :
      E ⁻¹'
          (CommGroup.torsion
              (Multiplicative ZHat × T) :
            Set (Multiplicative ZHat × T)) =
        (CommGroup.torsion G : Set G) := by
    ext x
    change IsOfFinOrder (E x) ↔ IsOfFinOrder x
    exact Function.Injective.isOfFinOrder_iff
      (f := E.toMonoidHom) E.injective
  have hpreClosure :
      E ⁻¹'
          closure
            (CommGroup.torsion
                (Multiplicative ZHat × T) :
              Set (Multiplicative ZHat × T)) =
        closure (CommGroup.torsion G : Set G) := by
    calc
      E ⁻¹'
          closure
            (CommGroup.torsion
                (Multiplicative ZHat × T) :
              Set (Multiplicative ZHat × T)) =
          closure
            (E ⁻¹'
              (CommGroup.torsion
                  (Multiplicative ZHat × T) :
                Set (Multiplicative ZHat × T))) :=
        E.toHomeomorph.preimage_closure _
      _ = closure (CommGroup.torsion G : Set G) := by
        rw [hpreTorsion]
  have hkerFst :
      fstHom.ker =
        (CommGroup.torsion
          (Multiplicative ZHat × T)).topologicalClosure := by
    rw [ClassFormation.topologicalClosure_torsion_zHatMul_prod T hT]
    ext x
    rcases x with ⟨x, y⟩
    change x = 1 ↔
      x ∈ (⊥ : Subgroup (Multiplicative ZHat)) ∧
        y ∈ (⊤ : Subgroup T)
    simp
  have hker :
      freePart.ker =
        (CommGroup.torsion G).topologicalClosure := by
    ext x
    change fstHom (E x) = 1 ↔
      x ∈ closure (CommGroup.torsion G : Set G)
    rw [← MonoidHom.mem_ker, hkerFst]
    exact Set.ext_iff.mp hpreClosure x
  have hsurj : Function.Surjective freePart := by
    intro z
    refine ⟨E.symm (z, 1), ?_⟩
    change fstHom (E (E.symm (z, 1))) = z
    rw [E.apply_symm_apply]
    rfl
  let e :
      G ⧸ (CommGroup.torsion G).topologicalClosure ≃*
        Multiplicative ZHat :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        freePart hsurj)
  exact
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.continuousMulEquivOfCompactToT2
        e
        (by
          rw [←
            QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff]
          exact continuous_fst.comp E.continuous_toFun)

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_Cyclotomic_ProfiniteUnitDecomposition_TorsionQuotientMk
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ramificationQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.residueQuotientFinite _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.DegreeData.FiniteAbstractExtension.inertia_relIndex_eq_ramificationIndex _root_.ClassFormation.DegreeData.FiniteAbstractExtension.mapped_relIndex_eq_residueDegree _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ramificationIndex_coe _root_.ClassFormation.DegreeData.FiniteAbstractExtension.residueDegree_coe _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.DegreeData.extensionNormalizedDegree_mk _root_.ClassFormation.DegreeData.fieldImageAdd_index _root_.ClassFormation.DegreeData.maximalUnramifiedDegreeEquiv_frobenius _root_.ClassFormation.DegreeData.maximalUnramifiedDegreeEquiv_mk _root_.ClassFormation.DegreeData.mem_fieldInertiaWithin_iff _root_.ClassFormation.DegreeData.mem_fieldInertia_iff _root_.ClassFormation.DegreeData.mem_inertia_iff _root_.ClassFormation.DegreeData.mem_maximalUnramifiedField_iff _root_.ClassFormation.DegreeData.normalizedDegree_apply_toAdd _root_.ClassFormation.DegreeData.restrictedDegreeInMulNatRange_coe _root_.ClassFormation.DegreeData.restrictedDegree_apply _root_.ClassFormation.ValuationData.mem_unitAddSubgroup_iff _root_.ClassFormation.ValuationData.oneValue_coe _root_.ClassFormation.ValuationData.valuationAt_chosenPrimeElement _root_.ClassFormation.ValuationData.valuationAt_coe _root_.ClassFormation.ValuationData.valueModulo_apply _root_.ClassFormation.canonicalValueQuotientMap_mk _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.mem_nsmulImage_iff _root_.ClassFormation.nsmulImage_top _root_.ClassFormation.zHatPowNat_apply_toAdd _root_.ClassFormation.zHatPowNat_one _root_.ClassFormation.zHatReductionMul_apply_toAdd _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_apply _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_one _root_.LocalClassFieldTheory.residueAbsoluteDegreeIn_frobenius _root_.LocalClassFieldTheory.residueAbsoluteFrobenius_one _root_.LocalClassFieldTheory.residueFrobeniusToLimit_apply_component _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Evaluation of the torsion-quotient equivalence
-/

open scoped Topology

noncomputable section

namespace KummerTheory

open ClassFormation

/-- The torsion-quotient equivalence evaluates a quotient class by
taking the genuine torsion-free coordinate of the chosen product
decomposition.  This is the commuting square needed to pass between an
actual cyclotomic character and the `ZHat`-coordinate of its torsion
fixed field. -/
@[simp]
theorem torsionQuotientEquivOfZHatMulDecomposition_mk
    (G T : Type*) [CommGroup G] [CommGroup T]
    [TopologicalSpace G] [TopologicalSpace T]
    [IsTopologicalGroup G] [IsTopologicalGroup T]
    [CompactSpace G]
    (E : G ≃ₜ* Multiplicative ZHat × T)
    (hT : Dense (CommGroup.torsion T : Set T))
    (g : G) :
    torsionQuotientEquivOfZHatMulDecomposition
        G T E hT (QuotientGroup.mk g) =
      (E g).1 := by
  rfl

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_Cyclotomic_RationalCyclotomicCharacter
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ramificationQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.residueQuotientFinite _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isAbelianGalois _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isGalois _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isIntegral _root_.KummerTheory.rationalCyclotomicTorsionFixedField_normal _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueCharacteristic.fact_prime _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The cyclotomic character of the rational cyclotomic field

This file assembles mathlib's `p`-adic cyclotomic characters of the
actual extension `rationalCyclotomicField / ℚ`.  Their product takes
values in the canonical product of the local unit groups, and the
topological Chinese-remainder equivalence identifies that product with
`ZHatˣ`.

No abstract copy of either the Galois group or its expected target is
introduced here.
-/

noncomputable section

namespace KummerTheory

open ClassFormation

attribute [local instance] KummerTheory.instFactPrimeValNat_solutions
/-- The rational cyclotomic character with its canonical profinite
integer-unit target. -/
noncomputable def rationalCyclotomicCharacter :
    (rationalCyclotomicField ≃ₐ[ℚ] rationalCyclotomicField) →ₜ* ZHatˣ :=
  (ContinuousMonoidHom.toContinuousMonoidHom
    zHatUnitsContinuousMulEquivPrimeProduct.symm).comp
      rationalCyclotomicCharacterPrimeProduct

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_Cyclotomic_RationalCyclotomicCharacterEquiv
attribute [-instance] _root_.AlgebraicNumberTheory.numberFieldInRationalSeparableClosure_numberField _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ramificationQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.residueQuotientFinite _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_isCyclotomic _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldNumberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isAbelianGalois _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isGalois _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isIntegral _root_.KummerTheory.rationalCyclotomicTorsionFixedField_normal _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_isGalois _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueCharacteristic.fact_prime _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.finiteNormalClosure_numberField _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.DegreeData.FiniteAbstractExtension.inertia_relIndex_eq_ramificationIndex _root_.ClassFormation.DegreeData.FiniteAbstractExtension.mapped_relIndex_eq_residueDegree _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ramificationIndex_coe _root_.ClassFormation.DegreeData.FiniteAbstractExtension.residueDegree_coe _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.DegreeData.extensionNormalizedDegree_mk _root_.ClassFormation.DegreeData.fieldImageAdd_index _root_.ClassFormation.DegreeData.maximalUnramifiedDegreeEquiv_frobenius _root_.ClassFormation.DegreeData.maximalUnramifiedDegreeEquiv_mk _root_.ClassFormation.DegreeData.mem_fieldInertiaWithin_iff _root_.ClassFormation.DegreeData.mem_fieldInertia_iff _root_.ClassFormation.DegreeData.mem_inertia_iff _root_.ClassFormation.DegreeData.mem_maximalUnramifiedField_iff _root_.ClassFormation.DegreeData.normalizedDegree_apply_toAdd _root_.ClassFormation.DegreeData.restrictedDegreeInMulNatRange_coe _root_.ClassFormation.DegreeData.restrictedDegree_apply _root_.ClassFormation.ValuationData.mem_unitAddSubgroup_iff _root_.ClassFormation.ValuationData.oneValue_coe _root_.ClassFormation.ValuationData.valuationAt_chosenPrimeElement _root_.ClassFormation.ValuationData.valuationAt_coe _root_.ClassFormation.ValuationData.valueModulo_apply _root_.ClassFormation.canonicalValueQuotientMap_mk _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.mem_nsmulImage_iff _root_.ClassFormation.nsmulImage_top _root_.ClassFormation.zHatPowNat_apply_toAdd _root_.ClassFormation.zHatPowNat_one _root_.ClassFormation.zHatReductionMul_apply_toAdd _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.torsionQuotientEquivOfZHatMulDecomposition_mk _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_apply _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_one _root_.LocalClassFieldTheory.residueAbsoluteDegreeIn_frobenius _root_.LocalClassFieldTheory.residueAbsoluteFrobenius_one _root_.LocalClassFieldTheory.residueFrobeniusToLimit_apply_component _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The rational cyclotomic character equivalence

Finite cyclotomic levels are detected by their prime-power reductions,
using mathlib's Chinese-remainder equivalence for `ZMod`.  Surjectivity
is obtained from the finite-intersection property for the closed fibers
of the restriction maps to those levels.
-/

noncomputable section

namespace KummerTheory

open ClassFormation

attribute [local instance] KummerTheory.instFactPrimeValNat_solutions_1
/-- The canonical rational cyclotomic character is injective. -/
theorem rationalCyclotomicCharacter_injective :
    Function.Injective rationalCyclotomicCharacter := by
  intro σ τ hστ
  apply rationalCyclotomicCharacterPrimeProduct_injective
  have h :=
    congrArg
      (fun u : ZHatˣ =>
        zHatUnitsContinuousMulEquivPrimeProduct u)
      hστ
  simpa [rationalCyclotomicCharacter] using h

/-- The canonical rational cyclotomic character is surjective. -/
theorem rationalCyclotomicCharacter_surjective :
    Function.Surjective rationalCyclotomicCharacter := by
  intro u
  let τ (n : ℕ+) :
      rationalCyclotomicLevel n ≃ₐ[ℚ]
        rationalCyclotomicLevel n :=
    (IsCyclotomicExtension.Rat.galEquivZMod
      (n : ℕ) (rationalCyclotomicLevel n)).symm
        (Units.map
          (zHatReductionRingHom (n : ℕ) n.2) u)
  let C (n : ℕ+) :
      Set
        (rationalCyclotomicField ≃ₐ[ℚ]
          rationalCyclotomicField) :=
    {σ |
      σ.restrictNormal (rationalCyclotomicLevel n) = τ n}
  have hclosed (n : ℕ+) : IsClosed (C n) := by
    let : FiniteDimensional ℚ (rationalCyclotomicLevel n) :=
      IsCyclotomicExtension.finiteDimensional
        {(n : ℕ)} ℚ (rationalCyclotomicLevel n)
    change IsClosed
      {σ :
          rationalCyclotomicField ≃ₐ[ℚ]
            rationalCyclotomicField |
        σ.restrictNormal (rationalCyclotomicLevel n) = τ n}
    refine @isClosed_eq
      (rationalCyclotomicLevel n ≃ₐ[ℚ]
        rationalCyclotomicLevel n)
      (rationalCyclotomicField ≃ₐ[ℚ]
        rationalCyclotomicField)
      inferInstance inferInstance krullTopology_t2
      _ _ ?_ ?_
    · exact
        InfiniteGalois.restrictNormalHom_continuous
          (k := ℚ) (K := rationalCyclotomicField)
          (rationalCyclotomicLevel n)
    · exact continuous_const
  have hfip (s : Finset ℕ+) :
      (⋂ n ∈ s, C n).Nonempty := by
    let N : ℕ+ :=
      ⟨∏ n ∈ s, (n : ℕ),
        Finset.prod_pos fun n _ => n.2⟩
    obtain ⟨σ, hσN⟩ :=
      (AlgEquiv.restrictNormalHom_surjective
        (F := ℚ)
        (K₁ := rationalCyclotomicLevel N)
        (E := rationalCyclotomicField)) (τ N)
    refine ⟨σ, ?_⟩
    rw [Set.mem_iInter₂]
    intro n hn
    have hnN : (n : ℕ) ∣ (N : ℕ) := by
      change
        (n : ℕ) ∣
          ∏ m ∈ s, (m : ℕ)
      exact
        Finset.dvd_prod_of_mem
          (fun m : ℕ+ => (m : ℕ)) hn
    let F := rationalCyclotomicLevel n
    let K := rationalCyclotomicLevel N
    have hFK : F ≤ K :=
      rationalCyclotomicLevel_mono hnN
    let algFK : Algebra F K :=
      RingHom.toAlgebra
        (IntermediateField.inclusion hFK).toRingHom
    let : SMul F K :=
      @Algebra.toSMul F K _ _ algFK
    let : Algebra F K := algFK
    let : IsScalarTower ℚ F K :=
      IsScalarTower.of_algebraMap_eq' rfl
    let : IsScalarTower ℚ F rationalCyclotomicField :=
      IsScalarTower.of_algebraMap_eq' rfl
    let : IsScalarTower ℚ K rationalCyclotomicField :=
      IsScalarTower.of_algebraMap_eq' rfl
    let : IsScalarTower F K rationalCyclotomicField :=
      IsScalarTower.of_algebraMap_eq' rfl
    have hτ :
        (AlgEquiv.restrictNormalHom F) (τ N) = τ n := by
      apply
        (IsCyclotomicExtension.Rat.galEquivZMod
          (n : ℕ) F).injective
      change
        IsCyclotomicExtension.Rat.galEquivZMod
            (n : ℕ) F ((τ N).restrictNormal F) =
          IsCyclotomicExtension.Rat.galEquivZMod
            (n : ℕ) F (τ n)
      rw [
        IsCyclotomicExtension.Rat.galEquivZMod_restrictNormal_apply
          (N : ℕ) K F hnN (τ N)]
      simp only [K, F, τ, MulEquiv.apply_symm_apply]
      apply Units.ext
      change
        ZMod.castHom hnN (ZMod (n : ℕ))
            (zHatReduction (N : ℕ) N.2 (u : ZHat)) =
          zHatReduction (n : ℕ) n.2 (u : ZHat)
      exact
        zHatReduction_transition
          n.2 N.2 hnN (u : ZHat)
    change σ.restrictNormal F = τ n
    calc
      σ.restrictNormal F =
          (AlgEquiv.restrictNormalHom F)
            ((AlgEquiv.restrictNormalHom K) σ) :=
        IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply F K σ
      _ = (AlgEquiv.restrictNormalHom F) (τ N) := by
        have hσN' :
            (AlgEquiv.restrictNormalHom K) σ = τ N := by
          simpa only [K] using hσN
        exact congrArg
          (AlgEquiv.restrictNormalHom F)
          hσN'
      _ = τ n := hτ
  obtain ⟨σ, hσ⟩ :=
    CompactSpace.iInter_nonempty hclosed hfip
  refine ⟨σ, ?_⟩
  apply zHatUnitsContinuousMulEquivPrimeProduct.injective
  change
    zHatUnitsContinuousMulEquivPrimeProduct
        (zHatUnitsContinuousMulEquivPrimeProduct.symm
          (rationalCyclotomicCharacterPrimeProduct σ)) =
      zHatUnitsContinuousMulEquivPrimeProduct u
  rw [
    zHatUnitsContinuousMulEquivPrimeProduct.apply_symm_apply]
  funext p
  apply Units.ext
  apply PadicInt.ext_of_toZModPow.mp
  intro k
  let n : ℕ+ :=
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩
  have hσn : σ ∈ C n :=
    Set.mem_iInter.mp hσ n
  change
    σ.restrictNormal (rationalCyclotomicLevel n) =
      τ n at hσn
  have hleft :=
    rationalCyclotomicCharacterPrimeProduct_toZModPow
      σ p k
  rw [hσn] at hleft
  change
    Units.map (PadicInt.toZModPow k).toMonoidHom
        (rationalCyclotomicCharacterPrimeProduct σ p) =
      (IsCyclotomicExtension.Rat.galEquivZMod
        (n : ℕ) (rationalCyclotomicLevel n))
        ((IsCyclotomicExtension.Rat.galEquivZMod
          (n : ℕ) (rationalCyclotomicLevel n)).symm
          (Units.map
            (zHatReductionRingHom (n : ℕ) n.2).toMonoidHom u))
      at hleft
  rw [MulEquiv.apply_symm_apply] at hleft
  have hright :
      Units.map (PadicInt.toZModPow k).toMonoidHom
          (zHatUnitsContinuousMulEquivPrimeProduct u p) =
        Units.map
          (zHatReductionRingHom
            (p.1 ^ k) (pow_pos p.2.pos k)) u := by
    apply Units.ext
    change
      PadicInt.toZModPow k
          (zHatUnitsContinuousMulEquivPrimeProduct u p :
            ℤ_[p.1]) =
        zHatReduction (p.1 ^ k)
          (pow_pos p.2.pos k) (u : ZHat)
    rw [
      zHatUnitsContinuousMulEquivPrimeProduct_coe_apply]
    simpa only [RingHom.comp_apply, zHatPadicReduction,
      zHatReductionRingHom_apply] using
      RingHom.congr_fun
        (toZModPow_zHatToPadicInt p k) (u : ZHat)
  exact
    congrArg
      (fun z : (ZMod (p.1 ^ k))ˣ =>
        (z : ZMod (p.1 ^ k)))
      (hleft.trans hright.symm)

/-- The canonical topological equivalence
`Gal(ℚ(μ∞)/ℚ) ≃ ℤ̂ˣ`. -/
noncomputable def rationalCyclotomicCharacterContinuousMulEquiv :
    (rationalCyclotomicField ≃ₐ[ℚ]
      rationalCyclotomicField) ≃ₜ* ZHatˣ :=
  let e :=
    MulEquiv.ofBijective
      rationalCyclotomicCharacter.toMonoidHom
      ⟨rationalCyclotomicCharacter_injective,
        rationalCyclotomicCharacter_surjective⟩
  ContinuousMulEquiv.mk'
    (rationalCyclotomicCharacter.continuous_toFun.homeoOfEquivCompactToT2
      (f := e.toEquiv))
    e.map_mul

/-- Evaluating the actual profinite-unit cyclotomic character at a
prime recovers the corresponding genuine `p`-adic cyclotomic
character. -/
@[simp]
theorem
    zHatUnitsContinuousMulEquivPrimeProduct_rationalCyclotomicCharacter
    (σ :
      rationalCyclotomicField ≃ₐ[ℚ]
        rationalCyclotomicField)
    (p : Nat.Primes) :
    zHatUnitsContinuousMulEquivPrimeProduct
        (rationalCyclotomicCharacterContinuousMulEquiv σ) p =
      rationalCyclotomicCharacterPrimeProduct σ p := by
  change
    zHatUnitsContinuousMulEquivPrimeProduct
        (rationalCyclotomicCharacter σ) p =
      rationalCyclotomicCharacterPrimeProduct σ p
  have h :=
    zHatUnitsContinuousMulEquivPrimeProduct.apply_symm_apply
      (rationalCyclotomicCharacterPrimeProduct σ)
  exact congrFun h p

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicTorsionFixedField
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.closedFixingSubgroup_normal _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_isGalois _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.ideleGroupIsTopologicalGroup _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The cyclotomic torsion fixed field

`rationalCyclotomicField` now denotes the actual field `ℚ(μ∞)` inside
`SeparableClosure ℚ`.  Its actual Galois group is therefore the standard
mathlib type
`rationalCyclotomicField ≃ₐ[ℚ] rationalCyclotomicField`; its finite
cyclotomic levels form a divisibility-directed system with supremum the
whole field.  The torsion fixed field is the actual
intermediate field `rationalCyclotomicTorsionFixedField`.

The actual continuous cyclotomic character identifies the full Galois
group with `ℤ̂ˣ`.  Applying infinite Galois correspondence to the actual
torsion closure and the group-theoretic decomposition of `ℤ̂ˣ` gives the
cyclotomic `ℤ̂`-extension.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open scoped IsMulCommutative
open KummerTheory
open ClassFormation

noncomputable def rationalCyclotomicTorsionRestrictionEquiv :
    (rationalCyclotomicField ≃ₐ[ℚ]
        rationalCyclotomicField) ⧸
        rationalCyclotomicTorsionClosure.toSubgroup ≃ₜ*
      (rationalCyclotomicTorsionFixedField ≃ₐ[ℚ]
        rationalCyclotomicTorsionFixedField) := by
  let _ : T2Space
      (rationalCyclotomicTorsionFixedField ≃ₐ[ℚ]
        rationalCyclotomicTorsionFixedField) :=
    krullTopology_t2
  exact
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.continuousMulEquivOfCompactToT2
      (InfiniteGalois.normalAutEquivQuotient
        (k := ℚ) (K := rationalCyclotomicField)
        rationalCyclotomicTorsionClosure)
      (by
        rw [←
          QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff]
        exact
          InfiniteGalois.restrictNormalHom_continuous
            rationalCyclotomicTorsionFixedField)

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.KummerTheory_Concrete_CyclotomicPrimeBaseChange
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Prime cyclotomic base change

This file constructs the roots-of-unity base change for a prime-degree
extension.  If `L / K` has prime degree `p`, the
cyclotomic extension `K(μ_p) / K` has degree strictly smaller than `p`.
The two degrees are therefore coprime, and

`K(μ_p) ⊗[K] L`

is an actual field, Galois of degree `p` over `K(μ_p)`.
-/

open scoped NumberField TensorProduct
open NumberField

noncomputable section

namespace KummerTheory

universe u

variable
    (K L : Type u)
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]

/-- The field structure on the prime cyclotomic pushout, obtained
from coprime degrees. -/
@[reducible]
noncomputable def primeCyclotomicPushoutField
    (p : ℕ) (hp : p.Prime)
    (hdegree : Module.finrank K L = p) :
    Field (PrimeCyclotomicPushout K L p) :=
  (tensorProduct_isField_of_finrank_coprime
    K (PrimeCyclotomicBase K p) L
    (primeCyclotomicBase_finrank_coprime
      (K := K) (L := L) p hp hdegree)).toField

/-- The canonical left-factor algebra structure, restated after
installing the field structure on the tensor product. -/
@[reducible]
noncomputable def primeCyclotomicPushoutAlgebra
    (p : ℕ) (hp : p.Prime)
    (hdegree : Module.finrank K L = p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    letI : Field (PrimeCyclotomicPushout K L p) :=
      primeCyclotomicPushoutField K L p hp hdegree
    Algebra
      (PrimeCyclotomicBase K p)
      (PrimeCyclotomicPushout K L p) := by
  letI : Field (PrimeCyclotomicPushout K L p) :=
    primeCyclotomicPushoutField K L p hp hdegree
  exact Algebra.TensorProduct.leftAlgebra

omit [IsGalois K L] in
/-- The pushout has the expected degree over the cyclotomic base. -/
theorem primeCyclotomicPushout_finrank
    (p : ℕ) (hp : p.Prime)
    (hdegree : Module.finrank K L = p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    letI : Field (PrimeCyclotomicPushout K L p) :=
      primeCyclotomicPushoutField K L p hp hdegree
    letI : Algebra
        (PrimeCyclotomicBase K p)
        (PrimeCyclotomicPushout K L p) :=
      primeCyclotomicPushoutAlgebra K L p hp hdegree
    Module.finrank
        (PrimeCyclotomicBase K p)
        (PrimeCyclotomicPushout K L p) =
      p := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let : Field (PrimeCyclotomicPushout K L p) :=
    primeCyclotomicPushoutField K L p hp hdegree
  let : Algebra
      (PrimeCyclotomicBase K p)
      (PrimeCyclotomicPushout K L p) :=
    primeCyclotomicPushoutAlgebra K L p hp hdegree
  rw [Module.finrank_baseChange, hdegree]

/-- The prime cyclotomic pushout is Galois over `K(μ_p)`. -/
theorem primeCyclotomicPushout_isGalois
    (p : ℕ) (hp : p.Prime)
    (hdegree : Module.finrank K L = p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    letI : Field (PrimeCyclotomicPushout K L p) :=
      primeCyclotomicPushoutField K L p hp hdegree
    letI : Algebra
        (PrimeCyclotomicBase K p)
        (PrimeCyclotomicPushout K L p) :=
      primeCyclotomicPushoutAlgebra K L p hp hdegree
    IsGalois
      (PrimeCyclotomicBase K p)
      (PrimeCyclotomicPushout K L p) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let : Field (PrimeCyclotomicPushout K L p) :=
    primeCyclotomicPushoutField K L p hp hdegree
  let : Algebra
      (PrimeCyclotomicBase K p)
      (PrimeCyclotomicPushout K L p) :=
    primeCyclotomicPushoutAlgebra K L p hp hdegree
  exact
    tensorProduct_isGalois_of_finrank_coprime
      K (PrimeCyclotomicBase K p) L
      (primeCyclotomicBase_finrank_coprime
        (K := K) (L := L) p hp hdegree)

omit [IsGalois K L] in
/-- The prime cyclotomic pushout is again a number field. -/
theorem primeCyclotomicPushout_numberField
    (p : ℕ) (hp : p.Prime)
    (hdegree : Module.finrank K L = p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    letI : Field (PrimeCyclotomicPushout K L p) :=
      primeCyclotomicPushoutField K L p hp hdegree
    letI : Algebra
        (PrimeCyclotomicBase K p)
        (PrimeCyclotomicPushout K L p) :=
      primeCyclotomicPushoutAlgebra K L p hp hdegree
    NumberField (PrimeCyclotomicPushout K L p) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let : Field (PrimeCyclotomicPushout K L p) :=
    primeCyclotomicPushoutField K L p hp hdegree
  let : Algebra
      (PrimeCyclotomicBase K p)
      (PrimeCyclotomicPushout K L p) :=
    primeCyclotomicPushoutAlgebra K L p hp hdegree
  exact
    NumberField.of_module_finite
      (PrimeCyclotomicBase K p)
      (PrimeCyclotomicPushout K L p)

/-- The cyclotomic base contains a primitive `p`-th root of unity. -/
theorem primeCyclotomicBase_primitiveRoots_nonempty
    (p : ℕ) (hp : p.Prime) :
    (primitiveRoots p (PrimeCyclotomicBase K p)).Nonempty := by
  let : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ :=
    (CyclotomicField.isCyclotomicExtension p K).exists_isPrimitiveRoot
      (Set.mem_singleton p) hp.ne_zero
  exact ⟨ζ, (mem_primitiveRoots hp.pos).2 hζ⟩

/-- The Galois group after cyclotomic base change is cyclic of prime
order. -/
theorem primeCyclotomicPushout_isCyclic
    (p : ℕ) (hp : p.Prime)
    (hdegree : Module.finrank K L = p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    letI : Field (PrimeCyclotomicPushout K L p) :=
      primeCyclotomicPushoutField K L p hp hdegree
    letI : Algebra
        (PrimeCyclotomicBase K p)
        (PrimeCyclotomicPushout K L p) :=
      primeCyclotomicPushoutAlgebra K L p hp hdegree
    letI : IsGalois
        (PrimeCyclotomicBase K p)
        (PrimeCyclotomicPushout K L p) :=
      primeCyclotomicPushout_isGalois
        K L p hp hdegree
    IsCyclic
      (PrimeCyclotomicPushout K L p ≃ₐ[
        PrimeCyclotomicBase K p]
        PrimeCyclotomicPushout K L p) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let : Field (PrimeCyclotomicPushout K L p) :=
    primeCyclotomicPushoutField K L p hp hdegree
  let : Algebra
      (PrimeCyclotomicBase K p)
      (PrimeCyclotomicPushout K L p) :=
    primeCyclotomicPushoutAlgebra K L p hp hdegree
  let : IsGalois
      (PrimeCyclotomicBase K p)
      (PrimeCyclotomicPushout K L p) :=
    primeCyclotomicPushout_isGalois
      K L p hp hdegree
  let : Fact p.Prime := ⟨hp⟩
  exact
    isCyclic_of_prime_card (p := p) (by
      rw [IsGalois.card_aut_eq_finrank,
        primeCyclotomicPushout_finrank
          K L p hp hdegree])

/-- Prime-degree Kummer coordinates for the base-changed Galois group,
in the exact one-coordinate form used by the prime-degree Kummer coordinate construction. -/
noncomputable def primeCyclotomicPushoutGalEquivPiZMod
    (p : ℕ) (hp : p.Prime)
    (hdegree : Module.finrank K L = p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    letI : Field (PrimeCyclotomicPushout K L p) :=
      primeCyclotomicPushoutField K L p hp hdegree
    letI : Algebra
        (PrimeCyclotomicBase K p)
        (PrimeCyclotomicPushout K L p) :=
      primeCyclotomicPushoutAlgebra K L p hp hdegree
    letI : IsGalois
        (PrimeCyclotomicBase K p)
        (PrimeCyclotomicPushout K L p) :=
      primeCyclotomicPushout_isGalois
        K L p hp hdegree
    (PrimeCyclotomicPushout K L p ≃ₐ[
        PrimeCyclotomicBase K p]
        PrimeCyclotomicPushout K L p) ≃*
      (Fin 1 → Multiplicative (ZMod p)) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Field (PrimeCyclotomicPushout K L p) :=
    primeCyclotomicPushoutField K L p hp hdegree
  letI : Algebra
      (PrimeCyclotomicBase K p)
      (PrimeCyclotomicPushout K L p) :=
    primeCyclotomicPushoutAlgebra K L p hp hdegree
  letI : IsGalois
      (PrimeCyclotomicBase K p)
      (PrimeCyclotomicPushout K L p) :=
    primeCyclotomicPushout_isGalois
      K L p hp hdegree
  let G :=
    PrimeCyclotomicPushout K L p ≃ₐ[
      PrimeCyclotomicBase K p]
      PrimeCyclotomicPushout K L p
  letI : IsCyclic G :=
    primeCyclotomicPushout_isCyclic
      K L p hp hdegree
  have hcardG : Nat.card G = p := by
    dsimp only [G]
    rw [IsGalois.card_aut_eq_finrank,
      primeCyclotomicPushout_finrank
        K L p hp hdegree]
  exact
    (hcardG ▸ (zmodCyclicMulEquiv
      (inferInstance : IsCyclic G)).symm).trans
      (MulEquiv.piUnique
        (fun _ : Fin 1 => Multiplicative (ZMod p))).symm

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_NormalizedIntegerValuation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The normalized integer valuation of a local field

The Kummer branch of the local existence theorem uses power-class index
formulas stated for valuations with value group
`WithZero (Multiplicative ℤ)`.  A nonarchimedean local field carries its
canonical valuation in an intrinsic value group.  This file transports that
valuation to the integer model and proves that completeness and the finite
residue field are preserved.
-/

noncomputable section

namespace LocalFieldTheory

open scoped ValuativeRel

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The valuation in the canonical complete-DVF package is the original local valuation. -/
theorem localCompleteDVF_valuation_eq :
    (localCompleteDVF K).valuation = ValuativeRel.valuation K := by
  unfold localCompleteDVF
  unfold ValuationTheory.Valuations.completeDVFOfCompleteValuedField
  rfl

/-- Identity on field elements gives the valuation-ring equivalence attached
to the normalization of the value group. -/
noncomputable def localIntegerValuationSubringEquiv :
    (localIntegerValuation K).valuationSubring ≃+*
      (localCompleteDVF K).valuationSubring where
  toFun := fun x => ⟨x, by
    change (localCompleteDVF K).valuation (x : K) ≤ 1
    rw [localCompleteDVF_valuation_eq]
    have hx :
        IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
            (ValuativeRel.valuation K (x : K)) ≤
          IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K 1 := by
      have hxmem := x.property
      change localIntegerValuation K (x : K) ≤ 1 at hxmem
      rw [localIntegerValuation_apply] at hxmem
      simpa only [map_one] using hxmem
    exact
      (map_le_map_iff
        (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)).mp hx⟩
  invFun := fun x => ⟨x, by
    have hx : ValuativeRel.valuation K (x : K) ≤ 1 := by
      have hxmem := x.property
      change (localCompleteDVF K).valuation (x : K) ≤ 1 at hxmem
      rw [localCompleteDVF_valuation_eq] at hxmem
      exact hxmem
    change
      IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
          (ValuativeRel.valuation K (x : K)) ≤ 1
    simpa only [localIntegerValuation, _root_.Valuation.map_apply,
      map_one] using
      (map_le_map_iff
        (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)).mpr hx⟩
  left_inv := fun x => by ext; rfl
  right_inv := fun x => by ext; rfl
  map_mul' := fun x y => by ext; rfl
  map_add' := fun x y => by ext; rfl

/-- The valuation-subring equivalence preserves the underlying element of `K`. -/
@[simp]
theorem localIntegerValuationSubringEquiv_apply_coe
    (x : (localIntegerValuation K).valuationSubring) :
    ((localIntegerValuationSubringEquiv K x :
      (localCompleteDVF K).valuationSubring) : K) = x := by
  rfl

end LocalFieldTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_SimpleExtension
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

/-- The chosen radical generates the whole simple extension. -/
theorem chosenSimpleKummerExtension_adjoin_root_eq_top
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0) (b : Kˣ) :
    let E := chosenSimpleKummerExtension K n hnK b
    IntermediateField.adjoin K
      {((chosenSimpleKummerRootUnit K n hnK b : Eˣ) : E)} = ⊤ := by
  let E := chosenSimpleKummerExtension K n hnK b
  let beta : E := (chosenSimpleKummerRootUnit K n hnK b : Eˣ)
  let R : IntermediateField K E :=
    IntermediateField.adjoin K {beta}
  change R = ⊤
  apply top_unique
  intro x _
  have hall : ∀ y : SeparableClosure K, ∀ hy : y ∈ E,
      (⟨y, hy⟩ : E) ∈ R := by
    intro y hy
    change y ∈ IntermediateField.adjoin K
      {chosenSimpleKummerRoot K n hnK b} at hy
    induction hy using IntermediateField.adjoin_induction with
    | mem y hy =>
        have hy' : y = chosenSimpleKummerRoot K n hnK b :=
          Set.mem_singleton_iff.mp hy
        subst y
        apply IntermediateField.subset_adjoin K
        rw [Set.mem_singleton_iff]
        apply Subtype.ext
        rfl
    | algebraMap a => exact R.algebraMap_mem a
    | add x y hx hy ihx ihy => exact R.add_mem ihx ihy
    | inv x hx ihx => exact R.inv_mem ihx
    | mul x y hx hy ihx ihy => exact R.mul_mem ihx ihy
  exact hall x.1 x.property

/-- The Galois group of a simple Kummer extension is cyclic. -/
theorem chosenSimpleKummerExtension_isCyclic
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (b : Kˣ) :
    IsCyclic Gal((chosenSimpleKummerExtension K n hnK b)/K) := by
  let : IsAbelianGalois K (chosenSimpleKummerExtension K n hnK b) :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  exact
    isCyclic_of_injective
      (chosenSimpleKummerRootCharacter K n hnK hmu b)
      (chosenSimpleKummerRootCharacter_injective K n hnK hmu b)

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_IntermediateFieldNormResidueNaturality
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Restriction naturality for the concrete local norm-residue symbol

The abstract class formation supplies restriction naturality.  This file
constructs the field-facing restriction map for two finite Galois intermediate
fields in the fixed separable closure and transports the naturality identity
to the concrete local norm-residue symbol.

The intermediate-field restriction is packaged here so callers do not have
to install the auxiliary `Algebra E F` and scalar-tower instances attached
to an inclusion `E ≤ F`.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation LocalClassFieldTheory
open scoped IsMulCommutative

universe u v

variable {K : Type u} {Omega : Type v}
  [Field K] [Field Omega] [Algebra K Omega]

abbrev absoluteGalois_p0 (K : Type) [Field K] :=
  intrinsicAbsoluteGalois K

abbrev absoluteUnits (K : Type) [Field K] :
    Rep ℤ (absoluteGalois_p0 K) :=
  intrinsicAbsoluteUnits K

abbrev abstractBase_p0 (K : Type) [Field K] :
    ClosedSubgroup (absoluteGalois_p0 K) :=
  intrinsicAbstractBase K

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_UnramifiedComparison
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Abstract and concrete unramified Frobenius

This module compares the residue-degree construction on a fixed separable
closure with the ordinary unramified valuation extension and its arithmetic
Frobenius.
-/

noncomputable section

namespace LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open RamificationTheory.HilbertRamification.ValuationSubring


abbrev absoluteGalois_p1 (K : Type) [Field K] :=
  intrinsicAbsoluteGalois K

abbrev abstractBase_p1 (K : Type) [Field K] :
    ClosedSubgroup (absoluteGalois_p1 K) :=
  intrinsicAbstractBase K

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_UnramifiedNormalization
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Canonical unramified normalization

The canonical local norm-residue symbol is identified with the field-facing
unramified Artin map. An element of normalized valuation one maps to arithmetic
Frobenius, both algebraically and in the topological abelianization.
-/

noncomputable section

namespace LocalClassFieldTheory

open scoped IsMulCommutative ValuativeRel
open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation

abbrev G_p3 (K : Type) [Field K] :=
  intrinsicAbsoluteGalois K

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FormalModule_Series
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Lubin--Tate power series

A Lubin--Tate power series over a chosen valuation ring has zero constant
coefficient, prescribed linear coefficient, and reduces to the residue-field
Frobenius power series. The chosen element is not required to be a uniformizer
in the structure itself, so the coefficient package can be reused independently.
-/

noncomputable section

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- A Lubin--Tate series with prescribed linear coefficient π.

The first two fields specify the constant and linear terms. The final field
specifies coefficientwise reduction to the residue-field Frobenius series. -/
structure LubinTateSeries
    (F : LocalField.{u, v} K) (π : F.valuationSubring) where
  /-- The underlying one-variable formal power series over `O_K`. -/
  toPowerSeries : PowerSeries F.valuationSubring
  /-- The constant coefficient of a Lubin--Tate series vanishes. -/
  constantCoeff_eq_zero :
    PowerSeries.constantCoeff toPowerSeries = 0
  /-- The linear coefficient is the chosen element `π`. -/
  coeff_one_eq_uniformizer :
    PowerSeries.coeff 1 toPowerSeries = π
  /-- Reduction to the residue field is the `q`-power Frobenius series. -/
  map_residue_eq_frobenius :
    PowerSeries.map F.residueMap toPowerSeries =
      (PowerSeries.X : PowerSeries F.residueField) ^
        Nat.card F.residueField

attribute [simp] LubinTateSeries.constantCoeff_eq_zero
  LubinTateSeries.coeff_one_eq_uniformizer
  LubinTateSeries.map_residue_eq_frobenius

namespace LubinTateSeries

variable {F : LocalField.{u, v} K} {π : F.valuationSubring}

/-- Two Lubin--Tate series are equal when their underlying power series
are equal. -/
@[ext]
theorem ext {e e' : LubinTateSeries F π}
    (h : e.toPowerSeries = e'.toPowerSeries) : e = e' := by
  cases e
  cases e'
  cases h
  rfl

end LubinTateSeries

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FormalModule_Intertwiner
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Intertwining equations for Lubin--Tate series

For two Lubin--Tate series with the same prescribed linear coefficient, this
module defines the multivariable intertwining equation and its additive defect.
-/

noncomputable section

universe u v

namespace LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type*}

/-- Insert a one-variable Lubin--Tate series into the variable `X_i`. -/
noncomputable def inVariable (e : LubinTateSeries F π) (i : σ) :
    MvPowerSeries σ F.valuationSubring :=
  PowerSeries.subst (MvPowerSeries.X i) e.toPowerSeries

/-- States the theorem `constantCoeff_inVariable`. -/
@[simp]
theorem constantCoeff_inVariable (e : LubinTateSeries F π) (i : σ) :
    MvPowerSeries.constantCoeff (inVariable e i) = 0 := by
  exact PowerSeries.constantCoeff_subst_eq_zero
    (MvPowerSeries.constantCoeff_X (R := F.valuationSubring) i)
    e.toPowerSeries e.constantCoeff_eq_zero

/-- The family `i |-> e(X_i)` admits genuine multivariable
substitution. -/
theorem inVariable_hasSubst [Finite σ] (e : LubinTateSeries F π) :
    MvPowerSeries.HasSubst (fun i : σ ↦ inVariable e i) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero
    (fun i ↦ constantCoeff_inVariable e i)

/-- The literal same-uniformizer equation
`e(H(X_i)) = H(ebar(X_i))`. -/
def Intertwines (e ebar : LubinTateSeries F π)
    (H : MvPowerSeries σ F.valuationSubring) : Prop :=
  PowerSeries.subst H e.toPowerSeries =
    MvPowerSeries.subst (fun i : σ ↦ inVariable ebar i) H

/-- The coefficientwise defect whose vanishing is the intertwining
equation. -/
noncomputable def defect (e ebar : LubinTateSeries F π)
    (H : MvPowerSeries σ F.valuationSubring) :
    MvPowerSeries σ F.valuationSubring :=
  PowerSeries.subst H e.toPowerSeries -
    MvPowerSeries.subst (fun i : σ ↦ inVariable ebar i) H

/-- States the theorem `intertwines_iff_defect_eq_zero`. -/
theorem intertwines_iff_defect_eq_zero
    (e ebar : LubinTateSeries F π)
    (H : MvPowerSeries σ F.valuationSubring) :
    Intertwines e ebar H ↔ defect e ebar H = 0 := by
  simp only [Intertwines, defect, sub_eq_zero]

end SameUniformizer
end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FormalModule_Reduction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Reduction of a Lubin--Tate intertwining defect

After reduction to the finite residue field, both series become the Frobenius
power series. The two sides of the intertwining equation then agree, so every
coefficient of the defect is divisible by the chosen uniformizer.
-/

noncomputable section

universe u v w

namespace LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w} [Fintype σ]

omit [Fintype σ] in
/-- Reduction of `e(X_i)` is `X_i ^ q`. -/
theorem map_inVariable (e : LubinTateSeries F π) (i : σ) :
    MvPowerSeries.map F.residueMap (inVariable e i) =
      (MvPowerSeries.X i : MvPowerSeries σ F.residueField) ^
        Nat.card F.residueField := by
  have hX : PowerSeries.HasSubst
      (MvPowerSeries.X i : MvPowerSeries σ F.valuationSubring) :=
    PowerSeries.HasSubst.X i
  have hXbar : PowerSeries.HasSubst
      (MvPowerSeries.X i : MvPowerSeries σ F.residueField) :=
    PowerSeries.HasSubst.X i
  rw [inVariable, PowerSeries.map_subst hX e.toPowerSeries,
    e.map_residue_eq_frobenius, MvPowerSeries.map_X,
    PowerSeries.subst_pow hXbar, PowerSeries.subst_X hXbar]

/-- The reduced left side `e(H)` is `Hbar ^ q`. -/
theorem map_subst_lubinTateSeries
    (e : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L) :
    MvPowerSeries.map F.residueMap
        (PowerSeries.subst H e.toPowerSeries) =
      (MvPowerSeries.map F.residueMap H) ^
        Nat.card F.residueField := by
  have hmap : PowerSeries.HasSubst
      (MvPowerSeries.map F.residueMap H) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by
      simp [hH.constantCoeff_eq_zero])
  rw [PowerSeries.map_subst hH.hasSubst e.toPowerSeries,
    e.map_residue_eq_frobenius, PowerSeries.subst_pow hmap,
    PowerSeries.subst_X hmap]

/-- The reduced right side `H(ebar(X_i))` is the expansion
`Hbar(X_i ^ q)`. -/
theorem map_subst_inVariables
    (ebar : LubinTateSeries F π)
    (H : MvPowerSeries σ F.valuationSubring) :
    MvPowerSeries.map F.residueMap
        (MvPowerSeries.subst
          (fun i : σ ↦ inVariable ebar i) H) =
      MvPowerSeries.expand (Nat.card F.residueField)
        (Nat.ne_of_gt Nat.card_pos)
        (MvPowerSeries.map F.residueMap H) := by
  rw [MvPowerSeries.map_subst (inVariable_hasSubst ebar) H]
  simp_rw [map_inVariable]
  rw [MvPowerSeries.expand, MvPowerSeries.substAlgHom_apply]

/-- The same-uniformizer intertwining defect vanishes after reduction. -/
theorem map_defect_eq_zero
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L) :
    MvPowerSeries.map F.residueMap (defect e ebar H) = 0 := by
  rw [defect, map_sub, map_subst_lubinTateSeries e hH,
    map_subst_inVariables ebar H,
    mvPowerSeries_expand_natCard]
  exact sub_self _

end SameUniformizer
end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FormalModule_DegreeStabilization
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite-degree stabilization for Lubin--Tate intertwining defects

The coefficient of an intertwining defect in total degree at most `m`
depends only on the coefficients of the proposed intertwiner in total degree
at most `m`.  This is the finite-degree continuity statement needed to pass
from recursively corrected finite approximations to one full multivariable
power series.

The proof uses total-degree truncation.  On the left side of the
intertwining equation, truncation commutes with substituting a series with
zero constant coefficient into the fixed Lubin--Tate series.  On the right
side, truncation of multivariable substitution depends only on the same
truncation of the outer series.
-/

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable

universe u v w

namespace LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w} [Fintype σ]

theorem truncTotal_powerSeries_subst_eq_of_truncTotal_eq
    (e : LubinTateSeries F π)
    {H H' : MvPowerSeries σ F.valuationSubring}
    (hH : MvPowerSeries.constantCoeff H = 0)
    (hH' : MvPowerSeries.constantCoeff H' = 0)
    {k : ℕ} (htrunc : H.truncTotal k = H'.truncTotal k) :
    (PowerSeries.subst H e.toPowerSeries).truncTotal k =
      (PowerSeries.subst H' e.toPowerSeries).truncTotal k := by
  have hHsubst : PowerSeries.HasSubst H :=
    PowerSeries.HasSubst.of_constantCoeff_zero hH
  have hH'subst : PowerSeries.HasSubst H' :=
    PowerSeries.HasSubst.of_constantCoeff_zero hH'
  change
    (MvPowerSeries.subst (fun _ : Unit ↦ H) e.toPowerSeries).truncTotal k =
      (MvPowerSeries.subst (fun _ : Unit ↦ H') e.toPowerSeries).truncTotal k
  calc
    (MvPowerSeries.subst (fun _ : Unit ↦ H) e.toPowerSeries).truncTotal k =
        (MvPowerSeries.subst
          (fun _ : Unit ↦ (H.truncTotal k).toMvPowerSeries)
          e.toPowerSeries).truncTotal k := by
      exact
        MvPowerSeries.truncTotal_subst_eq_truncTotal_subst_truncTotal_of_le
          (f := e.toPowerSeries) (a := fun _ : Unit ↦ H)
          (x := fun _ : Unit ↦ k) hHsubst.const (fun _ ↦ le_rfl)
    _ = (MvPowerSeries.subst
          (fun _ : Unit ↦ (H'.truncTotal k).toMvPowerSeries)
          e.toPowerSeries).truncTotal k := by
      rw [htrunc]
    _ = (MvPowerSeries.subst (fun _ : Unit ↦ H')
          e.toPowerSeries).truncTotal k := by
      exact
        (MvPowerSeries.truncTotal_subst_eq_truncTotal_subst_truncTotal_of_le
          (f := e.toPowerSeries) (a := fun _ : Unit ↦ H')
          (x := fun _ : Unit ↦ k) hH'subst.const
          (fun _ ↦ le_rfl)).symm

theorem truncTotal_inVariables_subst_eq_of_truncTotal_eq
    (ebar : LubinTateSeries F π)
    {H H' : MvPowerSeries σ F.valuationSubring}
    {k : ℕ} (htrunc : H.truncTotal k = H'.truncTotal k) :
    (MvPowerSeries.subst (fun i : σ ↦ inVariable ebar i) H).truncTotal k =
      (MvPowerSeries.subst (fun i : σ ↦ inVariable ebar i) H').truncTotal k := by
  have hconstant :
      ∀ i : σ,
        MvPowerSeries.constantCoeff (inVariable ebar i) = 0 :=
    fun i ↦ constantCoeff_inVariable ebar i
  calc
    (MvPowerSeries.subst (fun i : σ ↦ inVariable ebar i) H).truncTotal k =
        (MvPowerSeries.subst (fun i : σ ↦ inVariable ebar i)
          (H.truncTotal k).toMvPowerSeries).truncTotal k := by
      exact
        MvPowerSeries.truncTotal_subst_eq_truncTotal_truncTotal_subst
          (f := H) (a := fun i : σ ↦ inVariable ebar i) hconstant
    _ = (MvPowerSeries.subst (fun i : σ ↦ inVariable ebar i)
          (H'.truncTotal k).toMvPowerSeries).truncTotal k := by
      rw [htrunc]
    _ = (MvPowerSeries.subst (fun i : σ ↦ inVariable ebar i) H').truncTotal k := by
      exact
        (MvPowerSeries.truncTotal_subst_eq_truncTotal_truncTotal_subst
          (f := H') (a := fun i : σ ↦ inVariable ebar i) hconstant).symm

noncomputable def linearInVariableStabilization
    (π : F.valuationSubring) (i : σ) :
    MvPowerSeries σ F.valuationSubring :=
  MvPowerSeries.C π * MvPowerSeries.X i

end SameUniformizer
end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FormalModule_RecursiveCorrection
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Recursive monomial corrections for Lubin--Tate intertwiners

The coefficient selected in `RecursiveCoefficient` is inserted as a single
monomial.  This file proves that the insertion preserves the prescribed linear
term and cancels the defect coefficient in precisely that total degree.
-/

noncomputable section

open scoped BigOperators

universe u v w

namespace LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w} [Fintype σ]

/-- The linear part of `e(X_i)` for a same-uniformizer Lubin--Tate series. -/
noncomputable def linearInVariable
    (π : F.valuationSubring) (i : σ) :
    MvPowerSeries σ F.valuationSubring :=
  MvPowerSeries.C π * MvPowerSeries.X i

omit [Fintype σ] in
theorem linearInVariable_constantCoeff
    (π : F.valuationSubring) (i : σ) :
    MvPowerSeries.constantCoeff (linearInVariable π i) = 0 := by
  rw [linearInVariable, map_mul,
    MvPowerSeries.constantCoeff_C,
    ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    MvPowerSeries.coeff_zero_X, mul_zero]

end SameUniformizer
end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FormalModule_RecursiveIntertwiner
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite-degree approximations to Lubin--Tate intertwiners

For a fixed total degree there are only finitely many monomials.  This file
orders those monomials, applies the coefficient correction from
`RecursiveCorrection` one at a time, and then iterates the resulting
degreewise correction.

The construction is genuinely recursive: stage `n + 1` corrects every
monomial of total degree `n + 2`.  Corrections in that degree leave all lower
coefficients unchanged.  The stabilized coefficient series and its
intertwining equation are established below after the finite-degree
construction.
-/

noncomputable section

universe u v w

namespace LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {pi : F.valuationSubring}
variable {sigma : Type w} [Fintype sigma]

/-- The prescribed linear form itself has the prescribed linear term. -/
theorem linearForm_hasLinearTerm
    (L : sigma → F.valuationSubring) :
    HasLinearTerm (linearForm L) L := by
  simp [HasLinearTerm]

abbrev Approximation
    (L : sigma → F.valuationSubring) :=
  {H : MvPowerSeries sigma F.valuationSubring // HasLinearTerm H L}

end SameUniformizer
end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FormalModule_StandardSeries
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The standard Lubin--Tate series

For a uniformizer `π`, the polynomial power series

`π X + X ^ q`,

where `q` is the cardinality of the residue field, is a Lubin--Tate
series.  This gives the general formal-module construction a canonical
polynomial input without making an equal-characteristic assumption.
-/

noncomputable section

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}

/-- The polynomial power series `π X + X ^ q`, where `q` is the residue
field cardinality. -/
noncomputable def standardLubinTatePowerSeries
    (F : LocalField.{u, v} K) (π : F.valuationSubring) :
    PowerSeries F.valuationSubring :=
  PowerSeries.C π * PowerSeries.X +
    PowerSeries.X ^ Nat.card F.residueField

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_Different
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.HilbertRamification.Dedekind.basePrime_isPrime _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedMaximalIdeal.instIsMaximal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Different and codifferent for valued finite extensions

This file specializes mathlib's Dedekind-domain different ideal to complete
DVF valuation rings.  The ideal itself remains mathlib's `differentIdeal`; the
extra API here connects it to the chosen valuation rings, the codifferent, and
the local unramified criterion.
-/

noncomputable section

universe u v w x

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace RamificationTheory
namespace DiscreteValuationField

open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

namespace ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L] [FiniteDimensional K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

omit [FiniteDimensional K L] in
/-- In a local valuation-ring extension, the different is a unit exactly when
the extension is unramified at the target maximal ideal. -/
theorem isUnit_differentIdeal_iff_isUnramifiedAt
    [Module.IsTorsionFree base.valuationSubring target.valuationSubring]
    [Module.Finite base.valuationSubring target.valuationSubring]
    [Algebra.IsSeparable
      (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring)] :
    IsUnit (differentIdeal base.valuationSubring target.valuationSubring) ↔
      Algebra.IsUnramifiedAt base.valuationSubring target.maximalIdeal := by
  constructor
  · intro hunit
    have htop :
        differentIdeal base.valuationSubring target.valuationSubring = ⊤ :=
      Ideal.isUnit_iff.mp hunit
    have hnot :
        ¬ target.maximalIdeal ∣
          differentIdeal base.valuationSubring target.valuationSubring := by
      intro hdvd
      have hle :
          differentIdeal base.valuationSubring target.valuationSubring ≤
            target.maximalIdeal :=
        Ideal.dvd_iff_le.mp hdvd
      rw [htop] at hle
      have hproper : target.maximalIdeal ≠ ⊤ :=
        (IsLocalRing.maximalIdeal.isMaximal target.valuationSubring).ne_top
      exact hproper (eq_top_iff.mpr hle)
    exact (_root_.not_dvd_differentIdeal_iff).1 hnot
  · intro hunram
    have hnot :
        ¬ target.maximalIdeal ∣
          differentIdeal base.valuationSubring target.valuationSubring :=
    (_root_.not_dvd_differentIdeal_iff).2 hunram
    rw [Ideal.isUnit_iff]
    by_contra hne
    have hle :
        differentIdeal base.valuationSubring target.valuationSubring ≤
          target.maximalIdeal :=
      IsLocalRing.le_maximalIdeal hne
    exact hnot (Ideal.dvd_iff_le.mpr hle)

omit [FiniteDimensional K L] in
/-- States the theorem `differentIdeal_eq_top_iff_isUnramifiedAt`. -/
theorem differentIdeal_eq_top_iff_isUnramifiedAt
    [Module.IsTorsionFree base.valuationSubring target.valuationSubring]
    [Module.Finite base.valuationSubring target.valuationSubring]
    [Algebra.IsSeparable
      (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring)] :
    differentIdeal base.valuationSubring target.valuationSubring = ⊤ ↔
      Algebra.IsUnramifiedAt base.valuationSubring target.maximalIdeal := by
  rw [← Ideal.isUnit_iff]
  exact (RamificationTheory.DiscreteValuationField.ValuedExtension.isUnit_differentIdeal_iff_isUnramifiedAt base target)

end ValuedExtension
end DiscreteValuationField
end RamificationTheory

end
end


