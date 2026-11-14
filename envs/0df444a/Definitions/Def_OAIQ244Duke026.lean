-- Prove2me | Definitions.Def_OAIQ244Duke026
-- name    : OAIQ244Duke026
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:30:51.9242+00:00
-- url     : https://prove2.me/theorems/b74e92a4-4181-4400-abe4-1b9027278175
-- title:
--   Definitions bundle OAIQ244Duke026 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 230 declarations of OpenAI's Lean: 66 definitions, 5 inductive types or structures, 20 instances and 139 theorems. The definitions and types are `ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower`, `ClassFormation.DegreeData.FrobeniusFixedFieldTower`, `ClassFormation.DegreeData.FrobeniusFixedFieldTower.CyclicGenerator`, `ClassFormation.DegreeData.FrobeniusFixedFieldTower.Representative`, `ClassFormation.DegreeData.FrobeniusFixedFieldTower.base`, `ClassFormation.DegreeData.FrobeniusFixedFieldTower.extension`, `ClassFormation.DegreeData.FrobeniusFixedFieldTower.field`, `ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower`, `ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.ambientGalois`, `ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.baseFrobenius`, `ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.fieldFrobenius`, `ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.toFiniteAmbientFrobeniusFixedFieldTower`, `ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.toFrobeniusFixedFieldTower`, `ClassFormation.DegreeData.chosenDegreeOneFrobeniusElement`, `ClassFormation.DegreeData.chosenFiniteReciprocityFrobeniusLift`, `ClassFormation.DegreeData.chosenUnramifiedFrobeniusLift`, `ClassFormation.DegreeData.extensionImageInInertiaQuotient`, `ClassFormation.DegreeData.finiteReciprocityCandidate`, `ClassFormation.DegreeData.finiteReciprocityValue`, `ClassFormation.DegreeData.fixedFieldNormalizedDegree`, `ClassFormation.DegreeData.frobeniusActionConjugate`, `ClassFormation.DegreeData.frobeniusActionRemainder`, `ClassFormation.DegreeData.frobeniusClosureDegreeInMulNatRange`, `ClassFormation.DegreeData.frobeniusFixedAbstractField`, `ClassFormation.DegreeData.frobeniusFixedCosetClosureEquiv`, `ClassFormation.DegreeData.frobeniusFixedCosetToClosureCoset`, `ClassFormation.DegreeData.frobeniusFixedField`, `ClassFormation.DegreeData.frobeniusFixedFieldAction`, `ClassFormation.DegreeData.frobeniusFixedFieldQuotientEquiv`, `ClassFormation.DegreeData.frobeniusFixedFieldToClosure`, `ClassFormation.DegreeData.frobeniusFixedField_normalizedDegreeEquiv`, `ClassFormation.DegreeData.frobeniusFixedIntermediateField`, `ClassFormation.DegreeData.frobeniusFixedSubgroupWithin`, `ClassFormation.DegreeData.frobeniusLiftDifference`, `ClassFormation.DegreeData.frobeniusMul`, `ClassFormation.DegreeData.frobeniusNormIdentityCosetEquiv`, `ClassFormation.DegreeData.frobeniusNormIdentityCosetMap`, `ClassFormation.DegreeData.frobeniusPowerOfDegreeOne`, `ClassFormation.DegreeData.frobeniusPowerSum`, `ClassFormation.DegreeData.frobeniusQuotientAction` and 31 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AbstractClassFieldTheory_Degree_FrobeniusFixedField`, `AbstractClassFieldTheory_Reciprocity_Construction_CanonicalUnramifiedNormQuotient`, `AbstractClassFieldTheory_Reciprocity_Construction_ChosenDegreeOneFrobenius`, `AbstractClassFieldTheory_Reciprocity_Construction_CoreFrobeniusNorm`, `AbstractClassFieldTheory_Reciprocity_Construction_FiniteFieldUnitMaps`, `AbstractClassFieldTheory_Reciprocity_Construction_FiniteIntermediateCompositum`, `AbstractClassFieldTheory_Reciprocity_Construction_FrobeniusClosureCommutation`, `AbstractClassFieldTheory_Reciprocity_Construction_FrobeniusDescent`, `AbstractClassFieldTheory_Reciprocity_Construction_FrobeniusField`, `AbstractClassFieldTheory_Reciprocity_Construction_FrobeniusFixedFieldAction`, `AbstractClassFieldTheory_Reciprocity_Construction_FrobeniusFixedFieldTower`, `AbstractClassFieldTheory_Reciprocity_Construction_FrobeniusPowerFixedField`, `AbstractClassFieldTheory_Reciprocity_Construction_FrobeniusQuotientDescent`, `AbstractClassFieldTheory_Reciprocity_Construction_FrobeniusSemigroup`, `AbstractClassFieldTheory_Reciprocity_Construction_InfiniteUnitDescent`, `AbstractClassFieldTheory_Reciprocity_Construction_InfiniteUnitNormSubgroup`, `AbstractClassFieldTheory_Reciprocity_Construction_MainFiniteReciprocity`, `AbstractClassFieldTheory_Reciprocity_Construction_MainMultiplicativity_ConjugatePrimeNorm`, `AbstractClassFieldTheory_Reciprocity_Construction_MainMultiplicativity_CorrectionSum`, `AbstractClassFieldTheory_Reciprocity_Construction_MainMultiplicativity_FiniteStageCorrections`, `AbstractClassFieldTheory_Reciprocity_Construction_MainMultiplicativity_FrobeniusActionRemainder`, `AbstractClassFieldTheory_Reciprocity_Construction_MainMultiplicativity_FrobeniusPowerSumRelation`, `AbstractClassFieldTheory_Reciprocity_Construction_MainMultiplicativity_NormClassRelation`, `AbstractClassFieldTheory_Reciprocity_Construction_MainMultiplicativity_PrimeUnitDifferences`, `AbstractClassFieldTheory_Reciprocity_Construction_ReciprocityDefinition`, `AbstractClassFieldTheory_Reciprocity_Construction_ReciprocityIndependence`, `AbstractClassFieldTheory_Reciprocity_Construction_UniversalNormDescent`, `AbstractClassFieldTheory_Reciprocity_Construction_UnramifiedNormQuotient`, `AlgebraicNumberTheory_Completion_ChosenLocalization`, `LocalField_NonarchimedeanLocalField_NormQuotient`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke015` and `OAIQ244Duke016` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke037`, `OAIQ244Duke038`, `OAIQ244Duke040`, `OAIQ244Duke042` and `OAIQ244Duke044`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Subring
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
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
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
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.Normal.Basic
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
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.Ostrowski
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification
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
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Vieta
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
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Topology.Algebra.Group.TopologicalAbelianization
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Compact
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.Algebra.Valued.ValuativeRel
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.UniformSpace.AbsoluteValue
import Definitions.Def_OAIQ244Duke015
import Definitions.Def_OAIQ244Duke016

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Degree_FrobeniusFixedField
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteTower.totalQuotientFinite _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientAddCommGroup _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.ClassFormation.finiteNormQuotientAddCommGroup _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.maximalUnramifiedNormClass_eq_zero_iff _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientInfiniteEquiv_maximalUnramifiedNormClass _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientLift_maximalUnramifiedNormClass _root_.ClassFormation.DegreeData.maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClass _root_.ClassFormation.DegreeData.mem_maximalUnramifiedField_iff _root_.ClassFormation.DegreeData.mem_maximalUnramifiedNormSubgroup_iff _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteAbstractField.normToBase_index_eq_degree _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_eq_one_iff _root_.ClassFormation.FiniteGaloisSubextension.toGaloisSubextension_isTotallyRamified_iff _root_.ClassFormation.FiniteGaloisSubextension.toGaloisSubextension_isUnramified_iff _root_.ClassFormation.ValuationData.mem_unitAddSubgroup_iff _root_.ClassFormation.ValuationData.oneValue_coe _root_.ClassFormation.ValuationData.unitRepresentation_quotient_mk_apply _root_.ClassFormation.ValuationData.valuationAt_chosenPrimeElement _root_.ClassFormation.ValuationData.valuationAt_coe _root_.ClassFormation.ValuationData.valueModulo_apply _root_.ClassFormation.absoluteConjugateCosetEquiv_mk _root_.ClassFormation.canonicalValueQuotientMap_mk _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.finiteNormClass_add _root_.ClassFormation.finiteNormClass_eq_zero_iff _root_.ClassFormation.finiteNormClass_nsmul _root_.ClassFormation.finiteNormClass_sub _root_.ClassFormation.finiteNormClass_zero _root_.ClassFormation.finiteNormQuotientConcreteEquiv_finiteNormClass _root_.ClassFormation.finiteNormQuotientLift_finiteNormClass _root_.ClassFormation.finiteReciprocityNaturalityConjugation_mk _root_.ClassFormation.mem_nsmulImage_iff _root_.ClassFormation.normalExtensionAction_coe _root_.ClassFormation.nsmulImage_top _root_.ClassFormation.orbitQuotientClosedCyclicEquiv_mk _root_.ClassFormation.relativeConjugateCosetEquiv_mk _root_.ClassFormation.relativeCosetAction_mk _root_.ClassFormation.relativeCosetAction_zero _root_.ClassFormation.relativeNorm_apply_coe _root_.ClassFormation.relativeNorm_self _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.extensionFixedEndomorphism_apply_val _root_.KummerTheory.extensionFixedKernelElement_val _root_.KummerTheory.extensionFixedRepresentation_quotient_mk_apply_val _root_.KummerTheory.mem_extensionSubgroup_iff _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option synthInstance.maxHeartbeats 400000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ClassFormation

open CyclicCohomology

/-!
# normalized degree and Frobenius theory: the fixed field of a Frobenius lift

This file gives the group-dual form of the Frobenius fixed-field theorem.  If `σ` is a
Frobenius lift in `G(\widetilde L | K)`, the subgroup `Γ` fixing the
field `Σ` is the closed subgroup topologically generated by `σ`.
-/

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The degree map sends the canonical Frobenius-closure generator to its expected value. -/
@[simp]
theorem frobeniusClosureDegree_generator (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    D.frobeniusClosureDegree K L hLK σ
        (D.frobeniusInClosure K L hLK σ) =
      (Multiplicative.ofAdd (1 : ZHat)) ^
          D.frobeniusExponent K L hLK σ := by
  change D.extensionNormalizedDegree K L hLK
      (D.frobeniusInClosure K L hLK σ).1 =
    (Multiplicative.ofAdd (1 : ZHat)) ^
      D.frobeniusExponent K L hLK σ
  have hval :
      (D.frobeniusInClosure K L hLK σ).1 = σ.1 := rfl
  rw [hval]
  exact D.extensionNormalizedDegree_frobenius_eq_pow K L hLK σ

/-- The image of `d_K` on `Γ` is precisely `n ℤ̂`, where
`n = d_K(σ)`.  This is the group-dual residue-degree calculation in
the Frobenius fixed-field residue-degree formula. -/
theorem frobeniusClosureDegree_range (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    (D.frobeniusClosureDegree K L hLK σ).toMonoidHom.range =
      AddSubgroup.toSubgroup
        ((zHatMulNat (D.frobeniusExponent K L hLK σ)).toAddMonoidHom.range) := by
  let : CompactSpace K.field.toSubgroup := by
    change CompactSpace K.field
    infer_instance
  let Γ := D.frobeniusClosure K L hLK σ
  let x : Γ := D.frobeniusInClosure K L hLK σ
  let f : Γ →ₜ* ZHatMul :=
    D.frobeniusClosureDegree K L hLK σ
  let n := D.frobeniusExponent K L hLK σ
  let R : Subgroup ZHatMul :=
    AddSubgroup.toSubgroup ((zHatMulNat n).toAddMonoidHom.range)
  have hn : 0 < n := D.frobeniusExponent_pos K L hLK σ
  have hxgen : TopologicallyGenerates ({x} : Set Γ) := by
    simpa [Γ, x] using
      D.frobeniusInClosure_topologicallyGenerates K L hLK σ
  have hfx : f x =
      (Multiplicative.ofAdd (1 : ZHat)) ^ n := by
    change D.frobeniusClosureDegree K L hLK σ
        (D.frobeniusInClosure K L hLK σ) =
      (Multiplicative.ofAdd (1 : ZHat)) ^
          D.frobeniusExponent K L hLK σ
    exact D.frobeniusClosureDegree_generator K L hLK σ
  have hRclosed : IsClosed (R : Set ZHatMul) := by
    exact isClosed_zHatMulNat_range n
  have hclosed_le_R :
      (closedSubgroupGenerated ({f x} : Set ZHatMul) : Subgroup ZHatMul) ≤ R := by
    apply Subgroup.topologicalClosure_minimal
    · rw [Subgroup.closure_le]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      rw [hfx]
      change n • (1 : ZHat) ∈
        (zHatMulNat n).toAddMonoidHom.range
      exact ⟨(1 : ZHat), rfl⟩
    · exact hRclosed
  apply le_antisymm
  · rintro y ⟨a, rfl⟩
    have ha : a ∈
        (closedSubgroupGenerated ({x} : Set Γ) : Subgroup Γ) := by
      rw [show (closedSubgroupGenerated ({x} : Set Γ) : Subgroup Γ) = ⊤ by
        simpa [TopologicallyGenerates, closedSubgroupGenerated] using hxgen]
      trivial
    exact hclosed_le_R
      (map_mem_closedSubgroupGenerated_singleton f x ha)
  · intro y hy
    change y.toAdd ∈ (zHatMulNat n).toAddMonoidHom.range at hy
    obtain ⟨z, hz⟩ := hy
    have hzgen : z ∈
        (closedSubgroupGenerated
          ({Multiplicative.ofAdd (1 : ZHat)} : Set ZHatMul) :
          Subgroup ZHatMul) := by
      rw [show (closedSubgroupGenerated
          ({Multiplicative.ofAdd (1 : ZHat)} : Set ZHatMul) :
          Subgroup ZHatMul) = ⊤ by
        simpa [TopologicallyGenerates, closedSubgroupGenerated] using
          zHatOne_topologicallyGenerates]
      trivial
    have hmap := map_mem_closedSubgroupGenerated_singleton
      (zHatPowNat n)
      (Multiplicative.ofAdd (1 : ZHat)) hzgen
    have hclosed_le_range :
        (closedSubgroupGenerated
          ({(Multiplicative.ofAdd (1 : ZHat)) ^ n} : Set ZHatMul) :
          Subgroup ZHatMul) ≤ f.toMonoidHom.range := by
      apply Subgroup.topologicalClosure_minimal
      · rw [Subgroup.closure_le]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        subst w
        exact ⟨x, hfx⟩
      · have hcompact : IsCompact (Set.range f) :=
          isCompact_range f.continuous_toFun
        have hrange : Set.range f = (f.toMonoidHom.range : Set ZHatMul) := by
          ext w
          constructor <;> rintro ⟨a, rfl⟩ <;> exact ⟨a, rfl⟩
        let : T2Space ZHatMul := by
          change T2Space ZHat
          infer_instance
        exact (hrange ▸ hcompact).isClosed
    have hzmap : zHatPowNat n z ∈ f.toMonoidHom.range := by
      apply hclosed_le_range
      simpa using hmap
    have hzy : zHatPowNat n z = y := by
      apply Multiplicative.ext
      exact hz
    exact hzy ▸ hzmap

/-- The value of `d_K` on `Γ`, regarded in the subgroup `n ℤ̂`. -/
def frobeniusClosureDegreeInMulNatRange (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (a : D.frobeniusClosure K L hLK σ) :
    (zHatMulNat (D.frobeniusExponent K L hLK σ)).toAddMonoidHom.range := by
  refine ⟨(D.frobeniusClosureDegree K L hLK σ a).toAdd, ?_⟩
  have ha : D.frobeniusClosureDegree K L hLK σ a ∈
      (D.frobeniusClosureDegree K L hLK σ).toMonoidHom.range :=
    ⟨a, rfl⟩
  rw [D.frobeniusClosureDegree_range K L hLK σ] at ha
  exact ha

/-- The restricted Frobenius-closure degree has the stated underlying profinite value. -/
@[simp]
theorem frobeniusClosureDegreeInMulNatRange_coe (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (a : D.frobeniusClosure K L hLK σ) :
    (D.frobeniusClosureDegreeInMulNatRange K L hLK σ a).1 =
      (D.frobeniusClosureDegree K L hLK σ a).toAdd :=
  rfl

/-- The normalized degree `d_Σ = (1/n)d_K` on `Γ`. -/
def fixedFieldNormalizedDegree (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    D.frobeniusClosure K L hLK σ →ₜ* ZHatMul where
  toFun a := Multiplicative.ofAdd
    (zHatDivide (D.frobeniusExponent K L hLK σ)
      (D.frobeniusExponent_pos K L hLK σ)
      (D.frobeniusClosureDegreeInMulNatRange K L hLK σ a))
  map_one' := by
    apply Multiplicative.ext
    rw [show D.frobeniusClosureDegreeInMulNatRange K L hLK σ 1 = 0 by
      apply Subtype.ext
      exact congrArg Multiplicative.toAdd
        (map_one (D.frobeniusClosureDegree K L hLK σ))]
    exact map_zero (zHatDivide
      (D.frobeniusExponent K L hLK σ)
      (D.frobeniusExponent_pos K L hLK σ))
  map_mul' a b := by
    apply Multiplicative.ext
    rw [show D.frobeniusClosureDegreeInMulNatRange K L hLK σ (a * b) =
        D.frobeniusClosureDegreeInMulNatRange K L hLK σ a +
          D.frobeniusClosureDegreeInMulNatRange K L hLK σ b by
      apply Subtype.ext
      exact congrArg Multiplicative.toAdd
        (map_mul (D.frobeniusClosureDegree K L hLK σ) a b)]
    exact map_add (zHatDivide
      (D.frobeniusExponent K L hLK σ)
      (D.frobeniusExponent_pos K L hLK σ)) _ _
  continuous_toFun := by
    apply (map_continuous (zHatDivide
      (D.frobeniusExponent K L hLK σ)
      (D.frobeniusExponent_pos K L hLK σ))).comp
    exact Continuous.subtype_mk
      (D.frobeniusClosureDegree K L hLK σ).continuous_toFun
      (fun a =>
        (D.frobeniusClosureDegreeInMulNatRange K L hLK σ a).2)

/-- The defining identity `n d_Σ = d_K` on `Γ`. -/
theorem frobeniusExponent_nsmul_fixedFieldNormalizedDegree
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (a : D.frobeniusClosure K L hLK σ) :
    D.frobeniusExponent K L hLK σ •
        (D.fixedFieldNormalizedDegree K L hLK σ a).toAdd =
      (D.frobeniusClosureDegree K L hLK σ a).toAdd := by
  exact zHatMulNat_zHatDivide
    (D.frobeniusExponent K L hLK σ)
    (D.frobeniusExponent_pos K L hLK σ)
    (D.frobeniusClosureDegreeInMulNatRange K L hLK σ a)

/-- The chosen lift has normalized degree `1` over its fixed field. -/
@[simp]
theorem fixedFieldNormalizedDegree_generator (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    D.fixedFieldNormalizedDegree K L hLK σ
        (D.frobeniusInClosure K L hLK σ) =
      Multiplicative.ofAdd (1 : ZHat) := by
  apply Multiplicative.ext
  apply zHatMulNat_injective
    (D.frobeniusExponent_pos K L hLK σ)
  change D.frobeniusExponent K L hLK σ •
      (D.fixedFieldNormalizedDegree K L hLK σ
        (D.frobeniusInClosure K L hLK σ)).toAdd =
    D.frobeniusExponent K L hLK σ •
      (Multiplicative.ofAdd (1 : ZHat)).toAdd
  rw [D.frobeniusExponent_nsmul_fixedFieldNormalizedDegree]
  change (D.frobeniusClosureDegree K L hLK σ
      (D.frobeniusInClosure K L hLK σ)).toAdd =
    D.frobeniusExponent K L hLK σ • (1 : ZHat)
  rw [D.frobeniusClosureDegree_generator]
  rfl

/-- The normalized degree on `Γ` is onto. -/
theorem fixedFieldNormalizedDegree_surjective (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    Function.Surjective
      (D.fixedFieldNormalizedDegree K L hLK σ) := by
  intro z
  have hz : Multiplicative.ofAdd
      (D.frobeniusExponent K L hLK σ • z.toAdd) ∈
      (D.frobeniusClosureDegree K L hLK σ).toMonoidHom.range := by
    rw [D.frobeniusClosureDegree_range K L hLK σ]
    exact ⟨z.toAdd, rfl⟩
  obtain ⟨a, ha⟩ := hz
  refine ⟨a, ?_⟩
  apply Multiplicative.ext
  apply zHatMulNat_injective
    (D.frobeniusExponent_pos K L hLK σ)
  change D.frobeniusExponent K L hLK σ •
      (D.fixedFieldNormalizedDegree K L hLK σ a).toAdd =
    D.frobeniusExponent K L hLK σ • z.toAdd
  rw [D.frobeniusExponent_nsmul_fixedFieldNormalizedDegree]
  exact congrArg Multiplicative.toAdd ha

/-- The closed cyclic group `Γ` is totally disconnected. -/
theorem frobeniusClosure_totallyDisconnectedSpace (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    TotallyDisconnectedSpace (D.frobeniusClosure K L hLK σ) := by
  let : CompactSpace K.field.toSubgroup := by
    change CompactSpace K.field
    infer_instance
  let Q := K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK
  let : TotallyDisconnectedSpace Q :=
    QuotientGroup.totallyDisconnectedSpace_of_isClosed
      (D.extensionInertiaWithin K.field L hLK)
      (D.extensionInertiaWithin_isClosed K L hLK)
  infer_instance

/-- finiteness of the Frobenius fixed field, in the Galois-dual form: the closed subgroup
`Γ = closure ⟨σ⟩` has finite index in `G(\widetilde L|K)`, hence its
fixed field `Σ` is finite over `K`. -/
theorem frobeniusFixedField_finiteIndex (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (σ : D.FrobeniusElements K L hLK) :
    Finite
      ((K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) ⧸
        (D.frobeniusClosure K L hLK σ).toSubgroup) := by
  let Q := K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK
  let Γ : Subgroup Q :=
    (D.frobeniusClosure K L hLK σ).toSubgroup
  let dQ : Q →ₜ* ZHatMul :=
    D.extensionNormalizedDegreeContinuous K L hLK
  have hΓmap : Γ.map dQ.toMonoidHom =
      (D.frobeniusClosureDegree K L hLK σ).toMonoidHom.range := by
    ext z
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, hq⟩, rfl⟩
    · rintro ⟨q, rfl⟩
      exact ⟨q.1, q.2, rfl⟩
  have htopmap : (Subgroup.map dQ.toMonoidHom (⊤ : Subgroup Q)) = ⊤ := by
    apply top_unique
    intro z _
    obtain ⟨q, rfl⟩ :=
      D.extensionNormalizedDegreeContinuous_surjective K L hLK z
    exact ⟨q, trivial, rfl⟩
  have himage : (Γ.map dQ.toMonoidHom).relIndex
      ((⊤ : Subgroup Q).map dQ.toMonoidHom) ≠ 0 := by
    rw [hΓmap, htopmap, Subgroup.relIndex_top_right,
      D.frobeniusClosureDegree_range K L hLK σ,
      AddSubgroup.index_toSubgroup,
      zHatMulNat_range_index _
        (D.frobeniusExponent_pos K L hLK σ)]
    exact (D.frobeniusExponent_pos K L hLK σ).ne'
  let j := D.extensionDegreeKernelRestriction K L hLK
  let : Finite dQ.toMonoidHom.ker :=
    Finite.of_injective j
      (D.extensionDegreeKernelRestriction_injective K L hLK)
  let T : Subgroup Q := (⊤ : Subgroup Q) ⊓ dQ.toMonoidHom.ker
  let toKer : T → dQ.toMonoidHom.ker :=
    fun t => ⟨t.1, t.2.2⟩
  let : Finite T := Finite.of_injective toKer (by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun x : dQ.toMonoidHom.ker => x.1) hab)
  have hkernel : (Γ ⊓ dQ.toMonoidHom.ker).relIndex
      ((⊤ : Subgroup Q) ⊓ dQ.toMonoidHom.ker) ≠ 0 := by
    rw [Subgroup.relIndex]
    change ((Γ ⊓ dQ.toMonoidHom.ker).subgroupOf T).index ≠ 0
    exact Subgroup.index_ne_zero_of_finite
  have hrel : Γ.relIndex (⊤ : Subgroup Q) ≠ 0 := by
    rw [relIndex_eq_map_relIndex_mul_inf_ker_relIndex
      dQ.toMonoidHom le_top]
    exact Nat.mul_ne_zero himage hkernel
  apply (Subgroup.index_ne_zero_iff_finite).mp
  simpa [Γ, Q, Subgroup.relIndex_top_right] using hrel

/-- The procyclic degree isomorphism, kernel form: `d_Σ` has trivial kernel.  The
proof is the comparison of the finite quotients `Γ/Γ^m` with
`ℤ̂/mℤ̂`. -/
theorem frobeniusFixedField_normalizedDegree_injective (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    Function.Injective
      (D.fixedFieldNormalizedDegree K L hLK σ) := by
  let Γ := D.frobeniusClosure K L hLK σ
  let : CompactSpace K.field.toSubgroup := by
    change CompactSpace K.field
    infer_instance
  let : IsClosed
      (D.extensionInertiaWithin K.field L hLK : Set K.field.toSubgroup) :=
    D.extensionInertiaWithin_isClosed K L hLK
  let : TotallyDisconnectedSpace Γ :=
    D.frobeniusClosure_totallyDisconnectedSpace K L hLK σ
  let : CommGroup Γ :=
    D.frobeniusClosureCommGroup K L hLK σ
  apply injective_of_topologicallyGenerates_zHat_one
    (D.fixedFieldNormalizedDegree K L hLK σ)
    (D.frobeniusInClosure K L hLK σ)
  · exact D.frobeniusInClosure_topologicallyGenerates K L hLK σ
  · exact D.fixedFieldNormalizedDegree_generator K L hLK σ

/-- The procyclic degree isomorphism: `d_Σ` identifies `Γ` continuously with `ℤ̂`.
On the field side its trivial kernel says exactly
`\widetilde Σ = \widetilde L`. -/
def frobeniusFixedField_normalizedDegreeEquiv (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    D.frobeniusClosure K L hLK σ ≃ₜ* ZHatMul := by
  letI : CompactSpace K.field.toSubgroup := by
    change CompactSpace K.field
    infer_instance
  letI : IsClosed
      (D.extensionInertiaWithin K.field L hLK : Set K.field.toSubgroup) :=
    D.extensionInertiaWithin_isClosed K L hLK
  letI : T2Space ZHatMul := by
    change T2Space ZHat
    infer_instance
  exact continuousMulEquivOfBijectiveCompactToT2
    (D.fixedFieldNormalizedDegree K L hLK σ).toMonoidHom
    (D.fixedFieldNormalizedDegree K L hLK σ).continuous_toFun
    ⟨D.frobeniusFixedField_normalizedDegree_injective K L hLK σ,
      D.fixedFieldNormalizedDegree_surjective K L hLK σ⟩

/-- The normalized-degree equivalence on the Frobenius fixed field evaluates by restriction. -/
@[simp]
theorem frobeniusFixedField_normalizedDegreeEquiv_apply (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (a : D.frobeniusClosure K L hLK σ) :
    D.frobeniusFixedField_normalizedDegreeEquiv K L hLK σ a =
      D.fixedFieldNormalizedDegree K L hLK σ a :=
  rfl

end DegreeData

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_FrobeniusField
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteTower.totalQuotientFinite _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientAddCommGroup _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.ClassFormation.finiteNormQuotientAddCommGroup _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.maximalUnramifiedNormClass_eq_zero_iff _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientInfiniteEquiv_maximalUnramifiedNormClass _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientLift_maximalUnramifiedNormClass _root_.ClassFormation.DegreeData.maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClass _root_.ClassFormation.DegreeData.mem_maximalUnramifiedField_iff _root_.ClassFormation.DegreeData.mem_maximalUnramifiedNormSubgroup_iff _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteAbstractField.normToBase_index_eq_degree _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_eq_one_iff _root_.ClassFormation.FiniteGaloisSubextension.toGaloisSubextension_isTotallyRamified_iff _root_.ClassFormation.FiniteGaloisSubextension.toGaloisSubextension_isUnramified_iff _root_.ClassFormation.ValuationData.mem_unitAddSubgroup_iff _root_.ClassFormation.ValuationData.oneValue_coe _root_.ClassFormation.ValuationData.unitRepresentation_quotient_mk_apply _root_.ClassFormation.ValuationData.valuationAt_chosenPrimeElement _root_.ClassFormation.ValuationData.valuationAt_coe _root_.ClassFormation.ValuationData.valueModulo_apply _root_.ClassFormation.absoluteConjugateCosetEquiv_mk _root_.ClassFormation.canonicalValueQuotientMap_mk _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.finiteNormClass_add _root_.ClassFormation.finiteNormClass_eq_zero_iff _root_.ClassFormation.finiteNormClass_nsmul _root_.ClassFormation.finiteNormClass_sub _root_.ClassFormation.finiteNormClass_zero _root_.ClassFormation.finiteNormQuotientConcreteEquiv_finiteNormClass _root_.ClassFormation.finiteNormQuotientLift_finiteNormClass _root_.ClassFormation.finiteReciprocityNaturalityConjugation_mk _root_.ClassFormation.mem_nsmulImage_iff _root_.ClassFormation.normalExtensionAction_coe _root_.ClassFormation.nsmulImage_top _root_.ClassFormation.relativeConjugateCosetEquiv_mk _root_.ClassFormation.relativeCosetAction_mk _root_.ClassFormation.relativeCosetAction_zero _root_.ClassFormation.relativeNorm_apply_coe _root_.ClassFormation.relativeNorm_self _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.extensionFixedEndomorphism_apply_val _root_.KummerTheory.extensionFixedKernelElement_val _root_.KummerTheory.extensionFixedRepresentation_quotient_mk_apply_val _root_.KummerTheory.mem_extensionSubgroup_iff _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ClassFormation

open CyclicCohomology

/-!
# The abstract reciprocity construction: the field fixed by a Frobenius lift

This file passes from the group-dual `Γ` of the Frobenius fixed-field theorem to the actual
abstract field `Σ`.  Thus `G_Σ` is the inverse image of `Γ` under
`G_K → G_K / I_L`, embedded back into the ambient profinite group.
-/

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The subgroup `G_Σ ≤ G_K`: the inverse image of
`Γ = closure ⟨σ⟩` under `G_K → G_K / I_L`. -/
def frobeniusFixedSubgroupWithin (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) : Subgroup K.field.toSubgroup :=
  (D.frobeniusClosure K L hLK σ).toSubgroup.comap
    (QuotientGroup.mk' (D.extensionInertiaWithin K.field L hLK))

/-- Membership in the internal Frobenius-fixed subgroup is characterized by
fixedness under Frobenius. -/
@[simp]
theorem mem_frobeniusFixedSubgroupWithin_iff (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) (k : K.field.toSubgroup) :
    k ∈ D.frobeniusFixedSubgroupWithin K L hLK σ ↔
      QuotientGroup.mk k ∈
        (D.frobeniusClosure K L hLK σ).toSubgroup :=
  Iff.rfl

/-- The Frobenius-fixed subgroup inside the extension subgroup is closed. -/
theorem frobeniusFixedSubgroupWithin_isClosed (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    IsClosed
      (D.frobeniusFixedSubgroupWithin K L hLK σ : Set K.field.toSubgroup) := by
  change IsClosed
    ((QuotientGroup.mk' (D.extensionInertiaWithin K.field L hLK)) ⁻¹'
      ((D.frobeniusClosure K L hLK σ).toSubgroup : Set
        (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)))
  exact (D.frobeniusClosure K L hLK σ).isClosed'.preimage
    continuous_quotient_mk'

/-- The actual abstract field `Σ` fixed by the chosen Frobenius lift.
Its absolute Galois subgroup is the inverse image of `Γ`, now regarded as
a closed subgroup of the ambient group `G`. -/
def frobeniusFixedField (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) : ClosedSubgroup G where
  toSubgroup :=
    (D.frobeniusFixedSubgroupWithin K L hLK σ).map
      K.field.toSubgroup.subtype
  isClosed' := by
    change IsClosed
      (Subtype.val ''
        (D.frobeniusFixedSubgroupWithin K L hLK σ : Set K.field.toSubgroup))
    exact K.field.isClosed'.isClosedEmbedding_subtypeVal.isClosedMap _
      (D.frobeniusFixedSubgroupWithin_isClosed K L hLK σ)

/-- An element lies in the Frobenius fixed field exactly when Frobenius fixes its restriction. -/
@[simp]
theorem mem_frobeniusFixedField_iff (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) (g : G) :
    g ∈ D.frobeniusFixedField K L hLK σ ↔
      ∃ k : K.field.toSubgroup,
        k ∈ D.frobeniusFixedSubgroupWithin K L hLK σ ∧ k.1 = g := by
  rfl

/-- The field `Σ` extends `K`, i.e. `G_Σ ≤ G_K`. -/
theorem frobeniusFixedField_le (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    (D.frobeniusFixedField K L hLK σ).toSubgroup ≤ K.field.toSubgroup := by
  rintro g ⟨k, _, rfl⟩
  exact k.2

/-- Inside `G_K`, the subgroup attached to the actual field `Σ` is
literally the quotient-projection inverse image used in its definition. -/
theorem extensionSubgroup_frobeniusFixedField (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ)
        (D.frobeniusFixedField_le K L hLK σ) =
      D.frobeniusFixedSubgroupWithin K L hLK σ := by
  ext k
  change
    (k.1 ∈ D.frobeniusFixedField K L hLK σ) ↔
      k ∈ D.frobeniusFixedSubgroupWithin K L hLK σ
  rw [D.mem_frobeniusFixedField_iff K L hLK σ]
  constructor
  · rintro ⟨t, ht, htk⟩
    have : t = k := by
      apply Subtype.ext
      exact htk
    simpa [this] using ht
  · intro hk
    exact ⟨k, hk, rfl⟩

/-- The subgroup `I_L = G_{\widetilde L}` lies in `G_Σ`. -/
theorem extensionInertiaWithin_le_frobeniusFixedSubgroupWithin
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    D.extensionInertiaWithin K.field L hLK ≤
      D.frobeniusFixedSubgroupWithin K L hLK σ := by
  intro k hk
  change QuotientGroup.mk k ∈
    (D.frobeniusClosure K L hLK σ).toSubgroup
  rw [(QuotientGroup.eq_one_iff k).2 hk]
  exact Subgroup.one_mem _

/-- Ambient form of `I_L ≤ G_Σ`. -/
theorem fieldInertia_le_frobeniusFixedField (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    (D.fieldInertia L).toSubgroup ≤
      (D.frobeniusFixedField K L hLK σ).toSubgroup := by
  intro g hg
  let k : K.field.toSubgroup := ⟨g, hLK hg.1⟩
  have hkE : k ∈ extensionSubgroup K.field L hLK := hg.1
  have hkI : k ∈ D.fieldInertiaWithin K.field := hg.2
  exact ⟨k,
    D.extensionInertiaWithin_le_frobeniusFixedSubgroupWithin
      K L hLK σ ⟨hkE, hkI⟩,
    rfl⟩

/-- finiteness of the Frobenius fixed field on the actual field side: `Σ | K` is finite. -/
theorem frobeniusFixedField_finite (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (σ : D.FrobeniusElements K L hLK) :
    Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ)
          (D.frobeniusFixedField_le K L hLK σ)) := by
  let N := D.extensionInertiaWithin K.field L hLK
  let Q := K.field.toSubgroup ⧸ N
  let Γ : Subgroup Q :=
    (D.frobeniusClosure K L hLK σ).toSubgroup
  let S : Subgroup K.field.toSubgroup :=
    D.frobeniusFixedSubgroupWithin K L hLK σ
  let : Finite (Q ⧸ Γ) := by
    simpa [Q, Γ, N] using
      D.frobeniusFixedField_finiteIndex K L hLK σ
  have hΓ : Γ.index ≠ 0 := Γ.index_ne_zero_of_finite
  have hS : S.index ≠ 0 := by
    rw [show S = Γ.comap (QuotientGroup.mk' N) by rfl]
    rw [Subgroup.index_comap_of_surjective Γ
      (QuotientGroup.mk'_surjective N)]
    exact hΓ
  apply Nat.finite_of_card_ne_zero
  change
    (extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ)
      (D.frobeniusFixedField_le K L hLK σ)).index ≠ 0
  rw [D.extensionSubgroup_frobeniusFixedField K L hLK σ]
  exact hS

/-- The procyclic degree isomorphism, faithfully pulled back along
`G_K → G_K / I_L`: `G_Σ ∩ I_K = I_L`.  This is the subgroup form of
the equality `\widetilde Σ = \widetilde L`. -/
theorem frobeniusFixedSubgroupWithin_inf_fieldInertiaWithin
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    D.frobeniusFixedSubgroupWithin K L hLK σ ⊓
        D.fieldInertiaWithin K.field =
      D.extensionInertiaWithin K.field L hLK := by
  apply le_antisymm
  · intro k hk
    let a : D.frobeniusClosure K L hLK σ :=
      ⟨QuotientGroup.mk k, hk.1⟩
    have hda : D.fixedFieldNormalizedDegree K L hLK σ a = 1 := by
      apply Multiplicative.ext
      apply zHatMulNat_injective
        (D.frobeniusExponent_pos K L hLK σ)
      change D.frobeniusExponent K L hLK σ •
          (D.fixedFieldNormalizedDegree K L hLK σ a).toAdd =
        D.frobeniusExponent K L hLK σ • (1 : ZHatMul).toAdd
      rw [D.frobeniusExponent_nsmul_fixedFieldNormalizedDegree]
      change (D.normalizedDegree K k).toAdd =
        D.frobeniusExponent K L hLK σ • (1 : ZHatMul).toAdd
      have hdk : D.normalizedDegree K k = 1 := by
        change k ∈ (D.normalizedDegree K).toMonoidHom.ker
        rw [D.normalizedDegree_ker K]
        exact hk.2
      rw [hdk]
      simp
    have ha : a = 1 := by
      apply D.frobeniusFixedField_normalizedDegree_injective K L hLK σ
      simpa using hda
    apply (QuotientGroup.eq_one_iff k).mp
    exact congrArg Subtype.val ha
  · intro k hk
    exact
      ⟨D.extensionInertiaWithin_le_frobeniusFixedSubgroupWithin
          K L hLK σ hk,
        hk.2⟩

/-- Ambient version of the procyclic degree isomorphism: the maximal unramified
extensions of `Σ` and `L` have the same absolute Galois subgroup. -/
theorem frobeniusFixedField_fieldInertia (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    D.fieldInertia (D.frobeniusFixedField K L hLK σ) =
      D.fieldInertia L := by
  ext g
  constructor
  · intro hg
    obtain ⟨k, hkS, hkg⟩ := hg.1
    have hgdeg : D.degree g = 1 := hg.2
    have hkI : k ∈ D.fieldInertiaWithin K.field := by
      change D.degree k.1 = 1
      exact (congrArg D.degree hkg).trans hgdeg
    have hkN : k ∈ D.extensionInertiaWithin K.field L hLK := by
      rw [← D.frobeniusFixedSubgroupWithin_inf_fieldInertiaWithin
        K L hLK σ]
      exact ⟨hkS, hkI⟩
    exact ⟨hkg ▸ hkN.1, hg.2⟩
  · intro hg
    let k : K.field.toSubgroup := ⟨g, hLK hg.1⟩
    have hgdeg : D.degree g = 1 := hg.2
    have hkE : k ∈ extensionSubgroup K.field L hLK := hg.1
    have hkI : k ∈ D.fieldInertiaWithin K.field := hgdeg
    have hkS : k ∈ D.frobeniusFixedSubgroupWithin K L hLK σ :=
      D.extensionInertiaWithin_le_frobeniusFixedSubgroupWithin
        K L hLK σ ⟨hkE, hkI⟩
    exact ⟨⟨k, hkS, rfl⟩, hg.2⟩

/-- Restriction from the actual group `G_Σ` to the group-dual `Γ`. -/
def frobeniusFixedFieldToClosure (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    (D.frobeniusFixedField K L hLK σ).toSubgroup →*
      D.frobeniusClosure K L hLK σ where
  toFun s := by
    let k : K.field.toSubgroup :=
      Subgroup.inclusion (D.frobeniusFixedField_le K L hLK σ) s
    refine ⟨QuotientGroup.mk k, ?_⟩
    have hk : k ∈
        extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ)
          (D.frobeniusFixedField_le K L hLK σ) := s.2
    rw [D.extensionSubgroup_frobeniusFixedField K L hLK σ] at hk
    exact hk
  map_one' := by
    apply Subtype.ext
    rfl
  map_mul' := by
    intro a b
    apply Subtype.ext
    rfl

/-- The map from the Frobenius fixed field to the closure evaluates by the underlying inclusion. -/
@[simp]
theorem frobeniusFixedFieldToClosure_apply (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (s : (D.frobeniusFixedField K L hLK σ).toSubgroup) :
    (D.frobeniusFixedFieldToClosure K L hLK σ s).1 =
      QuotientGroup.mk
        (Subgroup.inclusion
          (D.frobeniusFixedField_le K L hLK σ) s) :=
  rfl

/-- Every element of the Frobenius closure lifts from the Frobenius fixed field. -/
theorem frobeniusFixedFieldToClosure_surjective (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    Function.Surjective (D.frobeniusFixedFieldToClosure K L hLK σ) := by
  intro a
  obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective
    (D.extensionInertiaWithin K.field L hLK) a.1
  have hkS : k ∈ D.frobeniusFixedSubgroupWithin K L hLK σ := by
    change (QuotientGroup.mk' (D.extensionInertiaWithin K.field L hLK)) k ∈
      (D.frobeniusClosure K L hLK σ).toSubgroup
    exact hk.symm ▸ a.2
  let s : (D.frobeniusFixedField K L hLK σ).toSubgroup :=
    ⟨k.1, ⟨k, hkS, rfl⟩⟩
  refine ⟨s, ?_⟩
  apply Subtype.ext
  exact hk

/-- The kernel of restriction `G_Σ → Γ` is precisely `I_Σ`; by
the procyclic degree isomorphism, this is also `I_L`. -/
theorem frobeniusFixedFieldToClosure_ker (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    (D.frobeniusFixedFieldToClosure K L hLK σ).ker =
      D.fieldInertiaWithin (D.frobeniusFixedField K L hLK σ) := by
  ext s
  let k : K.field.toSubgroup :=
    Subgroup.inclusion (D.frobeniusFixedField_le K L hLK σ) s
  have hkS : k ∈ D.frobeniusFixedSubgroupWithin K L hLK σ := by
    have hk : k ∈
        extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ)
          (D.frobeniusFixedField_le K L hLK σ) := s.2
    rw [D.extensionSubgroup_frobeniusFixedField K L hLK σ] at hk
    exact hk
  constructor
  · intro hs
    have hq : QuotientGroup.mk k = 1 :=
      congrArg Subtype.val hs
    have hkN : k ∈ D.extensionInertiaWithin K.field L hLK :=
      (QuotientGroup.eq_one_iff k).mp hq
    exact hkN.2
  · intro hs
    have hkI : k ∈ D.fieldInertiaWithin K.field := hs
    have hkN : k ∈ D.extensionInertiaWithin K.field L hLK := by
      rw [← D.frobeniusFixedSubgroupWithin_inf_fieldInertiaWithin
        K L hLK σ]
      exact ⟨hkS, hkI⟩
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff k).mpr hkN

/-- The canonical identification
`G_Σ / I_Σ ≃ Γ = Gal(\widetilde L / Σ)`. -/
def frobeniusFixedFieldQuotientEquiv (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    ((D.frobeniusFixedField K L hLK σ).toSubgroup ⧸
        D.fieldInertiaWithin (D.frobeniusFixedField K L hLK σ)) ≃*
      D.frobeniusClosure K L hLK σ :=
  (QuotientGroup.quotientMulEquivOfEq
      (D.frobeniusFixedFieldToClosure_ker K L hLK σ).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (D.frobeniusFixedFieldToClosure K L hLK σ)
      (D.frobeniusFixedFieldToClosure_surjective K L hLK σ))

/-- The Frobenius fixed-field quotient equivalence has the expected value on representatives. -/
@[simp]
theorem frobeniusFixedFieldQuotientEquiv_mk (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (s : (D.frobeniusFixedField K L hLK σ).toSubgroup) :
    D.frobeniusFixedFieldQuotientEquiv K L hLK σ
        (QuotientGroup.mk s) =
      D.frobeniusFixedFieldToClosure K L hLK σ s := by
  rfl

end DegreeData

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_FrobeniusSemigroup
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteTower.totalQuotientFinite _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientAddCommGroup _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.ClassFormation.finiteNormQuotientAddCommGroup _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.frobeniusFixedFieldQuotientEquiv_mk _root_.ClassFormation.DegreeData.frobeniusFixedFieldToClosure_apply _root_.ClassFormation.DegreeData.maximalUnramifiedNormClass_eq_zero_iff _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientInfiniteEquiv_maximalUnramifiedNormClass _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientLift_maximalUnramifiedNormClass _root_.ClassFormation.DegreeData.maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClass _root_.ClassFormation.DegreeData.mem_frobeniusFixedField_iff _root_.ClassFormation.DegreeData.mem_frobeniusFixedSubgroupWithin_iff _root_.ClassFormation.DegreeData.mem_maximalUnramifiedField_iff _root_.ClassFormation.DegreeData.mem_maximalUnramifiedNormSubgroup_iff _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteAbstractField.normToBase_index_eq_degree _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_eq_one_iff _root_.ClassFormation.FiniteGaloisSubextension.toGaloisSubextension_isTotallyRamified_iff _root_.ClassFormation.FiniteGaloisSubextension.toGaloisSubextension_isUnramified_iff _root_.ClassFormation.ValuationData.mem_unitAddSubgroup_iff _root_.ClassFormation.ValuationData.oneValue_coe _root_.ClassFormation.ValuationData.unitRepresentation_quotient_mk_apply _root_.ClassFormation.ValuationData.valuationAt_chosenPrimeElement _root_.ClassFormation.ValuationData.valuationAt_coe _root_.ClassFormation.ValuationData.valueModulo_apply _root_.ClassFormation.absoluteConjugateCosetEquiv_mk _root_.ClassFormation.canonicalValueQuotientMap_mk _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.finiteNormClass_add _root_.ClassFormation.finiteNormClass_eq_zero_iff _root_.ClassFormation.finiteNormClass_nsmul _root_.ClassFormation.finiteNormClass_sub _root_.ClassFormation.finiteNormClass_zero _root_.ClassFormation.finiteNormQuotientConcreteEquiv_finiteNormClass _root_.ClassFormation.finiteNormQuotientLift_finiteNormClass _root_.ClassFormation.finiteReciprocityNaturalityConjugation_mk _root_.ClassFormation.mem_nsmulImage_iff _root_.ClassFormation.normalExtensionAction_coe _root_.ClassFormation.nsmulImage_top _root_.ClassFormation.relativeConjugateCosetEquiv_mk _root_.ClassFormation.relativeCosetAction_mk _root_.ClassFormation.relativeCosetAction_zero _root_.ClassFormation.relativeNorm_apply_coe _root_.ClassFormation.relativeNorm_self _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.extensionFixedEndomorphism_apply_val _root_.KummerTheory.extensionFixedKernelElement_val _root_.KummerTheory.extensionFixedRepresentation_quotient_mk_apply_val _root_.KummerTheory.mem_extensionSubgroup_iff _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ClassFormation

open CyclicCohomology

/-!
# The abstract reciprocity construction: the Frobenius semigroup

The set `Frob(\widetilde L | K)` from  is closed under multiplication:
normalized degrees are positive natural numbers and add under products.
-/

noncomputable section

namespace DegreeData

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- Multiplication in this construction's Frobenius semigroup. -/
def frobeniusMul (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (CyclicCohomology.extensionSubgroup (G := G)
      K.field L hLK).Normal]
    (σ τ : D.FrobeniusElements K L hLK) :
    D.FrobeniusElements K L hLK := by
  let m := D.frobeniusExponent K L hLK σ
  let n := D.frobeniusExponent K L hLK τ
  refine ⟨σ.1 * τ.1, m + n,
    Nat.add_pos_left (D.frobeniusExponent_pos K L hLK σ) n, ?_⟩
  rw [map_mul,
    D.extensionNormalizedDegree_frobenius_eq_pow K L hLK σ,
    D.extensionNormalizedDegree_frobenius_eq_pow K L hLK τ,
    pow_add]

/--
Multiplication of Frobenius elements is induced by multiplication of their quotient
representatives.
-/
instance frobeniusElementsMul (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (CyclicCohomology.extensionSubgroup (G := G)
      K.field L hLK).Normal] :
    Mul (D.FrobeniusElements K L hLK) :=
  ⟨D.frobeniusMul K L hLK⟩

/-- Establishes the identity `(σ * τ).1 = σ.1 * τ.1`. -/
@[simp]
theorem frobeniusMul_coe (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (CyclicCohomology.extensionSubgroup (G := G)
      K.field L hLK).Normal]
    (σ τ : D.FrobeniusElements K L hLK) :
    (σ * τ).1 = σ.1 * τ.1 :=
  rfl

/--
`extensionNormalizedDegree_frobenius` satisfies the multiplication formula
`D.extensionNormalizedDegree K L hLK (σ * τ).1 = D.extensionNormalizedDegree K L hLK σ.1 *
D.extensionNormalizedDegree K L hLK τ.1`.
-/
@[simp]
theorem extensionNormalizedDegree_frobenius_mul (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (CyclicCohomology.extensionSubgroup (G := G)
      K.field L hLK).Normal]
    (σ τ : D.FrobeniusElements K L hLK) :
    D.extensionNormalizedDegree K L hLK (σ * τ).1 =
      D.extensionNormalizedDegree K L hLK σ.1 *
        D.extensionNormalizedDegree K L hLK τ.1 :=
  map_mul _ _ _

end DegreeData

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_ReciprocityDefinition
attribute [-instance] _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.ClassFormation.finiteNormQuotientAddCommGroup _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

universe u

namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# The abstract reciprocity construction, the reciprocity construction: the reciprocity map

For a Frobenius element `σ`, let `Σ` be its fixed field.  The reciprocity
class is the class of `N_{Σ|K}(π_Σ)` in
`A_K / N_{\widetilde L|K} A_{\widetilde L}`.  Independence of the prime
element is proved separately from the unit-cohomology axiom.
-/

noncomputable section

section frobeniusFixedFields

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- A finite intermediate-field package for the fixed field `Σ` of a
Frobenius element. -/
def frobeniusFixedIntermediateField (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (σ : D.FrobeniusElements K L hLK) :
    FiniteIntermediateField (D.maximalUnramifiedField L) K.field where
  field := D.frobeniusFixedField K L hLK σ
  above := D.fieldInertia_le_frobeniusFixedField K L hLK σ
  below := D.frobeniusFixedField_le K L hLK σ
  finite := D.frobeniusFixedField_finite K L hLK σ

/-- Finiteness of `Σ | k`, obtained from the finite tower `Σ | K | k`. -/
theorem frobeniusFixedField_absoluteFinite (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (σ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK
      (hLnormal := by
        simpa only [FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal)) :
    Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G)
        (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK
          (hLnormal := by
            simpa only [FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal) σ)
        (le_baseField
          (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK
            (hLnormal := by
              simpa only [FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal) σ))) := by
  let KR := K.toFiniteResidueAbstractField D
  let hLnormalKR : (extensionSubgroup KR.field L hLK).Normal := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal
  let hLfiniteKR : Finite
      (KR.field.toSubgroup ⧸ extensionSubgroup KR.field L hLK) := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLfinite
  let : Finite (K.field.toSubgroup ⧸
      extensionSubgroup K.field (D.frobeniusFixedField KR L hLK σ)
        (D.frobeniusFixedField_le KR L hLK σ)) :=
    D.frobeniusFixedField_finite KR L hLK σ
  exact relativeTowerQuotientFinite (baseField G) K.field
    (D.frobeniusFixedField KR L hLK σ)
    (D.frobeniusFixedField_le KR L hLK σ) (le_baseField K.field)

end DegreeData

end frobeniusFixedFields

section reciprocityValues

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

namespace DegreeData

/-- The reciprocity construction with an explicit prime element `π_Σ`. -/
def reciprocityValueOfPrime (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (σ : D.FrobeniusElements K L hLK)
    (π : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ)) :
    D.MaximalUnramifiedNormQuotient A K.field L := by
  letI : Finite (K.field.toSubgroup ⧸
      extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ)
        (D.frobeniusFixedField_le K L hLK σ)) :=
    D.frobeniusFixedField_finite K L hLK σ
  exact D.maximalUnramifiedNormClass A K.field L
    (relativeNorm A K.field (D.frobeniusFixedField K L hLK σ)
      (D.frobeniusFixedField_le K L hLK σ) π)

/-- **the reciprocity construction.** The reciprocity map on the Frobenius semigroup,
using the canonical chosen prime supplied by surjectivity of `v_Σ`.
The following independence theorem identifies this value with the formula
for every prime element. -/
def reciprocityMap (D : DegreeData G) (A : Rep ℤ G)
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)] :
    D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK
        (hLnormal := by
          simpa only [FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal) →
      D.MaximalUnramifiedNormQuotient A K.field L :=
  fun σ => by
    let KR := K.toFiniteResidueAbstractField D
    letI hLnormalKR : (extensionSubgroup KR.field L hLK).Normal := by
      simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal
    letI hLfiniteKR : Finite
        (KR.field.toSubgroup ⧸ extensionSubgroup KR.field L hLK) := by
      simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLfinite
    letI : Finite ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G)
          (D.frobeniusFixedField KR L hLK σ)
          (le_baseField (D.frobeniusFixedField KR L hLK σ))) :=
      D.frobeniusFixedField_absoluteFinite K L hLK σ
    let Sigma : FiniteAbstractField G :=
      ⟨D.frobeniusFixedField KR L hLK σ, inferInstance⟩
    exact D.reciprocityValueOfPrime A KR L hLK σ
      (v.chosenPrimeElement Sigma)

/--
The reciprocity map at a Frobenius element is represented by the chosen prime element in its
Frobenius fixed field.
-/
theorem reciprocityMap_eq_chosenPrime (D : DegreeData G) (A : Rep ℤ G)
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (σ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK
      (hLnormal := by
        simpa only [FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal)) :
    D.reciprocityMap A v K L hLK σ = by
      let KR := K.toFiniteResidueAbstractField D
      letI : (extensionSubgroup KR.field L hLK).Normal := by
        simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal
      letI hLfiniteKR : Finite
          (KR.field.toSubgroup ⧸ extensionSubgroup KR.field L hLK) := by
        simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLfinite
      letI : Finite ((baseField G).toSubgroup ⧸
          extensionSubgroup (baseField G)
            (D.frobeniusFixedField KR L hLK σ)
            (le_baseField (D.frobeniusFixedField KR L hLK σ))) :=
        D.frobeniusFixedField_absoluteFinite K L hLK σ
      let Sigma : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK σ, inferInstance⟩
      simpa only [Sigma, KR, FiniteAbstractField.toFiniteResidueAbstractField] using
        (D.reciprocityValueOfPrime A KR L hLK σ
          (v.chosenPrimeElement Sigma)) :=
  rfl

end DegreeData

end reciprocityValues

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_ReciprocityIndependence
attribute [-instance] _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.conjugateExtension_normal _root_.ClassFormation.finiteNormQuotientAddCommGroup _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClass _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_eq_one_iff _root_.ClassFormation.FiniteGaloisSubextension.toGaloisSubextension_isTotallyRamified_iff _root_.ClassFormation.FiniteGaloisSubextension.toGaloisSubextension_isUnramified_iff _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.finiteNormClass_add _root_.ClassFormation.finiteNormClass_eq_zero_iff _root_.ClassFormation.finiteNormClass_nsmul _root_.ClassFormation.finiteNormClass_sub _root_.ClassFormation.finiteNormClass_zero _root_.ClassFormation.finiteNormQuotientConcreteEquiv_finiteNormClass _root_.ClassFormation.finiteNormQuotientLift_finiteNormClass _root_.ClassFormation.finiteReciprocityNaturalityConjugation_mk _root_.ClassFormation.mem_normFilterBasis_iff _root_.ClassFormation.relativeConjugateCosetEquiv_mk _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

universe u

namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# The abstract reciprocity construction: independence of the prime element

This file supplies the finite-Galois cofinality and compositum argument used to prove that the reciprocity construction is independent of its prime element.
-/

noncomputable section

section groupTheoreticRefinements

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteIntermediateField

/-- The normal core of a finite intermediate field, embedded back into the
ambient absolute Galois group. -/
def normalCoreField [IsTopologicalGroup G]
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K) :
    ClosedSubgroup G where
  toSubgroup :=
    (extensionSubgroup K M.field M.below).normalCore.map
      K.toSubgroup.subtype
  isClosed' := by
    change IsClosed
      (Subtype.val ''
        ((extensionSubgroup K M.field M.below).normalCore : Set K.toSubgroup))
    exact K.isClosed'.isClosedEmbedding_subtypeVal.isClosedMap _
      ((extensionSubgroup K M.field M.below).normalCore_isClosed
        (extensionSubgroup_isClosed K M.field M.below))

/-- The normal core field lies below the field from which it is constructed. -/
theorem normalCoreField_le [IsTopologicalGroup G]
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K) :
    (M.normalCoreField).toSubgroup ≤ K.toSubgroup := by
  rintro g ⟨k, _, rfl⟩
  exact k.2

/-- The normal core is contained in the specified refinement field. -/
theorem normalCoreField_le_field [IsTopologicalGroup G]
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K) :
    (M.normalCoreField).toSubgroup ≤ M.field.toSubgroup := by
  rintro g ⟨k, hk, rfl⟩
  exact (mem_extensionSubgroup_iff K M.field M.below k).1
    ((extensionSubgroup K M.field M.below).normalCore_le hk)

/-- The subgroup representing the normal core field is the corresponding normal core. -/
theorem extensionSubgroup_normalCoreField [IsTopologicalGroup G]
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K) :
    extensionSubgroup K M.normalCoreField M.normalCoreField_le =
      (extensionSubgroup K M.field M.below).normalCore := by
  ext k
  constructor
  · intro hk
    obtain ⟨k', hk', hk'n⟩ := hk
    have hk'eq : k' = k := by
      apply Subtype.ext
      exact hk'n
    simpa [hk'eq] using hk'
  · intro hk
    exact ⟨k, hk, rfl⟩

/-- Every finite intermediate field admits a finite Galois refinement once
the bottom extension is normal. -/
def galoisRefinement [IsTopologicalGroup G]
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K)
    [hEnormal :
      (extensionSubgroup K E (M.above.trans M.below)).Normal] :
    FiniteIntermediateField E K where
  field := M.normalCoreField
  above := by
    intro e he
    let eK : K.toSubgroup := ⟨e, M.below (M.above he)⟩
    have heE : eK ∈ extensionSubgroup K E (M.above.trans M.below) :=
      (mem_extensionSubgroup_iff K E (M.above.trans M.below) eK).2 he
    have hle : extensionSubgroup K E (M.above.trans M.below) ≤
        extensionSubgroup K M.field M.below := by
      intro x hx
      apply (mem_extensionSubgroup_iff K M.field M.below x).2
      exact M.above
        ((mem_extensionSubgroup_iff K E (M.above.trans M.below) x).1 hx)
    have heCore : eK ∈ (extensionSubgroup K M.field M.below).normalCore :=
      (Subgroup.normal_le_normalCore.mpr hle) heE
    exact ⟨eK, heCore, rfl⟩
  below := M.normalCoreField_le
  finite := by
    let H := extensionSubgroup K M.field M.below
    let : H.FiniteIndex :=
      @Subgroup.finiteIndex_of_finite_quotient K.toSubgroup _ H M.finite
    let : H.normalCore.FiniteIndex := inferInstance
    rw [M.extensionSubgroup_normalCoreField]
    infer_instance

/-- A Galois refinement lies below the original finite field. -/
theorem galoisRefinement_le_field [IsTopologicalGroup G]
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K)
    [_hEnormal :
      (extensionSubgroup K E (M.above.trans M.below)).Normal] :
    (M.galoisRefinement).field.toSubgroup ≤ M.field.toSubgroup :=
  M.normalCoreField_le_field

/-- The subgroup representing a Galois refinement is normal. -/
instance galoisRefinement_normal [IsTopologicalGroup G]
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K)
    [hEnormal :
      (extensionSubgroup K E (M.above.trans M.below)).Normal] :
    (extensionSubgroup K (M.galoisRefinement).field
      (M.galoisRefinement).below).Normal := by
  change (extensionSubgroup K M.normalCoreField M.normalCoreField_le).Normal
  rw [M.extensionSubgroup_normalCoreField]
  infer_instance

/-- The compositum of the two finite refinements has finite relative quotient. -/
theorem compositumWith_finite
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K)
    (S : ClosedSubgroup G) (hSK : S.toSubgroup ≤ K.toSubgroup) :
    Finite (S.toSubgroup ⧸
      extensionSubgroup S (M.compositumWith S) (M.compositumWith_le_right S)) := by
  let : Finite (K.toSubgroup ⧸
      extensionSubgroup K M.field M.below) := M.finite
  have hMK : M.field.toSubgroup.relIndex K.toSubgroup ≠ 0 := by
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite
  have hinter := Subgroup.relIndex_inter_ne_zero hMK S.toSubgroup
  have hKinfS : K.toSubgroup ⊓ S.toSubgroup = S.toSubgroup :=
    inf_eq_right.mpr hSK
  rw [hKinfS] at hinter
  apply Nat.finite_of_card_ne_zero
  change (extensionSubgroup S (M.compositumWith S)
      (M.compositumWith_le_right S)).index ≠ 0
  have hsub : extensionSubgroup S (M.compositumWith S)
      (M.compositumWith_le_right S) =
      M.field.toSubgroup.subgroupOf S.toSubgroup := by
    ext x
    rw [mem_extensionSubgroup_iff, Subgroup.mem_subgroupOf]
    change (x.1 ∈ M.field.toSubgroup ∧ x.1 ∈ S.toSubgroup) ↔
      x.1 ∈ M.field.toSubgroup
    exact and_iff_left x.2
  rw [hsub]
  simpa [Subgroup.relIndex] using hinter

/-- The compositum of normal refinements is again normal. -/
theorem compositumWith_normal
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K)
    (S : ClosedSubgroup G) (hSK : S.toSubgroup ≤ K.toSubgroup)
    [hMnormal : (extensionSubgroup K M.field M.below).Normal] :
    (extensionSubgroup S (M.compositumWith S)
      (M.compositumWith_le_right S)).Normal := by
  constructor
  intro p hp s
  have hpP : p.1 ∈ (M.compositumWith S).toSubgroup :=
    (mem_extensionSubgroup_iff S (M.compositumWith S)
      (M.compositumWith_le_right S) p).1 hp
  let pK : K.toSubgroup := ⟨p.1, hSK p.2⟩
  let sK : K.toSubgroup := ⟨s.1, hSK s.2⟩
  have hpM : pK ∈ extensionSubgroup K M.field M.below :=
    (mem_extensionSubgroup_iff K M.field M.below pK).2 hpP.1
  have hconjM : sK * pK * sK⁻¹ ∈
      extensionSubgroup K M.field M.below :=
    hMnormal.conj_mem pK hpM sK
  have hconjM' : s.1 * p.1 * s.1⁻¹ ∈ M.field.toSubgroup := by
    have := (mem_extensionSubgroup_iff K M.field M.below _).1 hconjM
    change (sK * pK * sK⁻¹).1 ∈ M.field.toSubgroup
    exact this
  apply (mem_extensionSubgroup_iff S (M.compositumWith S)
    (M.compositumWith_le_right S) _).2
  refine ⟨hconjM', ?_⟩
  exact S.toSubgroup.mul_mem
      (S.toSubgroup.mul_mem s.2 p.2) (S.toSubgroup.inv_mem s.2)

/-- The compositum of two finite extensions of `K` is finite over `K`.
Contravariantly this is the finite-index theorem for an intersection. -/
theorem compositumWith_finite_over_base
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K)
    (S : ClosedSubgroup G) (hSK : S.toSubgroup ≤ K.toSubgroup)
    [hSfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K S hSK)] :
    Finite (K.toSubgroup ⧸ extensionSubgroup K (M.compositumWith S)
      ((M.compositumWith_le_right S).trans hSK)) := by
  have hMindex : M.field.toSubgroup.relIndex K.toSubgroup ≠ 0 := by
    rw [Subgroup.relIndex]
    exact @Subgroup.index_ne_zero_of_finite K.toSubgroup _
      (extensionSubgroup K M.field M.below) M.finite
  have hSindex : S.toSubgroup.relIndex K.toSubgroup ≠ 0 := by
    rw [Subgroup.relIndex]
    exact @Subgroup.index_ne_zero_of_finite K.toSubgroup _
      (extensionSubgroup K S hSK) hSfinite
  apply Nat.finite_of_card_ne_zero
  change (extensionSubgroup K (M.compositumWith S)
      ((M.compositumWith_le_right S).trans hSK)).index ≠ 0
  have hsub : extensionSubgroup K (M.compositumWith S)
      ((M.compositumWith_le_right S).trans hSK) =
      (M.field.toSubgroup ⊓ S.toSubgroup).subgroupOf K.toSubgroup := by
    ext x
    rw [mem_extensionSubgroup_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    rfl
  rw [hsub]
  simpa only [Subgroup.relIndex] using
    Subgroup.relIndex_inf_ne_zero hMindex hSindex

/-- If `P | K` is finite and `P` contains the intermediate field `M`, then
`P | M` is finite. -/
theorem finite_extension_of_le
    {P M K : ClosedSubgroup G}
    (hPK : P.toSubgroup ≤ K.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    (hPM : P.toSubgroup ≤ M.toSubgroup)
    [hPfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K P hPK)] :
    Finite (M.toSubgroup ⧸ extensionSubgroup M P hPM) := by
  have hPKindex : P.toSubgroup.relIndex K.toSubgroup ≠ 0 := by
    rw [Subgroup.relIndex]
    exact @Subgroup.index_ne_zero_of_finite K.toSubgroup _
      (extensionSubgroup K P hPK) hPfinite
  have hPMindex : P.toSubgroup.relIndex M.toSubgroup ≠ 0 := by
    intro hzero
    have hmul := Subgroup.relIndex_mul_relIndex
      P.toSubgroup M.toSubgroup K.toSubgroup hPM hMK
    rw [hzero, zero_mul] at hmul
    exact hPKindex hmul.symm
  apply Nat.finite_of_card_ne_zero
  change (extensionSubgroup M P hPM).index ≠ 0
  simpa [Subgroup.relIndex] using hPMindex

end FiniteIntermediateField

namespace DegreeData

/-- In a finite unramified Galois extension, the restriction of any
degree-one lift is a generator.  This common form is used both in the universal norm-descent lemma
and in the explicit unramified norm-quotient calculation. -/
theorem quotient_generator_of_unramified_degree_one (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (extensionSubgroup K.field L hLK).Normal]
    [hfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D)
    (φ : K.field.toSubgroup)
    (hφ : D.normalizedDegree K φ =
      Multiplicative.ofAdd (1 : ZHat)) :
    ∀ x : K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK,
      x ∈ Subgroup.zpowers (QuotientGroup.mk φ) := by
  intro x
  obtain ⟨q, hqx⟩ := D.frobeniusRestriction_surjective K L hLK x
  obtain ⟨n, _hn, hdegree⟩ := q.2
  let t : K.field.toSubgroup := Quotient.out q.1
  have htq :
      (QuotientGroup.mk t :
        K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) = q.1 :=
    Quotient.out_eq' q.1
  have hdt : D.normalizedDegree K t =
      (Multiplicative.ofAdd (1 : ZHat)) ^ n := by
    calc
      D.normalizedDegree K t =
          D.extensionNormalizedDegree K L hLK
            (QuotientGroup.mk t) := rfl
      _ = D.extensionNormalizedDegree K L hLK q.1 :=
        congrArg (D.extensionNormalizedDegree K L hLK) htq
      _ = _ := hdegree
  let z : K.field.toSubgroup := t⁻¹ * φ ^ n
  have hzI : z ∈ D.fieldInertiaWithin K.field := by
    rw [← D.normalizedDegree_ker K]
    change D.normalizedDegree K z = 1
    calc
      D.normalizedDegree K z =
          (D.normalizedDegree K t)⁻¹ *
            (D.normalizedDegree K φ) ^ n := by
        simp [z, map_mul, map_inv, map_pow]
      _ = ((Multiplicative.ofAdd (1 : ZHat)) ^ n)⁻¹ *
            (Multiplicative.ofAdd (1 : ZHat)) ^ n := by
        rw [hdt, hφ]
      _ = 1 := by simp
  have hzL : z.1 ∈ L.toSubgroup :=
    ((DegreeData.AbstractExtension.mk L K.field hLK).isUnramified_iff_inertia_le D).1
      hUnramified ⟨z.2, hzI⟩
  have hzE : z ∈ extensionSubgroup K.field L hLK :=
    (mem_extensionSubgroup_iff K.field L hLK z).2 hzL
  have htgen :
      (QuotientGroup.mk t : K.field.toSubgroup ⧸
        extensionSubgroup K.field L hLK) = (QuotientGroup.mk φ) ^ n := by
    apply QuotientGroup.eq.mpr
    simpa [z] using hzE
  have htx :
      (QuotientGroup.mk t : K.field.toSubgroup ⧸
        extensionSubgroup K.field L hLK) = x := by
    calc
      QuotientGroup.mk t = D.extensionRestriction K.field L hLK
          (QuotientGroup.mk t) := rfl
      _ = D.extensionRestriction K.field L hLK q.1 :=
        congrArg (D.extensionRestriction K.field L hLK) htq
      _ = x := hqx
  have hxpow : x = (QuotientGroup.mk φ) ^ n := htx.symm.trans htgen
  rw [hxpow]
  exact Subgroup.mem_zpowers_iff.mpr ⟨(n : ℤ), by simp⟩

/-- A finite unramified Galois quotient is generated by the restriction of
an element of normalized degree `1`.  This is the cyclicity input needed to
use the finite-cyclic Tate complexes in the unit-cohomology axiom. -/
theorem exists_quotient_generator_of_unramified
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (extensionSubgroup K.field L hLK).Normal]
    [hfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D) :
    ∃ g : K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK,
      ∀ x, x ∈ Subgroup.zpowers g := by
  obtain ⟨φ, hφ⟩ := D.normalizedDegree_surjective K
    (Multiplicative.ofAdd (1 : ZHat))
  refine ⟨QuotientGroup.mk φ, ?_⟩
  exact D.quotient_generator_of_unramified_degree_one
    K L hLK hUnramified φ hφ

end DegreeData

end groupTheoreticRefinements

section reciprocityIndependence

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- **Independence of the prime element.**
Assuming the unit-cohomology axiom, replacing the chosen prime of the Frobenius fixed field
by any other prime does not change the reciprocity class. -/
theorem reciprocityValueOfPrime_eq_reciprocityMap
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (σ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK
      (hLnormal := by
        simpa only [FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal))
    (π : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK
        (hLnormal := by
          simpa only [FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal) σ))
    (hπ :
      let Sigma : FiniteAbstractField G :=
        { field := D.frobeniusFixedField
            (K.toFiniteResidueAbstractField D) L hLK
            (hLnormal := by
              simpa only [FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal) σ
          finite := D.frobeniusFixedField_absoluteFinite K L hLK σ }
      v.IsPrimeElement Sigma π) :
    D.reciprocityValueOfPrime A (K.toFiniteResidueAbstractField D)
        L hLK
        (hLnormal := by
          simpa only [FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal)
        (hLfinite := by
          simpa only [FiniteAbstractField.toFiniteResidueAbstractField] using hLfinite) σ π =
      D.reciprocityMap A v K L hLK σ := by
  let KR := K.toFiniteResidueAbstractField D
  let hLnormalKR : (extensionSubgroup KR.field L hLK).Normal := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal
  let hLfiniteKR : Finite
      (KR.field.toSubgroup ⧸ extensionSubgroup KR.field L hLK) := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLfinite
  let S := D.frobeniusFixedField KR L hLK σ
  let E := D.maximalUnramifiedField L
  have hSK : S.toSubgroup ≤ K.field.toSubgroup :=
    D.frobeniusFixedField_le KR L hLK σ
  let hSfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field S hSK) :=
    D.frobeniusFixedField_finite KR L hLK σ
  let hSabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) S (le_baseField S)) :=
    D.frobeniusFixedField_absoluteFinite K L hLK σ
  let Sigma : FiniteAbstractField G := ⟨S, hSabsolute⟩
  have hπSigma : v.IsPrimeElement Sigma π := by
    simpa [Sigma, S, KR] using hπ
  let π₀ : ambientFixedAddSubgroup A S := v.chosenPrimeElement Sigma
  let u : v.unitAddSubgroup Sigma :=
    ⟨π - π₀, v.sub_chosenPrimeElement_mem_unitAddSubgroup Sigma hπSigma⟩
  rw [D.reciprocityMap_eq_chosenPrime A v K L hLK σ]
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  change relativeNorm A K.field S hSK π -
      relativeNorm A K.field S hSK π₀ ∈ infiniteNormSubgroup A E K.field
  rw [← map_sub]
  change relativeNorm A K.field S hSK u.1 ∈
    infiniteNormSubgroup A E K.field
  rw [mem_infiniteNormSubgroup_iff]
  intro M
  let hEnormal :
      (extensionSubgroup K.field E
        (D.maximalUnramifiedField_le_of_le hLK)).Normal :=
    D.extensionSubgroup_maximalUnramifiedField_normal K.field L hLK
  let R := M.galoisRefinement
  let P := R.compositumWith S
  have hES : E.toSubgroup ≤ S.toSubgroup :=
    D.fieldInertia_le_frobeniusFixedField KR L hLK σ
  have hPS : P.toSubgroup ≤ S.toSubgroup :=
    R.compositumWith_le_right S
  have hPK : P.toSubgroup ≤ K.field.toSubgroup := hPS.trans hSK
  have hPM : P.toSubgroup ≤ M.field.toSubgroup :=
    (R.compositumWith_le_left S).trans M.galoisRefinement_le_field
  let hRnormal :
      (extensionSubgroup K.field R.field R.below).Normal := inferInstance
  let hPSnormal :
      (extensionSubgroup S P hPS).Normal :=
    FiniteIntermediateField.compositumWith_normal R S hSK
  let hPSfinite : Finite
      (S.toSubgroup ⧸ extensionSubgroup S P hPS) :=
    R.compositumWith_finite S hSK
  let hPKfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field P hPK) :=
    R.compositumWith_finite_over_base S hSK
  have hSinertia : D.fieldInertia S = E := by
    dsimp [S, E]
    exact D.frobeniusFixedField_fieldInertia KR L hLK σ
  have hPSunramified :
      (DegreeData.AbstractExtension.mk P S hPS).IsUnramified D := by
    rw [(DegreeData.AbstractExtension.mk P S hPS).isUnramified_iff_inertia_le D]
    intro x hx
    change x ∈ R.field.toSubgroup ∧ x ∈ S.toSubgroup
    refine ⟨R.above ?_, hx.1⟩
    have hxI : x ∈ D.fieldInertia S := ⟨hx.1, hx.2⟩
    rw [hSinertia] at hxI
    exact hxI
  let Sresidue := Sigma.toFiniteResidueAbstractField D
  let hPSnormalResidue :
      (extensionSubgroup Sresidue.field P hPS).Normal := by
    simpa only [Sresidue, Sigma,
      FiniteAbstractField.toFiniteResidueAbstractField] using hPSnormal
  let hPSfiniteResidue : Finite
      (Sresidue.field.toSubgroup ⧸
        extensionSubgroup Sresidue.field P hPS) := by
    simpa only [Sresidue, Sigma,
      FiniteAbstractField.toFiniteResidueAbstractField] using hPSfinite
  obtain ⟨g, hg⟩ :=
    D.exists_quotient_generator_of_unramified
      Sresidue P hPS (by
        simpa only [Sresidue, Sigma,
          FiniteAbstractField.toFiniteResidueAbstractField] using hPSunramified)
  let hPabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) P (le_baseField P)) :=
    relativeTowerQuotientFinite (baseField G) S P hPS (le_baseField S)
  let : Fintype (S.toSubgroup ⧸ extensionSubgroup S P hPS) :=
    Fintype.ofFinite _
  let Kuc : FiniteAbstractField G := Sigma
  let Euc : FiniteUnramifiedCyclicExtension D Kuc :=
    { field := P
      below := hPS
      normal := hPSnormal
      finite := hPSfinite
      generator := g
      generates := hg
      unramified := hPSunramified }
  have hzero :
      CategoryTheory.Limits.IsZero
          (tateCohomology (Euc.unitRepresentation v) 0) ∧
        CategoryTheory.Limits.IsZero
          (tateCohomology (Euc.unitRepresentation v) (-1)) :=
    hAxiom Kuc Euc
  obtain ⟨ε, hε⟩ :=
    v.exists_unit_relativeNorm_eq_of_tateHZero_isZero
      Euc.toFiniteAbstractFieldExtension Euc.normal
        Euc.toFiniteAbstractFieldExtension_isUnramified
        g hg hzero.1 u
  let hMfinite : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field M.field M.below) := M.finite
  let hPMfinite : Finite
      (M.field.toSubgroup ⧸ extensionSubgroup M.field P hPM) :=
    FiniteIntermediateField.finite_extension_of_le hPK M.below hPM
  change relativeNorm A K.field S hSK u.1 ∈
    (relativeNorm A K.field M.field M.below).range
  refine ⟨relativeNorm A M.field P hPM ε.1, ?_⟩
  let TMP : DegreeData.FiniteTower G :=
    { top := P
      middle := M.field
      base := K.field
      top_le_middle := hPM
      middle_le_base := M.below
      finiteTopQuotient := hPMfinite
      finiteBaseQuotient := hMfinite }
  let TSP : DegreeData.FiniteTower G :=
    { top := P
      middle := S
      base := K.field
      top_le_middle := hPS
      middle_le_base := hSK
      finiteTopQuotient := hPSfinite
      finiteBaseQuotient := hSfinite }
  calc
    relativeNorm A K.field M.field M.below
        (relativeNorm A M.field P hPM ε.1) =
        relativeNorm A K.field P hPK ε.1 :=
      TMP.norm_trans_apply A ε.1
    _ = relativeNorm A K.field S hSK
        (relativeNorm A S P hPS ε.1) :=
      (TSP.norm_trans_apply A ε.1).symm
    _ = relativeNorm A K.field S hSK u.1 := congrArg _ hε

end DegreeData

end reciprocityIndependence

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_UnramifiedNormQuotient
attribute [-instance] _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.conjugateExtension_normal _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_eq_one_iff _root_.ClassFormation.FiniteGaloisSubextension.toGaloisSubextension_isTotallyRamified_iff _root_.ClassFormation.FiniteGaloisSubextension.toGaloisSubextension_isUnramified_iff _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.finiteReciprocityNaturalityConjugation_mk _root_.ClassFormation.mem_normFilterBasis_iff _root_.ClassFormation.relativeConjugateCosetEquiv_mk _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

universe u

namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# The abstract reciprocity construction, the unramified norm-quotient equivalence: the unramified norm quotient

For a finite unramified Galois extension `L / K`, normalized valuation
identifies the actual norm quotient `A_K / N_{L/K} A_L` with
`ℤ / [L : K]ℤ`.  The only non-formal part of injectivity is the unit
correction: the unit-cohomology axiom (`H⁰ = 0`) makes every unit of `K` the norm
of a unit of `L`.
-/

noncomputable section

section unramifiedFrobenius

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The degree-one lift `φ_K` used in the unramified norm-quotient equivalence. -/
def chosenUnramifiedFrobeniusLift
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (extensionSubgroup K.field L hLK).Normal] :
    D.FrobeniusElements K L hLK := by
  let φ : K.field.toSubgroup := Classical.choose
    (D.normalizedDegree_surjective K
      (Multiplicative.ofAdd (1 : ZHat)))
  have hφ : D.normalizedDegree K φ =
      Multiplicative.ofAdd (1 : ZHat) :=
    Classical.choose_spec
      (D.normalizedDegree_surjective K
        (Multiplicative.ofAdd (1 : ZHat)))
  refine ⟨QuotientGroup.mk φ, 1, Nat.zero_lt_one, ?_⟩
  rw [D.extensionNormalizedDegree_mk K L hLK φ, hφ, pow_one]

/--
Establishes the identity `D.frobeniusExponent K L hLK (D.chosenUnramifiedFrobeniusLift K L hLK) =
1`.
-/
@[simp]
theorem chosenUnramifiedFrobeniusLift_exponent
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (extensionSubgroup K.field L hLK).Normal] :
    D.frobeniusExponent K L hLK
      (D.chosenUnramifiedFrobeniusLift K L hLK) = 1 := by
  apply proCIntegerOne_pow_nat_injective
  calc
    (Multiplicative.ofAdd (1 : ZHat)) ^
        D.frobeniusExponent K L hLK
          (D.chosenUnramifiedFrobeniusLift K L hLK) =
      D.extensionNormalizedDegree K L hLK
        (D.chosenUnramifiedFrobeniusLift K L hLK).1 :=
      (D.extensionNormalizedDegree_frobenius_eq_pow K L hLK
        (D.chosenUnramifiedFrobeniusLift K L hLK)).symm
    _ = Multiplicative.ofAdd (1 : ZHat) := by
      change D.normalizedDegree K
          (Classical.choose
            (D.normalizedDegree_surjective K
              (Multiplicative.ofAdd (1 : ZHat)))) = _
      exact Classical.choose_spec
        (D.normalizedDegree_surjective K
          (Multiplicative.ofAdd (1 : ZHat)))
    _ = (Multiplicative.ofAdd (1 : ZHat)) ^ 1 := (pow_one _).symm

end DegreeData

end unramifiedFrobenius

section valuationQuotient

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

namespace ValuationData

theorem valueModulo_eq_zero_iff
    (v : ValuationData D A) (n : ℕ) (hn : 0 < n)
    (z : v.valueGroup) :
    v.valueModulo n hn z = 0 ↔ ∃ w : v.valueGroup, z = n • w := by
  constructor
  · intro hz
    have hq :
        (QuotientAddGroup.mk' (nsmulWithin v.valueGroup n)) z = 0 := by
      apply (v.cyclic_value_quotients n hn).injective
      change v.valueModulo n hn z = v.valueModulo n hn 0
      rw [hz, map_zero]
    obtain ⟨w, hw⟩ :=
      (QuotientAddGroup.eq_zero_iff z).1 hq
    exact ⟨w, hw.symm⟩
  · rintro ⟨w, rfl⟩
    have hq :
        (QuotientAddGroup.mk' (nsmulWithin v.valueGroup n)) (n • w) = 0 := by
      apply (QuotientAddGroup.eq_zero_iff _).2
      exact ⟨w, rfl⟩
    change (v.cyclic_value_quotients n hn)
        ((QuotientAddGroup.mk' (nsmulWithin v.valueGroup n)) (n • w)) = 0
    rw [hq, map_zero]

def unramifiedValuationHom
    (v : ValuationData D A) (K : FiniteAbstractField G)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)] :
    ambientFixedAddSubgroup A K.field →+
      ZMod ((FiniteAbstractFieldExtension.ofInclusion L K hLK).degree : ℕ) :=
  (v.valueModulo
      ((FiniteAbstractFieldExtension.ofInclusion L K hLK).degree : ℕ)
      (FiniteAbstractFieldExtension.ofInclusion L K hLK).degree.property).comp
    (v.valuationAt K)

theorem finiteNormSubgroup_le_unramifiedValuationHom_ker
    (v : ValuationData D A)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D) :
    finiteNormSubgroup A K.field L hLK ≤
      (v.unramifiedValuationHom K L hLK).ker := by
  rintro _ ⟨a, rfl⟩
  let E := FiniteAbstractFieldExtension.ofInclusion L K hLK
  let n := (E.degree : ℕ)
  have hUn : E.IsUnramified D := by
    change (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D
    exact hUnramified
  have htower := v.normalizedValuation_tower E a
  change (E.residueDegree D : ℕ) • _ = _ at htower
  rw [E.residueDegree_eq_degree_of_isUnramified D hUn] at htower
  have hval : v.valuationAt K (relativeNorm A K.field L hLK a) =
      n • v.valuationAt E.field a := by
    apply Subtype.ext
    exact htower.symm
  change v.valueModulo n E.degree.property
      (v.valuationAt K (relativeNorm A K.field L hLK a)) = 0
  rw [hval]
  exact (v.valueModulo_eq_zero_iff n E.degree.property _).2
    ⟨v.valuationAt E.field a, rfl⟩

/-- The valuation map induced on the finite norm quotient. -/
def unramifiedNormQuotientValuation
    (v : ValuationData D A)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D) :
    FiniteNormQuotient A K.field L hLK →+
      ZMod ((FiniteAbstractFieldExtension.ofInclusion L K hLK).degree : ℕ) :=
  finiteNormQuotientLift A K.field L hLK
    (v.unramifiedValuationHom K L hLK)
    (v.finiteNormSubgroup_le_unramifiedValuationHom_ker K L hLK hUnramified)

/--
Establishes the identity `v.unramifiedNormQuotientValuation K L hLK hUnramified (finiteNormClass A
K.field L hLK a) = v.unramifiedValuationHom K L hLK a`.
-/
@[simp]
theorem unramifiedNormQuotientValuation_finiteNormClass
    (v : ValuationData D A)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D)
    (a : ambientFixedAddSubgroup A K.field) :
    v.unramifiedNormQuotientValuation K L hLK hUnramified
        (finiteNormClass A K.field L hLK a) =
      v.unramifiedValuationHom K L hLK a :=
  rfl

end ValuationData

end valuationQuotient

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_CanonicalUnramifiedNormQuotient
attribute [-instance] _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.FiniteGaloisSubextension.toGaloisSubextension_isTotallyRamified_iff _root_.ClassFormation.FiniteGaloisSubextension.toGaloisSubextension_isUnramified_iff _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.mem_normFilterBasis_iff _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# The abstract reciprocity construction: the canonical unramified valuation quotient

the valuation-quotient axiom supplies the order of `Z / nZ`.  The construction then uses the
canonical reduction inherited from `Z ⊆ ℤ̂`, rather than an arbitrary
isomorphism with `ℤ / nℤ`.  This file constructs that canonical map and
proves directly that it induces the unramified norm-quotient isomorphism
used in the unramified norm-quotient equivalence.
-/

noncomputable section

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

namespace ValuationData

/-- Reduction modulo `n` restricted to the actual value subgroup
`Z ⊆ ℤ̂`. -/
def canonicalValueReduction
    (v : ValuationData D A) (n : ℕ) (hn : 0 < n) :
    v.valueGroup →+ ZMod n :=
  v.valueModulo n hn

/-- The canonical value reduction sends the unit element to zero. -/
@[simp]
theorem canonicalValueReduction_one
    (v : ValuationData D A) (n : ℕ) (hn : 0 < n) :
    v.canonicalValueReduction n hn v.oneValue = 1 := by
  change zHatReduction n hn (1 : ZHat) = 1
  rfl

/-- Canonical reduction descended to `Z / nZ`. -/
def canonicalValueQuotientHom
    (v : ValuationData D A) (n : ℕ) (hn : 0 < n) :
    (v.valueGroup ⧸ nsmulWithin v.valueGroup n) →+ ZMod n :=
  v.canonicalQuotientMap n hn

/-- The quotient homomorphism evaluates on a coset through canonical value reduction. -/
@[simp]
theorem canonicalValueQuotientHom_mk
    (v : ValuationData D A) (n : ℕ) (hn : 0 < n)
    (z : v.valueGroup) :
    v.canonicalValueQuotientHom n hn
      (QuotientAddGroup.mk' (nsmulWithin v.valueGroup n) z) =
        v.canonicalValueReduction n hn z := by
  rfl

/-- Canonical valuation modulo `[L : K]` on `A_K`. -/
def canonicalUnramifiedValuationHom
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G) :
    ambientFixedAddSubgroup A E.base.field →+ ZMod (E.degree : ℕ) :=
  (v.canonicalValueReduction (E.degree : ℕ) E.degree.property).comp
    (v.valuationAt E.base)

theorem finiteNormSubgroup_le_canonicalUnramifiedValuationHom_ker
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hUnramified : E.IsUnramified D) :
    finiteNormSubgroup A E.base.field E.field.field E.below ≤
      (v.canonicalUnramifiedValuationHom E).ker := by
  rintro _ ⟨a, rfl⟩
  let n := (E.degree : ℕ)
  let hn : 0 < n := E.degree.property
  have htower := v.normalizedValuation_tower E a
  have hresidueDegree :
      ((E.toFiniteResidueAbstractExtension D).residueDegree : ℕ) =
        (E.degree : ℕ) := by
    exact E.residueDegree_eq_degree_of_isUnramified D hUnramified
  dsimp only at htower
  rw [hresidueDegree] at htower
  have htower' :
      n • ((v.valuationAt E.field a : v.valueGroup) : ZHat) =
        ((v.valuationAt E.base
          (relativeNorm A E.base.field E.field.field E.below a) :
          v.valueGroup) : ZHat) := by
    simpa [n] using htower
  change zHatReduction n hn
      (v.valuationAt E.base
        (relativeNorm A E.base.field E.field.field E.below a) : ZHat) = 0
  rw [← htower', map_nsmul]
  simp [n]

/-- The canonical valuation induced on the finite unramified norm
quotient. -/
def canonicalUnramifiedNormQuotientValuation
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hUnramified : E.IsUnramified D) :
    FiniteNormQuotient A E.base.field E.field.field E.below →+
      ZMod (E.degree : ℕ) :=
  finiteNormQuotientLift A E.base.field E.field.field E.below
    (v.canonicalUnramifiedValuationHom E)
    (v.finiteNormSubgroup_le_canonicalUnramifiedValuationHom_ker
      E hUnramified)

/-- Valuation sends a finite norm class to its canonical unramified quotient value. -/
@[simp]
theorem canonicalUnramifiedNormQuotientValuation_finiteNormClass
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hUnramified : E.IsUnramified D)
    (a : ambientFixedAddSubgroup A E.base.field) :
    v.canonicalUnramifiedNormQuotientValuation E hUnramified
      (finiteNormClass A E.base.field E.field.field E.below a) =
        v.canonicalUnramifiedValuationHom E a := by
  rfl

end ValuationData

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_FiniteIntermediateCompositum
attribute [-instance] _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.conjugateExtension_normal _root_.ClassFormation.finiteNormQuotientAddCommGroup _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ClassFormation

open CyclicCohomology

/-!
# Finite intermediate fields: composita and absolute finiteness

These are the finite-stage closure facts used in the proof of the universal norm-descent lemma.  The compositum of two finite intermediate fields is their
intersection on the Galois-group side.
-/

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace FiniteIntermediateField

/-- The compositum of two finite intermediate fields of `E / K`. -/
def compositum {E K : ClosedSubgroup G}
    (M N : FiniteIntermediateField E K) :
    FiniteIntermediateField E K where
  field := M.field ⊓ N.field
  above := fun x hx => ⟨M.above hx, N.above hx⟩
  below := (inf_le_left :
    (M.field ⊓ N.field).toSubgroup ≤ M.field.toSubgroup).trans M.below
  finite := by
    let : Finite
        (K.toSubgroup ⧸ extensionSubgroup K N.field N.below) := N.finite
    exact M.compositumWith_finite_over_base N.field N.below

/-- Proves the bound `(M.compositum N).field.toSubgroup ≤ M.field.toSubgroup`. -/
theorem compositum_le_left {E K : ClosedSubgroup G}
    (M N : FiniteIntermediateField E K) :
    (M.compositum N).field.toSubgroup ≤ M.field.toSubgroup :=
  inf_le_left

/-- Proves the bound `(M.compositum N).field.toSubgroup ≤ N.field.toSubgroup`. -/
theorem compositum_le_right {E K : ClosedSubgroup G}
    (M N : FiniteIntermediateField E K) :
    (M.compositum N).field.toSubgroup ≤ N.field.toSubgroup :=
  inf_le_right

/-- A finite intermediate field over a finite abstract base field is itself
finite over the global base field. -/
theorem absoluteFinite {E K : ClosedSubgroup G}
    [hKfinite : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) K (le_baseField K))]
    (M : FiniteIntermediateField E K) :
    Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) M.field (le_baseField M.field)) := by
  let : Finite
      (K.toSubgroup ⧸ extensionSubgroup K M.field M.below) := M.finite
  exact relativeTowerQuotientFinite (baseField G) K M.field M.below
    (le_baseField K)

end FiniteIntermediateField

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_CoreFrobeniusNorm
attribute [-instance] _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.finiteNormQuotientAddCommGroup _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.chosenUnramifiedFrobeniusLift_exponent _root_.ClassFormation.DegreeData.maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClass _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_eq_one_iff _root_.ClassFormation.FiniteGaloisSubextension.toGaloisSubextension_isTotallyRamified_iff _root_.ClassFormation.FiniteGaloisSubextension.toGaloisSubextension_isUnramified_iff _root_.ClassFormation.ValuationData.canonicalUnramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.canonicalValueQuotientHom_mk _root_.ClassFormation.ValuationData.canonicalValueReduction_one _root_.ClassFormation.ValuationData.unramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.finiteNormClass_add _root_.ClassFormation.finiteNormClass_eq_zero_iff _root_.ClassFormation.finiteNormClass_nsmul _root_.ClassFormation.finiteNormClass_sub _root_.ClassFormation.finiteNormClass_zero _root_.ClassFormation.finiteNormQuotientConcreteEquiv_finiteNormClass _root_.ClassFormation.finiteNormQuotientLift_finiteNormClass _root_.ClassFormation.mem_normFilterBasis_iff _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

universe u

namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# The abstract reciprocity construction, the Frobenius norm-identity lemma

The operator `φ_n` is written additively as the sum of the first
`n` powers of the actual quotient action.  This file compares that sum with
the relative norm through the Frobenius fixed field `Σ` constructed in
the Frobenius fixed-field theorem.
-/

noncomputable section

open scoped BigOperators

section inertiaQuotients

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The inclusion of inertia cosets into the finite extension cosets. -/
noncomputable def inertiaCosetToExtensionCoset (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup) :
    ((D.maximalUnramifiedField K).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) →
      (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
  Quotient.map'
    (fun x : (D.maximalUnramifiedField K).toSubgroup =>
      (⟨x.1, x.2.1⟩ : K.toSubgroup))
    (by
      intro x y hxy
      rw [QuotientGroup.leftRel_apply] at hxy ⊢
      exact hxy.1)

theorem inertiaCosetToExtensionCoset_injective (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup) :
    Function.Injective (D.inertiaCosetToExtensionCoset K L hLK) := by
  intro x y hxy
  refine Quotient.inductionOn₂' x y ?_ hxy
  intro a b hab
  apply Quotient.sound'
  rw [QuotientGroup.leftRel_apply]
  have habE :
      (⟨a.1, a.2.1⟩ : K.toSubgroup)⁻¹ * ⟨b.1, b.2.1⟩ ∈
        extensionSubgroup K L hLK := by
    exact QuotientGroup.leftRel_apply.mp (Quotient.exact' hab)
  refine ⟨habE, ?_⟩
  change D.degree (a.1⁻¹ * b.1) = 1
  rw [map_mul, map_inv]
  change (D.degree a.1)⁻¹ * D.degree b.1 = 1
  rw [show D.degree a.1 = 1 from a.2.2,
    show D.degree b.1 = 1 from b.2.2]
  simp

/-- Finiteness of `\widetilde L | \widetilde K`, derived from the finite
Galois extension `L | K`; no separate finiteness assumption is introduced. -/
theorem maximalUnramifiedExtension_finite (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    Finite
      ((D.maximalUnramifiedField K).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) :=
  Finite.of_injective (D.inertiaCosetToExtensionCoset K L hLK)
    (D.inertiaCosetToExtensionCoset_injective K L hLK)

/-- The actual quotient `G(\widetilde L/\widetilde K)` is the kernel of
`d_K` inside `G(\widetilde L/K)`. -/
noncomputable def inertiaCosetToDegreeKernel (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal] :
    ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) →
      (D.extensionNormalizedDegreeContinuous K L hLK).toMonoidHom.ker :=
  fun r => Quotient.liftOn' r
    (fun x : (D.maximalUnramifiedField K.field).toSubgroup => by
      let k : K.field.toSubgroup := ⟨x.1, x.2.1⟩
      refine ⟨QuotientGroup.mk k, ?_⟩
      change D.normalizedDegree K k = 1
      change k ∈ (D.normalizedDegree K).toMonoidHom.ker
      rw [D.normalizedDegree_ker K]
      exact x.2.2)
    (by
      intro x y hxy
      apply Subtype.ext
      apply QuotientGroup.eq.mpr
      rw [← D.extensionSubgroup_maximalUnramifiedField K.field L hLK]
      rw [QuotientGroup.leftRel_apply] at hxy
      exact hxy)

theorem inertiaCosetToDegreeKernel_bijective (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal] :
    Function.Bijective (D.inertiaCosetToDegreeKernel K L hLK) := by
  constructor
  · intro x y hxy
    refine Quotient.inductionOn₂' x y ?_ hxy
    intro a b hab
    apply Quotient.sound'
    rw [QuotientGroup.leftRel_apply]
    have hq : QuotientGroup.mk (⟨a.1, a.2.1⟩ : K.field.toSubgroup) =
        QuotientGroup.mk (⟨b.1, b.2.1⟩ : K.field.toSubgroup) :=
      congrArg Subtype.val hab
    have hkN :
        (⟨a.1, a.2.1⟩ : K.field.toSubgroup)⁻¹ * ⟨b.1, b.2.1⟩ ∈
          D.extensionInertiaWithin K.field L hLK :=
      QuotientGroup.eq.mp hq
    refine ⟨hkN.1, ?_⟩
    change D.degree (a.1⁻¹ * b.1) = 1
    rw [map_mul, map_inv]
    change (D.degree a.1)⁻¹ * D.degree b.1 = 1
    rw [show D.degree a.1 = 1 from a.2.2,
      show D.degree b.1 = 1 from b.2.2]
    simp
  · intro z
    obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective
      (D.extensionInertiaWithin K.field L hLK) z.1
    have hkNorm : D.normalizedDegree K k = 1 := by
      change D.extensionNormalizedDegreeContinuous K L hLK
          ((QuotientGroup.mk' (D.extensionInertiaWithin K.field L hLK)) k) = 1
      exact (congrArg
        (D.extensionNormalizedDegreeContinuous K L hLK) hk).trans z.2
    have hkI : k ∈ D.fieldInertiaWithin K.field := by
      rw [← D.normalizedDegree_ker K]
      exact hkNorm
    let x : (D.maximalUnramifiedField K.field).toSubgroup :=
      ⟨k.1, ⟨k.2, hkI⟩⟩
    refine ⟨QuotientGroup.mk x, ?_⟩
    apply Subtype.ext
    exact hk

/-- Canonical actual-group identification used in the Frobenius norm-identity lemma. -/
noncomputable def inertiaQuotientDegreeKernelEquiv (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal] :
    ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) ≃
      (D.extensionNormalizedDegreeContinuous K L hLK).toMonoidHom.ker :=
  Equiv.ofBijective (D.inertiaCosetToDegreeKernel K L hLK)
    (D.inertiaCosetToDegreeKernel_bijective K L hLK)

end DegreeData

end inertiaQuotients

section quotientActions

/-!
Mathlib's `Rep ℤ G` requires the coefficient ring and acting group to share
a universe; `IntegralRepGroupType` names that shared boundary.
-/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The actual action of `G(\widetilde L/K)` on `A_{\widetilde L}`. -/
def frobeniusQuotientAction (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    (q : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    ambientFixedAddSubgroup A (D.maximalUnramifiedField L) :=
  Quotient.liftOn' q
    (fun k : K.toSubgroup =>
      normalExtensionAction A K (D.maximalUnramifiedField L)
        (D.maximalUnramifiedField_le_of_le hLK)
        (D.extensionSubgroup_maximalUnramifiedField_normal K L hLK) k a)
    (by
      intro x y hxy
      rw [QuotientGroup.leftRel_apply] at hxy
      rw [← D.extensionSubgroup_maximalUnramifiedField K L hLK] at hxy
      let l : (D.maximalUnramifiedField L).toSubgroup :=
        ⟨x.1⁻¹ * y.1, hxy⟩
      have hy : y = x * Subgroup.inclusion
          (D.maximalUnramifiedField_le_of_le hLK) l := by
        apply Subtype.ext
        simp [l]
      apply Subtype.ext
      change A.ρ x.1 a.1 = A.ρ y.1 a.1
      rw [hy]
      change A.ρ x.1 a.1 = A.ρ (x.1 * l.1) a.1
      rw [map_mul]
      change A.ρ x.1 a.1 = A.ρ x.1 (A.ρ l.1 a.1)
      rw [a.2 l])

/--
Establishes the identity `D.frobeniusQuotientAction A K L hLK (QuotientGroup.mk k) a =
normalExtensionAction A K (D.maximalUnramifiedField L) (D.maximalUnramifiedField_le_of_le hLK)
(D.extensionSubgroup_maximalUnramifiedField_normal K L hLK) k a`.
-/
@[simp]
theorem frobeniusQuotientAction_mk (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    (k : K.toSubgroup)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    D.frobeniusQuotientAction A K L hLK (QuotientGroup.mk k) a =
      normalExtensionAction A K (D.maximalUnramifiedField L)
        (D.maximalUnramifiedField_le_of_le hLK)
        (D.extensionSubgroup_maximalUnramifiedField_normal K L hLK) k a :=
  rfl

/-- Conjugation by an element of `G_K` preserves the inertia group `I_K`.
The inverse convention is chosen so that the resulting coset permutation
rewrites `τ·φ` as `φ·(φ⁻¹τφ)`. -/
def inertiaConjugationEquiv (D : DegreeData G) (K : ClosedSubgroup G)
    (k : K.toSubgroup) :
    (D.maximalUnramifiedField K).toSubgroup ≃
      (D.maximalUnramifiedField K).toSubgroup where
  toFun x := ⟨k.1⁻¹ * x.1 * k.1, ⟨by
    exact K.toSubgroup.mul_mem
      (K.toSubgroup.mul_mem (K.toSubgroup.inv_mem k.2) x.2.1) k.2, by
    change D.degree (k.1⁻¹ * x.1 * k.1) = 1
    have hx : D.degree x.1 = 1 := x.2.2
    rw [map_mul, map_mul, map_inv, hx]
    simp⟩⟩
  invFun x := ⟨k.1 * x.1 * k.1⁻¹, ⟨by
    exact K.toSubgroup.mul_mem
      (K.toSubgroup.mul_mem k.2 x.2.1) (K.toSubgroup.inv_mem k.2), by
    change D.degree (k.1 * x.1 * k.1⁻¹) = 1
    have hx : D.degree x.1 = 1 := x.2.2
    rw [map_mul, map_mul, map_inv, hx]
    simp⟩⟩
  left_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv x := by
    apply Subtype.ext
    simp [mul_assoc]

/-- Conjugation by `G_K` also preserves `I_L` when `L/K` is Galois. -/
theorem conjugate_mem_maximalUnramifiedField (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    (k : K.toSubgroup) (l : (D.maximalUnramifiedField L).toSubgroup) :
    k.1⁻¹ * l.1 * k.1 ∈ (D.maximalUnramifiedField L).toSubgroup := by
  let lK : K.toSubgroup := ⟨l.1, hLK l.2.1⟩
  have hcK : k⁻¹ * lK * k ∈ extensionSubgroup K L hLK := by
    simpa [lK] using hLnormal.conj_mem lK l.2.1 k⁻¹
  refine ⟨?_, ?_⟩
  · exact hcK
  · change D.degree (k.1⁻¹ * l.1 * k.1) = 1
    have hlDegree : D.degree l.1 = 1 := l.2.2
    rw [map_mul, map_mul, map_inv, hlDegree]
    simp

/-- The coset permutation `τ ↦ φ⁻¹τφ` of
`G(\widetilde L/\widetilde K)`. -/
noncomputable def inertiaConjugationCosetEquiv (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    (k : K.toSubgroup) :
    ((D.maximalUnramifiedField K).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) ≃
      ((D.maximalUnramifiedField K).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) :=
  Quotient.congr (D.inertiaConjugationEquiv K k) (by
    intro x y
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
    constructor
    · intro hxy
      let l : (D.maximalUnramifiedField L).toSubgroup :=
        ⟨x.1⁻¹ * y.1, hxy⟩
      have hl := D.conjugate_mem_maximalUnramifiedField K L hLK k l
      change (k.1⁻¹ * x.1 * k.1)⁻¹ * (k.1⁻¹ * y.1 * k.1) ∈
        (D.maximalUnramifiedField L).toSubgroup
      simpa [l, mul_assoc] using hl
    · intro hxy
      let l : (D.maximalUnramifiedField L).toSubgroup :=
        ⟨(k.1⁻¹ * x.1 * k.1)⁻¹ * (k.1⁻¹ * y.1 * k.1), hxy⟩
      have hl := D.conjugate_mem_maximalUnramifiedField K L hLK k⁻¹ l
      change x.1⁻¹ * y.1 ∈ (D.maximalUnramifiedField L).toSubgroup
      simpa [l, mul_assoc] using hl)

@[simp]
theorem inertiaConjugationCosetEquiv_mk (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    (k : K.toSubgroup) (x : (D.maximalUnramifiedField K).toSubgroup) :
    D.inertiaConjugationCosetEquiv K L hLK k (QuotientGroup.mk x) =
      QuotientGroup.mk (D.inertiaConjugationEquiv K k x) :=
  rfl

theorem relativeCosetAction_inertiaConjugation (D : DegreeData G)
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    (k : K.toSubgroup)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L))
    (r : (D.maximalUnramifiedField K).toSubgroup ⧸
      extensionSubgroup (D.maximalUnramifiedField K)
        (D.maximalUnramifiedField L)
        (D.maximalUnramifiedField_mono hLK)) :
    relativeCosetAction A (D.maximalUnramifiedField K)
        (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
        (normalExtensionAction A K (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_le_of_le hLK)
          (D.extensionSubgroup_maximalUnramifiedField_normal K L hLK) k a) r =
      A.ρ k.1
        (relativeCosetAction A (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
          a (D.inertiaConjugationCosetEquiv K L hLK k r)) := by
  refine Quotient.inductionOn' r ?_
  intro x
  rw [relativeCosetAction_mk, D.inertiaConjugationCosetEquiv_mk,
    relativeCosetAction_mk, normalExtensionAction_coe]
  calc
    A.ρ x.1 (A.ρ k.1 a.1) = A.ρ (x.1 * k.1) a.1 := by
      rw [map_mul]
      rfl
    _ = A.ρ (k.1 * (k.1⁻¹ * x.1 * k.1)) a.1 := by
      simp [mul_assoc]
    _ = A.ρ k.1 (A.ρ (k.1⁻¹ * x.1 * k.1) a.1) := by
      rw [map_mul]
      rfl

/-- The norm `N_{\widetilde L/\widetilde K}` is equivariant for the
normalizing `G_K`-action. -/
theorem relativeNorm_normalizingAction (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    [Finite ((D.maximalUnramifiedField K).toSubgroup ⧸
      extensionSubgroup (D.maximalUnramifiedField K)
        (D.maximalUnramifiedField L)
        (D.maximalUnramifiedField_mono hLK))]
    (k : K.toSubgroup)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    ((relativeNorm A (D.maximalUnramifiedField K)
      (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
      (normalExtensionAction A K (D.maximalUnramifiedField L)
        (D.maximalUnramifiedField_le_of_le hLK)
        (D.extensionSubgroup_maximalUnramifiedField_normal K L hLK) k a) :
      ambientFixedAddSubgroup A (D.maximalUnramifiedField K)) : A.V) =
      A.ρ k.1
        ((relativeNorm A (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) a :
          ambientFixedAddSubgroup A (D.maximalUnramifiedField K)) : A.V) := by
  let R := (D.maximalUnramifiedField K).toSubgroup ⧸
    extensionSubgroup (D.maximalUnramifiedField K)
      (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
  let e := D.inertiaConjugationCosetEquiv K L hLK k
  let := Fintype.ofFinite R
  simp only [relativeNorm_apply_coe, relativeNormValue]
  calc
    ∑ r : R, relativeCosetAction A (D.maximalUnramifiedField K)
        (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
        (normalExtensionAction A K (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_le_of_le hLK)
          (D.extensionSubgroup_maximalUnramifiedField_normal K L hLK) k a) r =
      ∑ r : R, A.ρ k.1
        (relativeCosetAction A (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
          a (e r)) := by
      apply Finset.sum_congr rfl
      intro r _
      exact D.relativeCosetAction_inertiaConjugation A K L hLK k a r
    _ = A.ρ k.1
        (∑ r : R, relativeCosetAction A (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
          a (e r)) := by
      rw [map_sum]
    _ = A.ρ k.1
        (∑ r : R, relativeCosetAction A (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
          a r) := by
      rw [e.sum_comp]

/--
Relative norm commutes with the Frobenius quotient action after including the norm into the upper
fixed field.
-/
theorem relativeNorm_frobeniusQuotientAction (D : DegreeData G)
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    [Finite ((D.maximalUnramifiedField K).toSubgroup ⧸
      extensionSubgroup (D.maximalUnramifiedField K)
        (D.maximalUnramifiedField L)
        (D.maximalUnramifiedField_mono hLK))]
    (q : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    ((relativeNorm A (D.maximalUnramifiedField K)
      (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
      (D.frobeniusQuotientAction A K L hLK q a) :
      ambientFixedAddSubgroup A (D.maximalUnramifiedField K)) : A.V) =
      ((D.frobeniusQuotientAction A K L hLK q
        (fixedFieldInclusion A (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
          (relativeNorm A (D.maximalUnramifiedField K)
            (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
            a)) : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
        A.V) := by
  let k : K.toSubgroup := Quotient.out q
  have hq : q = QuotientGroup.mk k := (Quotient.out_eq' q).symm
  rw [hq]
  exact D.relativeNorm_normalizingAction A K L hLK k a

/-- Additive form of the `φ_n = 1 + φ + ⋯ + φ^{n-1}`. -/
def frobeniusPowerSum (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    (φ : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK)
    (n : ℕ)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    ambientFixedAddSubgroup A (D.maximalUnramifiedField L) :=
  ∑ i : Fin n, D.frobeniusQuotientAction A K L hLK (φ ^ i.1) a

/--
Establishes the identity `((D.frobeniusPowerSum A K L hLK φ n a : ambientFixedAddSubgroup A
(D.maximalUnramifiedField L)) : A.V) = ∑ i : Fin n, (D.frobeniusQuotientAction A K L hLK (φ ^ i.1)
a : A.V)`.
-/
@[simp]
theorem frobeniusPowerSum_coe (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    (φ : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK)
    (n : ℕ)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    ((D.frobeniusPowerSum A K L hLK φ n a :
      ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) : A.V) =
      ∑ i : Fin n,
        (D.frobeniusQuotientAction A K L hLK (φ ^ i.1) a : A.V) :=
  by
    change (ambientFixedAddSubgroup A
        (D.maximalUnramifiedField L)).subtype
      (∑ i : Fin n,
        D.frobeniusQuotientAction A K L hLK (φ ^ i.1) a) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rfl

end DegreeData

end quotientActions

section frobeniusCosetEquivalences

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Quotient projection identifies the actual cosets `G_K/G_Σ` with
the cosets of `Γ` in `G(\widetilde L/K)`. -/
noncomputable def frobeniusFixedCosetToClosureCoset
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    (K.field.toSubgroup ⧸
        extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ)
          (D.frobeniusFixedField_le K L hLK σ)) →
      ((K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) ⧸
        (D.frobeniusClosure K L hLK σ).toSubgroup) :=
  Quotient.map'
    (QuotientGroup.mk' (D.extensionInertiaWithin K.field L hLK))
    (by
      intro x y hxy
      rw [QuotientGroup.leftRel_apply] at hxy ⊢
      rw [D.extensionSubgroup_frobeniusFixedField K L hLK σ] at hxy
      exact hxy)

theorem frobeniusFixedCosetToClosureCoset_bijective
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    Function.Bijective
      (D.frobeniusFixedCosetToClosureCoset K L hLK σ) := by
  constructor
  · intro x y hxy
    refine Quotient.inductionOn₂' x y ?_ hxy
    intro a b hab
    apply Quotient.sound'
    rw [QuotientGroup.leftRel_apply]
    rw [D.extensionSubgroup_frobeniusFixedField K L hLK σ]
    have hrel := QuotientGroup.leftRel_apply.mp (Quotient.exact' hab)
    exact hrel
  · intro z
    refine Quotient.inductionOn' z ?_
    intro q
    obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective
      (D.extensionInertiaWithin K.field L hLK) q
    refine ⟨QuotientGroup.mk k, ?_⟩
    change QuotientGroup.mk
        ((QuotientGroup.mk' (D.extensionInertiaWithin K.field L hLK)) k) =
      QuotientGroup.mk q
    rw [hk]

/-- Defines `frobeniusFixedCosetClosureEquiv`. -/
noncomputable def frobeniusFixedCosetClosureEquiv
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    (K.field.toSubgroup ⧸
        extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ)
          (D.frobeniusFixedField_le K L hLK σ)) ≃
      ((K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) ⧸
        (D.frobeniusClosure K L hLK σ).toSubgroup) :=
  Equiv.ofBijective
    (D.frobeniusFixedCosetToClosureCoset K L hLK σ)
    (D.frobeniusFixedCosetToClosureCoset_bijective K L hLK σ)

/-- The procyclic degree isomorphism says that `Γ` meets the inertia kernel trivially. -/
theorem frobeniusClosure_inf_degreeKernel (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    (D.frobeniusClosure K L hLK σ).toSubgroup ⊓
        (D.extensionNormalizedDegreeContinuous K L hLK).toMonoidHom.ker =
      ⊥ := by
  ext q
  constructor
  · intro hq
    let a : D.frobeniusClosure K L hLK σ := ⟨q, hq.1⟩
    have hclosure : D.frobeniusClosureDegree K L hLK σ a = 1 := hq.2
    have hfixed : D.fixedFieldNormalizedDegree K L hLK σ a = 1 := by
      apply Multiplicative.ext
      apply zHatMulNat_injective
        (D.frobeniusExponent_pos K L hLK σ)
      change D.frobeniusExponent K L hLK σ •
          (D.fixedFieldNormalizedDegree K L hLK σ a).toAdd =
        D.frobeniusExponent K L hLK σ • (1 : ZHatMul).toAdd
      rw [D.frobeniusExponent_nsmul_fixedFieldNormalizedDegree]
      rw [hclosure]
      simp
    have ha : a = 1 :=
      D.frobeniusFixedField_normalizedDegree_injective K L hLK σ (by
        simpa using hfixed)
    exact congrArg Subtype.val ha
  · intro hq
    have : q = 1 := hq
    subst q
    exact ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩

/-- Candidate enumeration of the cosets of `Γ`: an inertia element followed
by one of the first `n=d_K(σ)` powers of a degree-one Frobenius. -/
def kernelPowerCosetMap (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ σ : D.FrobeniusElements K L hLK) :
    (D.extensionNormalizedDegreeContinuous K L hLK).toMonoidHom.ker ×
        Fin (D.frobeniusExponent K L hLK σ) →
      ((K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) ⧸
        (D.frobeniusClosure K L hLK σ).toSubgroup) :=
  fun p => QuotientGroup.mk (φ.1 ^ p.2.1 * p.1.1)

theorem kernelPowerCosetMap_injective (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ σ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1) :
    Function.Injective (D.kernelPowerCosetMap K L hLK φ σ) := by
  rintro ⟨h, i⟩ ⟨h', j⟩ hij
  let n := D.frobeniusExponent K L hLK σ
  let dQ := D.extensionNormalizedDegreeContinuous K L hLK
  have hn : 0 < n := D.frobeniusExponent_pos K L hLK σ
  have hdφ : dQ φ.1 =
      Multiplicative.ofAdd (1 : ZHat) := by
    change D.extensionNormalizedDegree K L hLK φ.1 = _
    rw [D.extensionNormalizedDegree_frobenius_eq_pow K L hLK φ, hφ]
    simp
  have hrel : (φ.1 ^ i.1 * h.1)⁻¹ * (φ.1 ^ j.1 * h'.1) ∈
      (D.frobeniusClosure K L hLK σ).toSubgroup :=
    QuotientGroup.leftRel_apply.mp (Quotient.exact' hij)
  let γ : D.frobeniusClosure K L hLK σ :=
    ⟨(φ.1 ^ i.1 * h.1)⁻¹ * (φ.1 ^ j.1 * h'.1), hrel⟩
  have hdegreeRange :
      (D.frobeniusClosureDegree K L hLK σ γ).toAdd ∈
        (zHatMulNat n).toAddMonoidHom.range := by
    have hmem : D.frobeniusClosureDegree K L hLK σ γ ∈
        (D.frobeniusClosureDegree K L hLK σ).toMonoidHom.range :=
      ⟨γ, rfl⟩
    rw [D.frobeniusClosureDegree_range K L hLK σ] at hmem
    exact hmem
  have hred : zHatReduction n hn
      (D.frobeniusClosureDegree K L hLK σ γ).toAdd = 0 := by
    have hker :
        (D.frobeniusClosureDegree K L hLK σ γ).toAdd ∈
          (zHatReduction n hn).ker := by
      rw [← zHatMulNat_range_eq_ker_reduction n hn]
      exact hdegreeRange
    exact hker
  have hredOne : zHatReduction n hn (1 : ZHat) = 1 := rfl
  have hmod : (j.1 : ZMod n) - (i.1 : ZMod n) = 0 := by
    have hdh : dQ h.1 = 1 := h.2
    have hdh' : dQ h'.1 = 1 := h'.2
    have hdegMul :
        dQ ((φ.1 ^ i.1 * h.1)⁻¹ * (φ.1 ^ j.1 * h'.1)) =
          (Multiplicative.ofAdd (1 : ZHat) ^ i.1)⁻¹ *
            Multiplicative.ofAdd (1 : ZHat) ^ j.1 := by
      rw [map_mul, map_inv, map_mul, map_mul, map_pow, map_pow,
        hdφ, hdh, hdh', mul_one, mul_one]
    have hdegAdd := congrArg Multiplicative.toAdd hdegMul
    change (D.frobeniusClosureDegree K L hLK σ γ).toAdd =
      -(i.1 • (1 : ZHat)) + j.1 • (1 : ZHat) at hdegAdd
    rw [hdegAdd] at hred
    rw [map_add, map_neg, map_nsmul, map_nsmul, hredOne] at hred
    simpa [sub_eq_add_neg, add_comm] using hred
  have hijCast : (i.1 : ZMod n) = (j.1 : ZMod n) := by
    exact (sub_eq_zero.mp hmod).symm
  have hijVal : i.1 = j.1 := by
    have hv := congrArg ZMod.val hijCast
    simpa [ZMod.val_natCast_of_lt i.2, ZMod.val_natCast_of_lt j.2] using hv
  have hijFin : i = j := Fin.ext hijVal
  subst j
  have hkernel : h.1⁻¹ * h'.1 ∈ dQ.toMonoidHom.ker := by
    have hdh : dQ h.1 = 1 := h.2
    have hdh' : dQ h'.1 = 1 := h'.2
    change dQ (h.1⁻¹ * h'.1) = 1
    rw [map_mul, map_inv, hdh, hdh', inv_one, one_mul]
  have hgamma : h.1⁻¹ * h'.1 ∈
      (D.frobeniusClosure K L hLK σ).toSubgroup := by
    simpa [mul_assoc] using hrel
  have hone : h.1⁻¹ * h'.1 = 1 := by
    have hm : h.1⁻¹ * h'.1 ∈ (⊥ : Subgroup
        (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)) := by
      rw [← D.frobeniusClosure_inf_degreeKernel K L hLK σ]
      exact ⟨hgamma, hkernel⟩
    exact hm
  have hh : h = h' := by
    apply Subtype.ext
    exact inv_mul_eq_one.mp hone
  subst h'
  rfl

theorem kernelPowerCosetMap_bijective (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (φ σ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1) :
    Function.Bijective (D.kernelPowerCosetMap K L hLK φ σ) := by
  let Q := K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK
  let dQ := D.extensionNormalizedDegreeContinuous K L hLK
  let H : Subgroup Q := dQ.toMonoidHom.ker
  let Γ : Subgroup Q := (D.frobeniusClosure K L hLK σ).toSubgroup
  let n := D.frobeniusExponent K L hLK σ
  let j := D.extensionDegreeKernelRestriction K L hLK
  let : Finite H :=
    Finite.of_injective j
      (D.extensionDegreeKernelRestriction_injective K L hLK)
  let : Finite (Q ⧸ Γ) := by
    simpa [Q, Γ] using D.frobeniusFixedField_finiteIndex K L hLK σ
  have hΓmap : Γ.map dQ.toMonoidHom =
      (D.frobeniusClosureDegree K L hLK σ).toMonoidHom.range := by
    ext z
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, hq⟩, rfl⟩
    · rintro ⟨q, rfl⟩
      exact ⟨q.1, q.2, rfl⟩
  have htopmap : (⊤ : Subgroup Q).map dQ.toMonoidHom = ⊤ := by
    apply top_unique
    intro z _
    obtain ⟨q, hq⟩ :=
      D.extensionNormalizedDegreeContinuous_surjective K L hLK z
    exact ⟨q, trivial, hq⟩
  have himage : (Γ.map dQ.toMonoidHom).relIndex
      ((⊤ : Subgroup Q).map dQ.toMonoidHom) = n := by
    rw [hΓmap, htopmap, Subgroup.relIndex_top_right,
      D.frobeniusClosureDegree_range K L hLK σ,
      AddSubgroup.index_toSubgroup,
      zHatMulNat_range_index _
        (D.frobeniusExponent_pos K L hLK σ)]
  have hkernel : (Γ ⊓ dQ.toMonoidHom.ker).relIndex
      ((⊤ : Subgroup Q) ⊓ dQ.toMonoidHom.ker) = Nat.card H := by
    rw [show Γ ⊓ dQ.toMonoidHom.ker = ⊥ by
      simpa [Γ, dQ, Q] using
        D.frobeniusClosure_inf_degreeKernel K L hLK σ]
    rw [top_inf_eq]
    change (⊥ : Subgroup Q).relIndex H = Nat.card H
    rw [Subgroup.relIndex_bot_left]
  have hindex : Γ.index = n * Nat.card H := by
    rw [← Subgroup.relIndex_top_right]
    rw [relIndex_eq_map_relIndex_mul_inf_ker_relIndex dQ.toMonoidHom le_top,
      himage, hkernel]
  have hcard :
      Nat.card (H × Fin n) = Nat.card (Q ⧸ Γ) := by
    calc
      Nat.card (H × Fin n) =
          Nat.card H * Nat.card (Fin n) := Nat.card_prod _ _
      _ = Nat.card H * n := by
        have hfin : Nat.card (Fin n) = n := by
          calc
            Nat.card (Fin n) = Fintype.card (Fin n) :=
              Nat.card_eq_fintype_card
            _ = n := Fintype.card_fin n
        rw [hfin]
      _ = n * Nat.card H := Nat.mul_comm _ _
      _ = Γ.index := hindex.symm
      _ = Nat.card (Q ⧸ Γ) := Subgroup.index_eq_card Γ
  apply (Nat.bijective_iff_injective_and_card
    (D.kernelPowerCosetMap K L hLK φ σ)).2
  exact ⟨D.kernelPowerCosetMap_injective K L hLK φ σ hφ,
    by simpa [H, n, Q, Γ, dQ] using hcard⟩

/-- The coset decomposition used in the proof of the Frobenius norm-identity lemma. -/
noncomputable def kernelPowerCosetEquiv (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (φ σ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1) :
    (D.extensionNormalizedDegreeContinuous K L hLK).toMonoidHom.ker ×
        Fin (D.frobeniusExponent K L hLK σ) ≃
      ((K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) ⧸
        (D.frobeniusClosure K L hLK σ).toSubgroup) :=
  Equiv.ofBijective (D.kernelPowerCosetMap K L hLK φ σ)
    (D.kernelPowerCosetMap_bijective K L hLK φ σ hφ)

/-- Explicit version of the coset decomposition, with representatives in
the order `φ^i · τ`; this is the order occurring in `φ_n ∘ N`. -/
noncomputable def frobeniusNormIdentityCosetMap (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ σ : D.FrobeniusElements K L hLK) :
    ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) ×
        Fin (D.frobeniusExponent K L hLK σ) →
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ)
          (D.frobeniusFixedField_le K L hLK σ)) :=
  fun p =>
    let kφ : K.field.toSubgroup := Quotient.out (φ.1 ^ p.2.1)
    let kI : (D.maximalUnramifiedField K.field).toSubgroup := Quotient.out p.1
    QuotientGroup.mk (kφ * (⟨kI.1, kI.2.1⟩ : K.field.toSubgroup))

theorem frobeniusNormIdentityCosetMap_commutes (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ σ : D.FrobeniusElements K L hLK)
    (p : ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) ×
      Fin (D.frobeniusExponent K L hLK σ)) :
    D.frobeniusFixedCosetToClosureCoset K L hLK σ
        (D.frobeniusNormIdentityCosetMap K L hLK φ σ p) =
      D.kernelPowerCosetMap K L hLK φ σ
        (D.inertiaQuotientDegreeKernelEquiv K L hLK p.1, p.2) := by
  let kφ : K.field.toSubgroup := Quotient.out (φ.1 ^ p.2.1)
  let kI : (D.maximalUnramifiedField K.field).toSubgroup := Quotient.out p.1
  let kIK : K.field.toSubgroup := ⟨kI.1, kI.2.1⟩
  have hkφ : (QuotientGroup.mk'
      (D.extensionInertiaWithin K.field L hLK)) kφ = φ.1 ^ p.2.1 :=
    Quotient.out_eq' (φ.1 ^ p.2.1)
  have hkI :
      (D.inertiaQuotientDegreeKernelEquiv K L hLK p.1).1 =
        (QuotientGroup.mk' (D.extensionInertiaWithin K.field L hLK)) kIK := by
    change (D.inertiaCosetToDegreeKernel K L hLK p.1).1 = _
    calc
      (D.inertiaCosetToDegreeKernel K L hLK p.1).1 =
          (D.inertiaCosetToDegreeKernel K L hLK
            (QuotientGroup.mk kI)).1 := by
        exact congrArg
          (fun r => (D.inertiaCosetToDegreeKernel K L hLK r).1)
          (Quotient.out_eq' p.1).symm
      _ = _ := rfl
  change QuotientGroup.mk
      ((QuotientGroup.mk' (D.extensionInertiaWithin K.field L hLK))
        (kφ * kIK)) =
    QuotientGroup.mk
      (φ.1 ^ p.2.1 *
        (D.inertiaQuotientDegreeKernelEquiv K L hLK p.1).1)
  rw [map_mul, hkφ, hkI]

theorem frobeniusNormIdentityCosetMap_bijective (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (φ σ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1) :
    Function.Bijective (D.frobeniusNormIdentityCosetMap K L hLK φ σ) := by
  let eI := D.inertiaQuotientDegreeKernelEquiv K L hLK
  let eP := D.kernelPowerCosetEquiv K L hLK φ σ hφ
  let eSigma := D.frobeniusFixedCosetClosureEquiv K L hLK σ
  have hinj : Function.Injective (D.frobeniusNormIdentityCosetMap K L hLK φ σ) := by
    intro p q hpq
    apply (Equiv.prodCongr eI (Equiv.refl _)).injective
    apply eP.injective
    calc
      eP (eI p.1, p.2) =
          eSigma (D.frobeniusNormIdentityCosetMap K L hLK φ σ p) :=
        (D.frobeniusNormIdentityCosetMap_commutes K L hLK φ σ p).symm
      _ = eSigma (D.frobeniusNormIdentityCosetMap K L hLK φ σ q) :=
        congrArg eSigma hpq
      _ = eP (eI q.1, q.2) :=
        D.frobeniusNormIdentityCosetMap_commutes K L hLK φ σ q
  have hsurj : Function.Surjective (D.frobeniusNormIdentityCosetMap K L hLK φ σ) := by
    intro q
    obtain ⟨p, hp⟩ := eP.surjective (eSigma q)
    obtain ⟨r, hr⟩ := (Equiv.prodCongr eI (Equiv.refl _)).surjective p
    refine ⟨r, ?_⟩
    apply eSigma.injective
    calc
      eSigma (D.frobeniusNormIdentityCosetMap K L hLK φ σ r) =
          eP (eI r.1, r.2) :=
        D.frobeniusNormIdentityCosetMap_commutes K L hLK φ σ r
      _ = eP p := by
        apply congrArg eP
        exact hr
      _ = eSigma q := hp
  exact ⟨hinj, hsurj⟩

/-- Defines `frobeniusNormIdentityCosetEquiv`. -/
noncomputable def frobeniusNormIdentityCosetEquiv (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (φ σ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1) :
    ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) ×
        Fin (D.frobeniusExponent K L hLK σ) ≃
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ)
          (D.frobeniusFixedField_le K L hLK σ)) :=
  Equiv.ofBijective (D.frobeniusNormIdentityCosetMap K L hLK φ σ)
    (D.frobeniusNormIdentityCosetMap_bijective K L hLK φ σ hφ)

end DegreeData

end frobeniusCosetEquivalences

section frobeniusNormIdentities

/-!
Mathlib's `Rep ℤ G` requires the coefficient ring and acting group to share
a universe; `IntegralRepGroupType` names that shared boundary.
-/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

theorem relativeCosetAction_frobeniusNormIdentityCosetEquiv
    (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (φ σ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (a : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ))
    (r : (D.maximalUnramifiedField K.field).toSubgroup ⧸
      extensionSubgroup (D.maximalUnramifiedField K.field)
        (D.maximalUnramifiedField L)
        (D.maximalUnramifiedField_mono hLK))
    (i : Fin (D.frobeniusExponent K L hLK σ)) :
    relativeCosetAction A K.field (D.frobeniusFixedField K L hLK σ)
        (D.frobeniusFixedField_le K L hLK σ) a
        (D.frobeniusNormIdentityCosetEquiv K L hLK φ σ hφ (r, i)) =
      A.ρ (Quotient.out (φ.1 ^ i.1)).1
        (relativeCosetAction A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)
          (fixedFieldInclusion A
            (D.frobeniusFixedField K L hLK σ)
            (D.maximalUnramifiedField L)
            (D.fieldInertia_le_frobeniusFixedField K L hLK σ) a) r) := by
  let kφ : K.field.toSubgroup := Quotient.out (φ.1 ^ i.1)
  let kI : (D.maximalUnramifiedField K.field).toSubgroup := Quotient.out r
  let kIK : K.field.toSubgroup := ⟨kI.1, kI.2.1⟩
  change relativeCosetAction A K.field
      (D.frobeniusFixedField K L hLK σ)
      (D.frobeniusFixedField_le K L hLK σ) a
      (QuotientGroup.mk (kφ * kIK)) = _
  rw [relativeCosetAction_mk]
  have hr : r = QuotientGroup.mk kI := (Quotient.out_eq' r).symm
  rw [hr, relativeCosetAction_mk]
  change A.ρ (kφ.1 * kI.1) a.1 = A.ρ kφ.1 (A.ρ kI.1 a.1)
  rw [map_mul]
  rfl

theorem frobeniusQuotientAction_relativeNorm (D : DegreeData G)
    (A : Rep ℤ G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hInertiaFintype : Fintype
      ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK))]
    (φ : D.FrobeniusElements K L hLK)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L))
    (i : ℕ) :
    ((D.frobeniusQuotientAction A K.field L hLK (φ.1 ^ i)
      (fixedFieldInclusion A (D.maximalUnramifiedField K.field)
        (D.maximalUnramifiedField L)
        (D.maximalUnramifiedField_mono hLK)
        (relativeNorm A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK) a)) :
        ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) : A.V) =
      (@Finset.univ
        ((D.maximalUnramifiedField K.field).toSubgroup ⧸
          extensionSubgroup (D.maximalUnramifiedField K.field)
            (D.maximalUnramifiedField L)
            (D.maximalUnramifiedField_mono hLK))
        (Fintype.ofFinite _)).sum (fun r =>
          A.ρ (Quotient.out (φ.1 ^ i)).1
            (relativeCosetAction A (D.maximalUnramifiedField K.field)
              (D.maximalUnramifiedField L)
              (D.maximalUnramifiedField_mono hLK) a r)) := by
  let kφ : K.field.toSubgroup := Quotient.out (φ.1 ^ i)
  have hkφ : φ.1 ^ i = QuotientGroup.mk kφ :=
    (Quotient.out_eq' (φ.1 ^ i)).symm
  let b := fixedFieldInclusion A (D.maximalUnramifiedField K.field)
    (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
    (relativeNorm A (D.maximalUnramifiedField K.field)
      (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) a)
  calc
    ((D.frobeniusQuotientAction A K.field L hLK (φ.1 ^ i) b :
        ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) : A.V) =
      (D.frobeniusQuotientAction A K.field L hLK
        (QuotientGroup.mk kφ) b : A.V) := by
          exact congrArg
            (fun q => (D.frobeniusQuotientAction A K.field L hLK q b : A.V)) hkφ
    _ = A.ρ kφ.1 b.1 := rfl
    _ = A.ρ kφ.1
        ((relativeNorm A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK) a :
            ambientFixedAddSubgroup A (D.maximalUnramifiedField K.field)) : A.V) := by
          rw [fixedFieldInclusion_coe]
    _ = A.ρ kφ.1
        (relativeNormValue A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK) a) := by
          rw [relativeNorm_apply_coe]
    _ = A.ρ kφ.1
        ((@Finset.univ
          ((D.maximalUnramifiedField K.field).toSubgroup ⧸
            extensionSubgroup (D.maximalUnramifiedField K.field)
              (D.maximalUnramifiedField L)
              (D.maximalUnramifiedField_mono hLK))
          (Fintype.ofFinite _)).sum (fun r =>
            relativeCosetAction A (D.maximalUnramifiedField K.field)
              (D.maximalUnramifiedField L)
              (D.maximalUnramifiedField_mono hLK) a r)) := by
          rfl
    _ = (@Finset.univ
        ((D.maximalUnramifiedField K.field).toSubgroup ⧸
          extensionSubgroup (D.maximalUnramifiedField K.field)
            (D.maximalUnramifiedField L)
            (D.maximalUnramifiedField_mono hLK))
        (Fintype.ofFinite _)).sum (fun r => A.ρ kφ.1
          (relativeCosetAction A (D.maximalUnramifiedField K.field)
            (D.maximalUnramifiedField L)
            (D.maximalUnramifiedField_mono hLK) a r)) := by
          rw [map_sum]

/-- The first norm identity of the Frobenius norm-identity lemma, in the order `φ_n ∘ N`. -/
theorem frobeniusNormIdentity_norm_eq_powerSum_norm (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (φ σ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (a : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ)) :
    letI : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ)
            (D.frobeniusFixedField_le K L hLK σ)) :=
      D.frobeniusFixedField_finite K L hLK σ
    letI : Finite
        ((D.maximalUnramifiedField K.field).toSubgroup ⧸
          extensionSubgroup (D.maximalUnramifiedField K.field)
            (D.maximalUnramifiedField L)
            (D.maximalUnramifiedField_mono hLK)) :=
      D.maximalUnramifiedExtension_finite K.field L hLK
    ((relativeNorm A K.field (D.frobeniusFixedField K L hLK σ)
      (D.frobeniusFixedField_le K L hLK σ) a :
        ambientFixedAddSubgroup A K.field) : A.V) =
      ((D.frobeniusPowerSum A K.field L hLK φ.1
        (D.frobeniusExponent K L hLK σ)
        (fixedFieldInclusion A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)
          (relativeNorm A (D.maximalUnramifiedField K.field)
            (D.maximalUnramifiedField L)
            (D.maximalUnramifiedField_mono hLK)
            (fixedFieldInclusion A
              (D.frobeniusFixedField K L hLK σ)
              (D.maximalUnramifiedField L)
              (D.fieldInertia_le_frobeniusFixedField K L hLK σ) a))) :
          ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) : A.V) := by
  let : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ)
          (D.frobeniusFixedField_le K L hLK σ)) :=
    D.frobeniusFixedField_finite K L hLK σ
  let : Finite
      ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) :=
    D.maximalUnramifiedExtension_finite K.field L hLK
  let R := (D.maximalUnramifiedField K.field).toSubgroup ⧸
    extensionSubgroup (D.maximalUnramifiedField K.field)
      (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
  let n := D.frobeniusExponent K L hLK σ
  let e := D.frobeniusNormIdentityCosetEquiv K L hLK φ σ hφ
  let aI := fixedFieldInclusion A
    (D.frobeniusFixedField K L hLK σ)
    (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField K L hLK σ) a
  let b := fixedFieldInclusion A (D.maximalUnramifiedField K.field)
    (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
    (relativeNorm A (D.maximalUnramifiedField K.field)
      (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) aI)
  let := Fintype.ofFinite R
  let := Fintype.ofFinite
    (K.field.toSubgroup ⧸
      extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ)
        (D.frobeniusFixedField_le K L hLK σ))
  rw [relativeNorm_apply_coe, relativeNormValue,
    D.frobeniusPowerSum_coe]
  calc
    ∑ q, relativeCosetAction A K.field
        (D.frobeniusFixedField K L hLK σ)
        (D.frobeniusFixedField_le K L hLK σ) a q =
      ∑ p : R × Fin n,
        relativeCosetAction A K.field
          (D.frobeniusFixedField K L hLK σ)
          (D.frobeniusFixedField_le K L hLK σ) a (e p) :=
      (e.sum_comp _).symm
    _ = ∑ p : R × Fin n,
        A.ρ (Quotient.out (φ.1 ^ p.2.1)).1
          (relativeCosetAction A (D.maximalUnramifiedField K.field)
            (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
            aI p.1) := by
      apply Finset.sum_congr rfl
      intro p _
      exact D.relativeCosetAction_frobeniusNormIdentityCosetEquiv
        A K L hLK φ σ hφ a p.1 p.2
    _ = ∑ i : Fin n, ∑ r : R,
        A.ρ (Quotient.out (φ.1 ^ i.1)).1
          (relativeCosetAction A (D.maximalUnramifiedField K.field)
            (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
            aI r) := by
      rw [Fintype.sum_prod_type]
      exact Finset.sum_comm
    _ = ∑ i : Fin n,
        (D.frobeniusQuotientAction A K.field L hLK (φ.1 ^ i.1) b : A.V) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (D.frobeniusQuotientAction_relativeNorm
        A K L hLK φ aI i.1).symm

/-- The second identity of the Frobenius norm-identity lemma:
`N_{\widetilde L/\widetilde K} ∘ φ_n =
  φ_n ∘ N_{\widetilde L/\widetilde K}`. -/
theorem frobeniusNormIdentity_norm_powerSum_eq_powerSum_norm (D : DegreeData G)
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    [hLfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (φ : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK)
    (n : ℕ)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    letI : Finite
        ((D.maximalUnramifiedField K).toSubgroup ⧸
          extensionSubgroup (D.maximalUnramifiedField K)
            (D.maximalUnramifiedField L)
            (D.maximalUnramifiedField_mono hLK)) :=
      D.maximalUnramifiedExtension_finite K L hLK
    ((relativeNorm A (D.maximalUnramifiedField K)
      (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
      (D.frobeniusPowerSum A K L hLK φ n a) :
        ambientFixedAddSubgroup A (D.maximalUnramifiedField K)) : A.V) =
      ((D.frobeniusPowerSum A K L hLK φ n
        (fixedFieldInclusion A (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
          (relativeNorm A (D.maximalUnramifiedField K)
            (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
            a)) : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
        A.V) := by
  let : Finite
      ((D.maximalUnramifiedField K).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) :=
    D.maximalUnramifiedExtension_finite K L hLK
  change
    ((relativeNorm A (D.maximalUnramifiedField K)
      (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK))
      (∑ i : Fin n, D.frobeniusQuotientAction A K L hLK (φ ^ i.1) a)).1 =
      (∑ i : Fin n, D.frobeniusQuotientAction A K L hLK (φ ^ i.1)
        (fixedFieldInclusion A (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
          (relativeNorm A (D.maximalUnramifiedField K)
            (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
            a))).1
  simp only [map_sum]
  change (ambientFixedAddSubgroup A
      (D.maximalUnramifiedField K)).subtype
      (∑ i : Fin n, relativeNorm A (D.maximalUnramifiedField K)
        (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
        (D.frobeniusQuotientAction A K L hLK (φ ^ i.1) a)) =
    (ambientFixedAddSubgroup A
      (D.maximalUnramifiedField L)).subtype
      (∑ i : Fin n, D.frobeniusQuotientAction A K L hLK (φ ^ i.1)
        (fixedFieldInclusion A (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
          (relativeNorm A (D.maximalUnramifiedField K)
            (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
            a)))
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact D.relativeNorm_frobeniusQuotientAction A K L hLK (φ ^ i.1) a

/-- **The Frobenius norm-identity lemma.**  For `d_K(φ)=1`, `d_K(σ)=n` and the
fixed field `Σ` of `σ`, the three actual norm expressions agree:
`N_{Σ/K}(a) = (N_{\widetilde L/\widetilde K} ∘ φ_n)(a) =
(φ_n ∘ N_{\widetilde L/\widetilde K})(a)`. -/
theorem frobeniusNormIdentities (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (φ σ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (a : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ)) :
    letI : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ)
            (D.frobeniusFixedField_le K L hLK σ)) :=
      D.frobeniusFixedField_finite K L hLK σ
    letI : Finite
        ((D.maximalUnramifiedField K.field).toSubgroup ⧸
          extensionSubgroup (D.maximalUnramifiedField K.field)
            (D.maximalUnramifiedField L)
            (D.maximalUnramifiedField_mono hLK)) :=
      D.maximalUnramifiedExtension_finite K.field L hLK
    let n := D.frobeniusExponent K L hLK σ
    let aI := fixedFieldInclusion A
      (D.frobeniusFixedField K L hLK σ)
      (D.maximalUnramifiedField L)
      (D.fieldInertia_le_frobeniusFixedField K L hLK σ) a
    let b := fixedFieldInclusion A (D.maximalUnramifiedField K.field)
      (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
      (relativeNorm A (D.maximalUnramifiedField K.field)
        (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) aI)
    let φnAI := D.frobeniusPowerSum A K.field L hLK φ.1 n aI
    (((relativeNorm A K.field (D.frobeniusFixedField K L hLK σ)
      (D.frobeniusFixedField_le K L hLK σ) a :
        ambientFixedAddSubgroup A K.field) : A.V) =
      ((relativeNorm A (D.maximalUnramifiedField K.field)
        (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
        φnAI : ambientFixedAddSubgroup A
          (D.maximalUnramifiedField K.field)) : A.V)) ∧
    (((relativeNorm A (D.maximalUnramifiedField K.field)
      (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
      φnAI : ambientFixedAddSubgroup A
        (D.maximalUnramifiedField K.field)) : A.V) =
      ((D.frobeniusPowerSum A K.field L hLK φ.1 n b :
        ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) : A.V)) := by
  let : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ)
          (D.frobeniusFixedField_le K L hLK σ)) :=
    D.frobeniusFixedField_finite K L hLK σ
  let : Finite
      ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) :=
    D.maximalUnramifiedExtension_finite K.field L hLK
  let n := D.frobeniusExponent K L hLK σ
  let aI := fixedFieldInclusion A
    (D.frobeniusFixedField K L hLK σ)
    (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField K L hLK σ) a
  let b := fixedFieldInclusion A (D.maximalUnramifiedField K.field)
    (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
    (relativeNorm A (D.maximalUnramifiedField K.field)
      (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) aI)
  let φnAI := D.frobeniusPowerSum A K.field L hLK φ.1 n aI
  have hFirst :
      ((relativeNorm A K.field (D.frobeniusFixedField K L hLK σ)
        (D.frobeniusFixedField_le K L hLK σ) a :
          ambientFixedAddSubgroup A K.field) : A.V) =
        ((D.frobeniusPowerSum A K.field L hLK φ.1 n b :
          ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) : A.V) := by
    simpa [n, aI, b] using
      D.frobeniusNormIdentity_norm_eq_powerSum_norm A K L hLK φ σ hφ a
  have hCommute :
      ((relativeNorm A (D.maximalUnramifiedField K.field)
        (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
        φnAI : ambientFixedAddSubgroup A
          (D.maximalUnramifiedField K.field)) : A.V) =
        ((D.frobeniusPowerSum A K.field L hLK φ.1 n b :
          ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) : A.V) := by
    simpa [n, aI, b, φnAI] using
      D.frobeniusNormIdentity_norm_powerSum_eq_powerSum_norm
        A K.field L hLK φ.1 n aI
  exact ⟨hFirst.trans hCommute.symm, hCommute⟩

end DegreeData
end frobeniusNormIdentities
end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_FrobeniusClosureCommutation
attribute [-instance] _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.finiteNormQuotientAddCommGroup _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.chosenUnramifiedFrobeniusLift_exponent _root_.ClassFormation.DegreeData.maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClass _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_eq_one_iff _root_.ClassFormation.FiniteGaloisSubextension.toGaloisSubextension_isTotallyRamified_iff _root_.ClassFormation.FiniteGaloisSubextension.toGaloisSubextension_isUnramified_iff _root_.ClassFormation.ValuationData.canonicalUnramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.canonicalValueQuotientHom_mk _root_.ClassFormation.ValuationData.canonicalValueReduction_one _root_.ClassFormation.ValuationData.unramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.finiteNormClass_add _root_.ClassFormation.finiteNormClass_eq_zero_iff _root_.ClassFormation.finiteNormClass_nsmul _root_.ClassFormation.finiteNormClass_sub _root_.ClassFormation.finiteNormClass_zero _root_.ClassFormation.finiteNormQuotientConcreteEquiv_finiteNormClass _root_.ClassFormation.finiteNormQuotientLift_finiteNormClass _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

universe u

namespace ClassFormation

open KummerTheory
open CyclicCohomology

/-!
# Frobenius-closure commutation

This module promotes commutation with a Frobenius generator to its closed
procyclic subgroup and derives the conjugation identities for the associated
fixed field.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators

section frobeniusClosureCommutation

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Commuting with the chosen generator means commuting with its closed
procyclic closure. -/
theorem frobeniusClosure_commutes_of_commutes_generator (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : q * σ.1 = σ.1 * q)
    (c : D.frobeniusClosure K L hLK σ) :
    q * c.1 = c.1 * q := by
  let : IsClosed
      (D.extensionInertiaWithin K.field L hLK : Set K.field.toSubgroup) :=
    D.extensionInertiaWithin_isClosed K L hLK
  let : T2Space
      (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) := by
    infer_instance
  let Q := K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK
  let X : Set Q := Set.range (fun _ : Unit => σ.1)
  have hclosure : Subgroup.closure X ≤
      Subgroup.centralizer ({q} : Set Q) := by
    rw [Subgroup.closure_le]
    rintro x ⟨i, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr hq.symm
  have htop : (Subgroup.closure X).topologicalClosure ≤
      Subgroup.centralizer ({q} : Set Q) :=
    Subgroup.topologicalClosure_minimal _ hclosure
      (Set.isClosed_centralizer (M := Q) ({q} : Set Q))
  have hc : c.1 ∈ (Subgroup.closure X).topologicalClosure := c.2
  exact (Subgroup.mem_centralizer_singleton_iff.mp (htop hc)).symm

/-- If a quotient element commutes with the Frobenius lift, its chosen
representative stabilizes the corresponding fixed field. -/
theorem conjugate_frobeniusFixedField_eq_of_commutes (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : q * σ.1 = σ.1 * q) :
    let k : K.field.toSubgroup := Quotient.out q
    conjugateClosedSubgroup (D.frobeniusFixedField K L hLK σ) k.1⁻¹ =
      D.frobeniusFixedField K L hLK σ := by
  dsimp only
  let T := D.frobeniusFixedField K L hLK σ
  let k : K.field.toSubgroup := Quotient.out q
  have hkq :
      (QuotientGroup.mk k :
        K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) = q :=
    Quotient.out_eq' q
  ext x
  change x ∈ conjugateClosedSubgroup
      (D.frobeniusFixedField K L hLK σ) k.1⁻¹ ↔
    x ∈ D.frobeniusFixedField K L hLK σ
  rw [conjugateClosedSubgroup_mem]
  constructor
  · intro hx
    obtain ⟨t, htClosure, htx⟩ := hx
    let xK : K.field.toSubgroup := ⟨x, by
      have htK : t.1 ∈ K.field.toSubgroup := t.2
      have htxval : t.1 = k.1⁻¹ * x * k.1 := by simpa using htx
      have : x = k.1 * t.1 * k.1⁻¹ := by
        calc
          x = k.1 * (k.1⁻¹ * x * k.1) * k.1⁻¹ := by simp [mul_assoc]
          _ = k.1 * t.1 * k.1⁻¹ := by rw [htxval]
      rw [this]
      exact K.field.toSubgroup.mul_mem
        (K.field.toSubgroup.mul_mem k.2 htK) (K.field.toSubgroup.inv_mem k.2)⟩
    have hcomm := D.frobeniusClosure_commutes_of_commutes_generator
      K L hLK σ q hq ⟨QuotientGroup.mk t, htClosure⟩
    have hcomm' : q * QuotientGroup.mk t = QuotientGroup.mk t * q := hcomm
    have hxClosure : QuotientGroup.mk xK ∈
        (D.frobeniusClosure K L hLK σ).toSubgroup := by
      have hqconj : q * QuotientGroup.mk t * q⁻¹ = QuotientGroup.mk t := by
        calc
          q * QuotientGroup.mk t * q⁻¹ =
              (QuotientGroup.mk t * q) * q⁻¹ := by rw [hcomm']
          _ = QuotientGroup.mk t := by simp
      change QuotientGroup.mk xK ∈
        (D.frobeniusClosure K L hLK σ).toSubgroup
      have hxval : xK = k * t * k⁻¹ := by
        apply Subtype.ext
        dsimp [xK]
        have htxval : t.1 = k.1⁻¹ * x * k.1 := by simpa using htx
        calc
          x = k.1 * (k.1⁻¹ * x * k.1) * k.1⁻¹ := by simp [mul_assoc]
          _ = k.1 * t.1 * k.1⁻¹ := by rw [htxval]
      rw [hxval]
      change (QuotientGroup.mk k :
          K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) *
          QuotientGroup.mk t * (QuotientGroup.mk k)⁻¹ ∈
        (D.frobeniusClosure K L hLK σ).toSubgroup
      rw [hkq, hqconj]
      exact htClosure
    exact ⟨xK, hxClosure, rfl⟩
  · intro hx
    obtain ⟨t, htClosure, htx⟩ := hx
    let yK : K.field.toSubgroup := ⟨k.1⁻¹ * x * k.1, by
      have htK : t.1 ∈ K.field.toSubgroup := t.2
      rw [← htx]
      exact K.field.toSubgroup.mul_mem
        (K.field.toSubgroup.mul_mem (K.field.toSubgroup.inv_mem k.2) htK) k.2⟩
    have hcomm := D.frobeniusClosure_commutes_of_commutes_generator
      K L hLK σ q hq ⟨QuotientGroup.mk t, htClosure⟩
    have hcomm' : q * QuotientGroup.mk t = QuotientGroup.mk t * q := hcomm
    have hyClosure : QuotientGroup.mk yK ∈
        (D.frobeniusClosure K L hLK σ).toSubgroup := by
      have hqconj : q⁻¹ * QuotientGroup.mk t * q = QuotientGroup.mk t := by
        calc
          q⁻¹ * QuotientGroup.mk t * q =
              q⁻¹ * (QuotientGroup.mk t * q) := by simp [mul_assoc]
          _ = q⁻¹ * (q * QuotientGroup.mk t) := by rw [hcomm']
          _ = QuotientGroup.mk t := by simp
      have hyval : yK = k⁻¹ * t * k := by
        apply Subtype.ext
        dsimp [yK]
        have htxval : t.1 = x := by simpa using htx
        rw [htxval]
      rw [hyval]
      change (QuotientGroup.mk k :
          K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)⁻¹ *
          QuotientGroup.mk t * QuotientGroup.mk k ∈
        (D.frobeniusClosure K L hLK σ).toSubgroup
      rw [hkq, hqconj]
      exact htClosure
    refine ⟨yK, hyClosure, ?_⟩
    simp [yK]

end DegreeData

end frobeniusClosureCommutation

end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_UniversalNormDescent
attribute [-instance] _root_.ClassFormation.finiteNormQuotientAddCommGroup _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClass _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.ValuationData.canonicalUnramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.canonicalValueQuotientHom_mk _root_.ClassFormation.ValuationData.canonicalValueReduction_one _root_.ClassFormation.ValuationData.unramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.finiteNormClass_add _root_.ClassFormation.finiteNormClass_eq_zero_iff _root_.ClassFormation.finiteNormClass_nsmul _root_.ClassFormation.finiteNormClass_sub _root_.ClassFormation.finiteNormClass_zero _root_.ClassFormation.finiteNormQuotientConcreteEquiv_finiteNormClass _root_.ClassFormation.finiteNormQuotientLift_finiteNormClass _root_.ClassFormation.mem_normFilterBasis_iff _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

universe u v

namespace ClassFormation

open KummerTheory
open CyclicCohomology

/-!
# Universal norm descent

This module contains the representation-theoretic lifting and correction
calculation used by the abstract reciprocity construction, together with
the norm, action, and iterate identities it requires.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators

/-- Transport the ordinary conjugation action back to a field stabilized
by that conjugation. -/
noncomputable def conjugateStableAction
    {R : IntegralRepGroupType} [Group R] [TopologicalSpace R] [ContinuousMul R]
    (B : Rep ℤ R) (F : ClosedSubgroup R) (s : R)
    (hF : conjugateClosedSubgroup F s = F)
    (a : ambientFixedAddSubgroup B F) : ambientFixedAddSubgroup B F :=
  hF ▸ conjugateFixedElement B F s a

theorem transport_fixed_coe
    {R : IntegralRepGroupType} [Group R] [TopologicalSpace R]
    (B : Rep ℤ R) (F' F : ClosedSubgroup R) (h : F' = F)
    (a : ambientFixedAddSubgroup B F') :
    (((h ▸ a : ambientFixedAddSubgroup B F) : B.V)) = a.1 := by
  cases h
  rfl

/-- The conjugation-stable action agrees with its ambient action after coercion. -/
@[simp]
theorem conjugateStableAction_coe
    {R : IntegralRepGroupType} [Group R] [TopologicalSpace R] [ContinuousMul R]
    (B : Rep ℤ R) (F : ClosedSubgroup R) (s : R)
    (hF : conjugateClosedSubgroup F s = F)
    (a : ambientFixedAddSubgroup B F) :
    ((conjugateStableAction B F s hF a : ambientFixedAddSubgroup B F) : B.V) =
      B.ρ s⁻¹ a.1 := by
  exact transport_fixed_coe B _ F hF _

/-- Powers in a representation are the iterates of the corresponding
action map. -/
theorem rep_action_pow_eq_iterate {R : IntegralRepGroupType} [Group R]
    (B : Rep ℤ R) (g : R) (n : ℕ) (x : B.V) :
    B.ρ (g ^ n) x = ((B.ρ g)^[n]) x := by
  let : Module ℤ B.V := B.hV2
  rw [map_pow, Module.End.coe_pow]

end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_FrobeniusFixedFieldAction
attribute [-instance] _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.finiteNormQuotientAddCommGroup _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.chosenUnramifiedFrobeniusLift_exponent _root_.ClassFormation.DegreeData.maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClass _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_eq_one_iff _root_.ClassFormation.FiniteGaloisSubextension.toGaloisSubextension_isTotallyRamified_iff _root_.ClassFormation.FiniteGaloisSubextension.toGaloisSubextension_isUnramified_iff _root_.ClassFormation.ValuationData.canonicalUnramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.canonicalValueQuotientHom_mk _root_.ClassFormation.ValuationData.canonicalValueReduction_one _root_.ClassFormation.ValuationData.unramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.finiteNormClass_add _root_.ClassFormation.finiteNormClass_eq_zero_iff _root_.ClassFormation.finiteNormClass_nsmul _root_.ClassFormation.finiteNormClass_sub _root_.ClassFormation.finiteNormClass_zero _root_.ClassFormation.finiteNormQuotientConcreteEquiv_finiteNormClass _root_.ClassFormation.finiteNormQuotientLift_finiteNormClass _root_.ClassFormation.mem_normFilterBasis_iff _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

universe u

namespace ClassFormation

open KummerTheory
open CyclicCohomology

/-!
# Actions on Frobenius fixed fields

This module defines the action induced on a Frobenius fixed field and proves
its compatibility with conjugate-stable actions, relative norms, inclusions,
and Frobenius power sums.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators

section fixedFieldActions

/-!
Mathlib's `Rep ℤ G` requires its coefficient ring and acting group in the
same universe; `IntegralRepGroupType` names that shared boundary.
-/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The action on a Frobenius fixed field induced by an element commuting
with its defining generator. -/
noncomputable def frobeniusFixedFieldAction (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : q * σ.1 = σ.1 * q) :
    ambientFixedAddSubgroup A (D.frobeniusFixedField K L hLK σ) →+
      ambientFixedAddSubgroup A (D.frobeniusFixedField K L hLK σ) := by
  let k : K.field.toSubgroup := Quotient.out q
  let hstable :
      conjugateClosedSubgroup (D.frobeniusFixedField K L hLK σ) k.1⁻¹ =
        D.frobeniusFixedField K L hLK σ :=
    D.conjugate_frobeniusFixedField_eq_of_commutes K L hLK σ q hq
  exact
    { toFun := fun a => ⟨A.ρ k.1 a.1, by
        intro t
        have htConj : t.1 ∈ conjugateClosedSubgroup
            (D.frobeniusFixedField K L hLK σ) k.1⁻¹ := by
          rw [hstable]
          exact t.2
        have hcMem : k.1⁻¹ * t.1 * k.1 ∈
            D.frobeniusFixedField K L hLK σ := by
          simpa using (conjugateClosedSubgroup_mem
            (D.frobeniusFixedField K L hLK σ) k.1⁻¹ t.1).mp htConj
        let c : (D.frobeniusFixedField K L hLK σ).toSubgroup :=
          ⟨k.1⁻¹ * t.1 * k.1, hcMem⟩
        calc
          A.ρ t.1 (A.ρ k.1 a.1) = A.ρ (t.1 * k.1) a.1 := by
            rw [map_mul]
            rfl
          _ = A.ρ (k.1 * c.1) a.1 := by simp [c, mul_assoc]
          _ = A.ρ k.1 (A.ρ c.1 a.1) := by rw [map_mul]; rfl
          _ = A.ρ k.1 a.1 := by rw [a.2 c]⟩
      map_zero' := by apply Subtype.ext; exact map_zero _
      map_add' := by
        intro a b
        apply Subtype.ext
        exact map_add _ _ _ }

/-- The fixed-field action has the expected ambient automorphism after coercion. -/
@[simp]
theorem frobeniusFixedFieldAction_coe (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : q * σ.1 = σ.1 * q)
    (a : ambientFixedAddSubgroup A (D.frobeniusFixedField K L hLK σ)) :
    ((D.frobeniusFixedFieldAction A K L hLK σ q hq a :
      ambientFixedAddSubgroup A (D.frobeniusFixedField K L hLK σ)) : A.V) =
      A.ρ (Quotient.out q).1 a.1 := by
  rfl

/-- Inclusion of a stabilized Frobenius fixed field intertwines its action
with the actual quotient action on the maximal unramified field. -/
theorem frobeniusFixedFieldAction_inclusion (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : q * σ.1 = σ.1 * q)
    (a : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ)) :
    fixedFieldInclusion A (D.frobeniusFixedField K L hLK σ)
        (D.maximalUnramifiedField L)
        (D.fieldInertia_le_frobeniusFixedField K L hLK σ)
        (D.frobeniusFixedFieldAction A K L hLK σ q hq a) =
      D.frobeniusQuotientAction A K.field L hLK q
        (fixedFieldInclusion A (D.frobeniusFixedField K L hLK σ)
          (D.maximalUnramifiedField L)
          (D.fieldInertia_le_frobeniusFixedField K L hLK σ) a) := by
  apply Subtype.ext
  refine (D.frobeniusFixedFieldAction_coe A K L hLK σ q hq a).trans ?_
  let k : K.field.toSubgroup := Quotient.out q
  have hkq : (QuotientGroup.mk k :
      K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) = q :=
    Quotient.out_eq' q
  calc
    A.ρ (Quotient.out q).1 a.1 = A.ρ k.1 a.1 := rfl
    _ = (D.frobeniusQuotientAction A K.field L hLK (QuotientGroup.mk k)
        (fixedFieldInclusion A (D.frobeniusFixedField K L hLK σ)
          (D.maximalUnramifiedField L)
          (D.fieldInertia_le_frobeniusFixedField K L hLK σ) a)).1 := rfl
    _ = _ := congrArg (fun z =>
      (D.frobeniusQuotientAction A K.field L hLK z
        (fixedFieldInclusion A (D.frobeniusFixedField K L hLK σ)
          (D.maximalUnramifiedField L)
          (D.fieldInertia_le_frobeniusFixedField K L hLK σ) a)).1) hkq

end DegreeData

end fixedFieldActions

end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_FrobeniusPowerFixedField
attribute [-instance] _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.finiteNormQuotientAddCommGroup _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.chosenUnramifiedFrobeniusLift_exponent _root_.ClassFormation.DegreeData.frobeniusFixedFieldAction_coe _root_.ClassFormation.DegreeData.maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClass _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_eq_one_iff _root_.ClassFormation.FiniteGaloisSubextension.toGaloisSubextension_isTotallyRamified_iff _root_.ClassFormation.FiniteGaloisSubextension.toGaloisSubextension_isUnramified_iff _root_.ClassFormation.ValuationData.canonicalUnramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.canonicalValueQuotientHom_mk _root_.ClassFormation.ValuationData.canonicalValueReduction_one _root_.ClassFormation.ValuationData.unramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.finiteNormClass_add _root_.ClassFormation.finiteNormClass_eq_zero_iff _root_.ClassFormation.finiteNormClass_nsmul _root_.ClassFormation.finiteNormClass_sub _root_.ClassFormation.finiteNormClass_zero _root_.ClassFormation.finiteNormQuotientConcreteEquiv_finiteNormClass _root_.ClassFormation.finiteNormQuotientLift_finiteNormClass _root_.ClassFormation.orbitQuotientClosedCyclicEquiv_mk _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

universe u

namespace ClassFormation

open KummerTheory
open CyclicCohomology

/-!
# Frobenius power fixed fields

This module constructs the fixed fields of powers of a Frobenius element and
proves their inclusion, exponent, normality, unramifiedness, finiteness,
degree, quotient-cardinality, and generator properties.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators

section degreeOnePowerFields

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

theorem extensionNormalizedDegree_pow_of_degreeOne (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (n : ℕ) :
    D.extensionNormalizedDegree K L hLK (φ.1 ^ n) =
      (Multiplicative.ofAdd (1 : ZHat)) ^ n := by
  rw [map_pow,
    D.extensionNormalizedDegree_frobenius_eq_pow K L hLK φ, hφ]
  simp

/-- A positive power of a degree-one Frobenius element, with the exponent
recorded exactly.  These are the elements `σ = φⁿ` and `σⁿ = φⁿ²`. -/
def frobeniusPowerOfDegreeOne (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (n : ℕ) (hn : 0 < n) : D.FrobeniusElements K L hLK :=
  ⟨φ.1 ^ n,
    ⟨n, hn, D.extensionNormalizedDegree_pow_of_degreeOne
      K L hLK φ hφ n⟩⟩

/-- The degree-one Frobenius power has the stated ambient coercion. -/
@[simp]
theorem frobeniusPowerOfDegreeOne_coe (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (n : ℕ) (hn : 0 < n) :
    (D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn).1 = φ.1 ^ n :=
  rfl

/-- The Frobenius exponent of the degree-one power is the supplied exponent. -/
@[simp]
theorem frobeniusExponent_powerOfDegreeOne (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (n : ℕ) (hn : 0 < n) :
    D.frobeniusExponent K L hLK
      (D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn) = n :=
  by
    apply proCIntegerOne_pow_nat_injective
    calc
      (Multiplicative.ofAdd (1 : ZHat)) ^
          D.frobeniusExponent K L hLK
            (D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn) =
          D.extensionNormalizedDegree K L hLK
            (D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn).1 :=
        (D.extensionNormalizedDegree_frobenius_eq_pow K L hLK
          (D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn)).symm
      _ = (Multiplicative.ofAdd (1 : ZHat)) ^ n :=
        D.extensionNormalizedDegree_pow_of_degreeOne K L hLK φ hφ n

theorem frobeniusClosure_power_mul_le (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    (D.frobeniusClosure K L hLK
      (D.frobeniusPowerOfDegreeOne K L hLK φ hφ (n * m)
        (Nat.mul_pos hn hm))).toSubgroup ≤
      (D.frobeniusClosure K L hLK
        (D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn)).toSubgroup := by
  let Q := K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK
  let x : Q := φ.1 ^ n
  let C : ClosedSubgroup Q := closedSubgroupGenerated ({x} : Set Q)
  have hxC : x ∈ C.toSubgroup :=
    Subgroup.le_topologicalClosure _
      (Subgroup.subset_closure (by simp [x]))
  have hpowC : φ.1 ^ (n * m) ∈ C.toSubgroup := by
    rw [pow_mul]
    exact C.toSubgroup.pow_mem hxC m
  change (closedSubgroupGenerated
      (Set.range (fun _ : Unit => φ.1 ^ (n * m)))).toSubgroup ≤
    (closedSubgroupGenerated
      (Set.range (fun _ : Unit => φ.1 ^ n))).toSubgroup
  have hrangeLeft : Set.range (fun _ : Unit => φ.1 ^ (n * m)) =
      ({φ.1 ^ (n * m)} : Set Q) := by ext q; simp
  have hrangeRight : Set.range (fun _ : Unit => φ.1 ^ n) =
      ({φ.1 ^ n} : Set Q) := by ext q; simp
  rw [hrangeLeft, hrangeRight]
  apply Subgroup.topologicalClosure_minimal
  · rw [Subgroup.closure_le]
    simpa [C, x] using hpowC
  · exact (closedSubgroupGenerated ({φ.1 ^ n} : Set Q)).isClosed'

/-- If `Σ` is fixed by `φⁿ`, then the field fixed by `φⁿᵐ` extends `Σ`.
This is the tower `Σ_m / Σ` used in the universal norm-descent lemma. -/
theorem frobeniusPowerFixedField_le (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    (D.frobeniusFixedField K L hLK
      (D.frobeniusPowerOfDegreeOne K L hLK φ hφ (n * m)
        (Nat.mul_pos hn hm))).toSubgroup ≤
      (D.frobeniusFixedField K L hLK
        (D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn)).toSubgroup := by
  rintro z ⟨k, hk, rfl⟩
  exact ⟨k,
    D.frobeniusClosure_power_mul_le K L hLK φ hφ n m hn hm hk,
    rfl⟩

/-- The power-fixed-field tower is Galois.  On the group side this is the
normality of `closure ⟨φⁿᵐ⟩` inside the procyclic group
`closure ⟨φⁿ⟩`. -/
theorem frobeniusPowerFixedField_normal (D : DegreeData G)
    [IsTopologicalGroup G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
    let σm := D.frobeniusPowerOfDegreeOne K L hLK φ hφ (n * m)
      (Nat.mul_pos hn hm)
    let S := D.frobeniusFixedField K L hLK σ
    let T := D.frobeniusFixedField K L hLK σm
    (extensionSubgroup S T
      (D.frobeniusPowerFixedField_le K L hLK φ hφ n m hn hm)).Normal := by
  dsimp only
  let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
  let σm := D.frobeniusPowerOfDegreeOne K L hLK φ hφ (n * m)
    (Nat.mul_pos hn hm)
  let S := D.frobeniusFixedField K L hLK σ
  let T := D.frobeniusFixedField K L hLK σm
  let hSK := D.frobeniusFixedField_le K L hLK σ
  let hTK := D.frobeniusFixedField_le K L hLK σm
  let hTS := D.frobeniusPowerFixedField_le K L hLK φ hφ n m hn hm
  let C := D.frobeniusClosure K L hLK σ
  let Cm := D.frobeniusClosure K L hLK σm
  let : CommGroup C := D.frobeniusClosureCommGroup K L hLK σ
  have hCmC : Cm.toSubgroup ≤ C.toSubgroup :=
    D.frobeniusClosure_power_mul_le K L hLK φ hφ n m hn hm
  constructor
  intro t ht s
  have htT : t.1 ∈ T.toSubgroup :=
    (mem_extensionSubgroup_iff S T hTS t).1 ht
  let tK : K.field.toSubgroup := ⟨t.1, hSK t.2⟩
  let sK : K.field.toSubgroup := ⟨s.1, hSK s.2⟩
  have htFixed : tK ∈ D.frobeniusFixedSubgroupWithin K L hLK σm := by
    rw [← D.extensionSubgroup_frobeniusFixedField K L hLK σm]
    exact (mem_extensionSubgroup_iff K.field T hTK tK).2 htT
  have hsFixed : sK ∈ D.frobeniusFixedSubgroupWithin K L hLK σ := by
    rw [← D.extensionSubgroup_frobeniusFixedField K L hLK σ]
    exact (mem_extensionSubgroup_iff K.field S hSK sK).2 s.2
  let a : C := ⟨QuotientGroup.mk sK, hsFixed⟩
  let b : C := ⟨QuotientGroup.mk tK, hCmC htFixed⟩
  have hconj :
      (QuotientGroup.mk sK :
          K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) *
        QuotientGroup.mk tK * (QuotientGroup.mk sK)⁻¹ =
          QuotientGroup.mk tK := by
    exact congrArg Subtype.val (by
      change a * b * a⁻¹ = b
      simp)
  apply (mem_extensionSubgroup_iff S T hTS _).2
  let cK : K.field.toSubgroup := ⟨s.1 * t.1 * s.1⁻¹, by
    exact K.field.toSubgroup.mul_mem
      (K.field.toSubgroup.mul_mem (hSK s.2) (hSK t.2))
      (K.field.toSubgroup.inv_mem (hSK s.2))⟩
  refine ⟨cK, ?_, rfl⟩
  change QuotientGroup.mk cK ∈ Cm.toSubgroup
  change QuotientGroup.mk sK * QuotientGroup.mk tK *
      (QuotientGroup.mk sK)⁻¹ ∈ Cm.toSubgroup
  rw [hconj]
  exact htFixed

end DegreeData
end degreeOnePowerFields

end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_FrobeniusQuotientDescent
attribute [-instance] _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.finiteNormQuotientAddCommGroup _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.chosenUnramifiedFrobeniusLift_exponent _root_.ClassFormation.DegreeData.frobeniusExponent_powerOfDegreeOne _root_.ClassFormation.DegreeData.frobeniusFixedFieldAction_coe _root_.ClassFormation.DegreeData.frobeniusPowerOfDegreeOne_coe _root_.ClassFormation.DegreeData.maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClass _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_eq_one_iff _root_.ClassFormation.FiniteGaloisSubextension.toGaloisSubextension_isTotallyRamified_iff _root_.ClassFormation.FiniteGaloisSubextension.toGaloisSubextension_isUnramified_iff _root_.ClassFormation.ValuationData.canonicalUnramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.canonicalValueQuotientHom_mk _root_.ClassFormation.ValuationData.canonicalValueReduction_one _root_.ClassFormation.ValuationData.unramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.finiteNormClass_add _root_.ClassFormation.finiteNormClass_eq_zero_iff _root_.ClassFormation.finiteNormClass_nsmul _root_.ClassFormation.finiteNormClass_sub _root_.ClassFormation.finiteNormClass_zero _root_.ClassFormation.finiteNormQuotientConcreteEquiv_finiteNormClass _root_.ClassFormation.finiteNormQuotientLift_finiteNormClass _root_.ClassFormation.mem_normFilterBasis_iff _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

universe u v

namespace ClassFormation

open KummerTheory
open CyclicCohomology

/-!
# Frobenius quotient descent

This module constructs the Frobenius quotient representation, identifies its
Birkhoff sums with Frobenius power sums, and proves the finite-support
descent from the maximal unramified field.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators

section representationDescent

/-!
Mathlib's `Rep ℤ G` requires its coefficient ring and acting group in the
same universe; `IntegralRepGroupType` names that shared boundary.
-/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The linear action of `G(\widetilde L/K)` on
`A_{\widetilde L}`.  This packages the concrete quotient action from
the Frobenius norm-identity lemma in the form needed by the Tate-cohomology calculation. -/
noncomputable def frobeniusQuotientActionLinearMap (D : DegreeData G)
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    (q : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK) :
    ambientFixedAddSubgroup A (D.maximalUnramifiedField L) →ₗ[ℤ]
      ambientFixedAddSubgroup A (D.maximalUnramifiedField L) where
  toFun := D.frobeniusQuotientAction A K L hLK q
  map_add' a b := by
    refine Quotient.inductionOn' q ?_
    intro k
    apply Subtype.ext
    change A.ρ k.1 (a.1 + b.1) = A.ρ k.1 a.1 + A.ρ k.1 b.1
    exact map_add (A.ρ k.1) _ _
  map_smul' n a := by
    refine Quotient.inductionOn' q ?_
    intro k
    apply Subtype.ext
    change A.ρ k.1 (n • a.1) = n • A.ρ k.1 a.1
    exact map_zsmul (A.ρ k.1) n a.1

/-- The actual `G(\widetilde L/K)`-representation on
`A_{\widetilde L}` used in the universal norm-descent lemma. -/
noncomputable def frobeniusQuotientRepresentation (D : DegreeData G)
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal] :
    Rep ℤ (K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK) :=
  Rep.of
    { toFun := D.frobeniusQuotientActionLinearMap A K L hLK
      map_one' := by
        ext a
        change A.ρ (1 : G) a.1 = a.1
        simp
      map_mul' := by
        intro q r
        refine Quotient.inductionOn₂' q r ?_
        intro k l
        ext a
        change A.ρ (k.1 * l.1) a.1 = A.ρ k.1 (A.ρ l.1 a.1)
        rw [map_mul]
        rfl }

/-- The Frobenius quotient representation evaluates by the chosen quotient action. -/
@[simp]
theorem frobeniusQuotientRepresentation_apply (D : DegreeData G)
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    (q : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    (D.frobeniusQuotientRepresentation A K L hLK).ρ q a =
      D.frobeniusQuotientAction A K L hLK q a :=
  rfl

/-- The Birkhoff sum of the quotient action is the corresponding sum of Frobenius powers. -/
theorem birkhoffSum_eq_frobeniusPowerSum (D : DegreeData G)
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    (φ : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK) (n : ℕ)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    birkhoffSum
        ((D.frobeniusQuotientRepresentation A K L hLK).ρ φ) id n a =
      D.frobeniusPowerSum A K L hLK φ n a := by
  unfold birkhoffSum frobeniusPowerSum
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [id_eq, Finset.mem_range.mp hi, dite_true]
  exact (rep_action_pow_eq_iterate
    (D.frobeniusQuotientRepresentation A K L hLK) φ i a).symm

/-- A Frobenius power sum splits into its first `n` terms and a translated
block of `m` terms. -/
theorem frobeniusPowerSum_add (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    (φ : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK)
    (n m : ℕ)
    (x : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    D.frobeniusPowerSum A K L hLK φ (n + m) x =
      D.frobeniusPowerSum A K L hLK φ n x +
        D.frobeniusPowerSum A K L hLK φ m
          (D.frobeniusQuotientAction A K L hLK (φ ^ n) x) := by
  let B := D.frobeniusQuotientRepresentation A K L hLK
  have hsum (r : ℕ)
      (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
      birkhoffSum (B.ρ φ) id r a =
        D.frobeniusPowerSum A K L hLK φ r a :=
    D.birkhoffSum_eq_frobeniusPowerSum A K L hLK φ r a
  have hiterate : ((B.ρ φ)^[n]) x =
      D.frobeniusQuotientAction A K L hLK (φ ^ n) x :=
    (rep_action_pow_eq_iterate B φ n x).symm
  exact ((hsum (n + m) x).symm.trans
    (birkhoffSum_add (B.ρ φ) id n m x)).trans
      (congrArg₂
        (fun a b : ambientFixedAddSubgroup A (D.maximalUnramifiedField L) => a + b)
        (hsum n x)
        ((hsum m (((B.ρ φ)^[n]) x)).trans
          (congrArg (D.frobeniusPowerSum A K L hLK φ m) hiterate)))

/-- Actual additive telescoping identity for the Frobenius power sum. -/
theorem frobeniusPowerSum_action_sub (D : DegreeData G)
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    (φ : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK) (n : ℕ)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    D.frobeniusQuotientAction A K L hLK φ
        (D.frobeniusPowerSum A K L hLK φ n a) -
        D.frobeniusPowerSum A K L hLK φ n a =
      D.frobeniusQuotientAction A K L hLK (φ ^ n) a - a := by
  let B := D.frobeniusQuotientRepresentation A K L hLK
  have h := birkhoffSum_apply_sub_birkhoffSum (B.ρ φ) id n a
  have hshift :
      B.ρ φ (birkhoffSum (B.ρ φ) id n a) =
        birkhoffSum (B.ρ φ) id n (B.ρ φ a) := by
    calc
      B.ρ φ (birkhoffSum (B.ρ φ) id n a) =
          birkhoffSum (B.ρ φ) (B.ρ φ ∘ id) n a :=
        map_birkhoffSum (B.ρ φ) (B.ρ φ) id n a
      _ = birkhoffSum (B.ρ φ) id n (B.ρ φ a) := by
        unfold birkhoffSum
        apply Finset.sum_congr rfl
        intro i _
        simp only [Function.comp_apply, id_eq]
        exact (Function.Commute.self_iterate (B.ρ φ) i).eq a
  rw [← hshift] at h
  simp only [id_eq] at h
  rw [D.birkhoffSum_eq_frobeniusPowerSum A K L hLK,
    ← rep_action_pow_eq_iterate B φ n a] at h
  change
    D.frobeniusQuotientAction A K L hLK φ
          (D.frobeniusPowerSum A K L hLK φ n a) -
        D.frobeniusPowerSum A K L hLK φ n a =
      D.frobeniusQuotientAction A K L hLK (φ ^ n) a - a at h
  exact h

/-- The difference of Frobenius power sums is represented by universal norm descent. -/
theorem frobeniusPowerSum_sub_universalNormDescent (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    (φ : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK)
    (n : ℕ)
    (x y : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    D.frobeniusPowerSum A K L hLK φ n (x - y) =
      D.frobeniusPowerSum A K L hLK φ n x -
        D.frobeniusPowerSum A K L hLK φ n y := by
  unfold DegreeData.frobeniusPowerSum
  change
    (∑ i : Fin n,
      D.frobeniusQuotientActionLinearMap A K L hLK (φ ^ i.1) (x - y)) =
      (∑ i : Fin n,
        D.frobeniusQuotientActionLinearMap A K L hLK (φ ^ i.1) x) -
      ∑ i : Fin n,
        D.frobeniusQuotientActionLinearMap A K L hLK (φ ^ i.1) y
  simp only [map_sub, Finset.sum_sub_distrib]

/-- Equivariance of `N_{\widetilde L/\widetilde K}` expressed inside
`A_{\widetilde L}`. -/
theorem maximalUnramifiedNorm_frobeniusQuotientAction (D : DegreeData G)
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (q : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    letI : Finite
        ((D.maximalUnramifiedField K).toSubgroup ⧸
          extensionSubgroup (D.maximalUnramifiedField K)
            (D.maximalUnramifiedField L)
            (D.maximalUnramifiedField_mono hLK)) :=
      D.maximalUnramifiedExtension_finite K L hLK
    fixedFieldInclusion A (D.maximalUnramifiedField K)
        (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
        (relativeNorm A (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
          (D.frobeniusQuotientAction A K L hLK q a)) =
      D.frobeniusQuotientAction A K L hLK q
        (fixedFieldInclusion A (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
          (relativeNorm A (D.maximalUnramifiedField K)
            (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
            a)) := by
  let : Finite
      ((D.maximalUnramifiedField K).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) :=
    D.maximalUnramifiedExtension_finite K L hLK
  apply Subtype.ext
  exact D.relativeNorm_frobeniusQuotientAction A K L hLK q a

/-- A degree-zero element acts trivially on an element already defined
over `\widetilde K`. -/
theorem frobeniusQuotientAction_fixed_of_degreeZero (D : DegreeData G)
    (A : Rep ℤ G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : D.extensionNormalizedDegree K L hLK q = 1)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField K.field)) :
    D.frobeniusQuotientAction A K.field L hLK q
        (fixedFieldInclusion A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) a) =
      fixedFieldInclusion A (D.maximalUnramifiedField K.field)
        (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) a := by
  let k : K.field.toSubgroup := Quotient.out q
  have hkq :
      (QuotientGroup.mk k :
        K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) = q :=
    Quotient.out_eq' q
  have hkDegree : D.normalizedDegree K k = 1 := by
    calc
      D.normalizedDegree K k =
          D.extensionNormalizedDegree K L hLK (QuotientGroup.mk k) := rfl
      _ = D.extensionNormalizedDegree K L hLK q :=
        congrArg (D.extensionNormalizedDegree K L hLK) hkq
      _ = 1 := hq
  have hkInertia : k ∈ D.fieldInertiaWithin K.field := by
    rw [← D.normalizedDegree_ker K]
    exact hkDegree
  let kI : (D.maximalUnramifiedField K.field).toSubgroup :=
    ⟨k.1, ⟨k.2, hkInertia⟩⟩
  rw [← hkq]
  apply Subtype.ext
  exact a.2 kI

/-- Applying `N_{\widetilde L/\widetilde K}` to equation `(*)` kills
all degree-zero differences.  Hence the norm of `u` is fixed by the
chosen degree-one Frobenius element. -/
theorem maximalUnramifiedNorm_fixed_of_hstar (D : DegreeData G)
    (A : Rep ℤ G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    {ι : Type v} (s : Finset ι)
    (φ : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (τ : ι →
      (D.extensionNormalizedDegreeContinuous K L hLK).toMonoidHom.ker)
    (u : ambientFixedAddSubgroup A (D.maximalUnramifiedField L))
    (uᵢ : ι → ambientFixedAddSubgroup A (D.maximalUnramifiedField L))
    (hstar : D.frobeniusQuotientAction A K.field L hLK φ u - u =
      ∑ i ∈ s,
        (D.frobeniusQuotientAction A K.field L hLK (τ i).1 (uᵢ i) - uᵢ i)) :
    letI : Finite
        ((D.maximalUnramifiedField K.field).toSubgroup ⧸
          extensionSubgroup (D.maximalUnramifiedField K.field)
            (D.maximalUnramifiedField L)
            (D.maximalUnramifiedField_mono hLK)) :=
      D.maximalUnramifiedExtension_finite K.field L hLK
    let N := relativeNorm A (D.maximalUnramifiedField K.field)
      (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
    let b := fixedFieldInclusion A (D.maximalUnramifiedField K.field)
      (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) (N u)
    D.frobeniusQuotientAction A K.field L hLK φ b = b := by
  dsimp only
  let : Finite
      ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) :=
    D.maximalUnramifiedExtension_finite K.field L hLK
  let N := relativeNorm A (D.maximalUnramifiedField K.field)
    (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
  let J := fixedFieldInclusion A (D.maximalUnramifiedField K.field)
    (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
  have hnorm := congrArg (J.comp N) hstar
  simp only [map_sub, map_sum] at hnorm
  change J (N (D.frobeniusQuotientAction A K.field L hLK φ u)) - J (N u) =
    ∑ i ∈ s,
      (J (N (D.frobeniusQuotientAction A K.field L hLK (τ i).1 (uᵢ i))) -
        J (N (uᵢ i))) at hnorm
  have hφEquiv :
      J (N (D.frobeniusQuotientAction A K.field L hLK φ u)) =
        D.frobeniusQuotientAction A K.field L hLK φ (J (N u)) := by
    simpa [J, N] using
      D.maximalUnramifiedNorm_frobeniusQuotientAction A K.field L hLK φ u
  rw [hφEquiv] at hnorm
  have hzero (i : ι) :
      J (N (D.frobeniusQuotientAction A K.field L hLK (τ i).1 (uᵢ i))) =
        J (N (uᵢ i)) := by
    calc
      J (N (D.frobeniusQuotientAction A K.field L hLK (τ i).1 (uᵢ i))) =
          D.frobeniusQuotientAction A K.field L hLK (τ i).1 (J (N (uᵢ i))) := by
        simpa [J, N] using
          D.maximalUnramifiedNorm_frobeniusQuotientAction
            A K.field L hLK (τ i).1 (uᵢ i)
      _ = J (N (uᵢ i)) := by
        simpa [J, N] using D.frobeniusQuotientAction_fixed_of_degreeZero
          A K L hLK (τ i).1 (τ i).2 (N (uᵢ i))
  simp_rw [hzero] at hnorm
  have hnormzero :
      D.frobeniusQuotientAction A K.field L hLK φ (J (N u)) - J (N u) = 0 := by
    simpa only [sub_self, Finset.sum_const_zero] using hnorm
  simpa [J, N] using sub_eq_zero.mp hnormzero

/-- A `\widetilde K`-fixed element with finite Galois support descends to
`K` as soon as it is fixed by a degree-one Frobenius lift.  The proof is
the finite-quotient argument implicit: the finite degree-quotient decomposition writes
each element of `Gal(P/K)` as a positive Frobenius power up to inertia. -/
theorem descend_maximalUnramified_fixed_of_finiteSupport (D : DegreeData G)
    (A : Rep ℤ G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (P : FiniteIntermediateField (D.maximalUnramifiedField L) K.field)
    [hPnormal : (extensionSubgroup K.field P.field P.below).Normal]
    (aI : ambientFixedAddSubgroup A (D.maximalUnramifiedField K.field))
    (aP : ambientFixedAddSubgroup A P.field)
    (hsupport :
      fixedFieldInclusion A P.field (D.maximalUnramifiedField L) P.above aP =
        fixedFieldInclusion A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) aI)
    (hfixed :
      D.frobeniusQuotientAction A K.field L hLK φ.1
          (fixedFieldInclusion A (D.maximalUnramifiedField K.field)
            (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) aI) =
        fixedFieldInclusion A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) aI) :
    ∃ aK : ambientFixedAddSubgroup A K.field,
      fixedFieldInclusion A K.field (D.maximalUnramifiedField K.field)
        (D.maximalUnramifiedField_le K.field) aK = aI := by
  let hPfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field P.field P.below) := P.finite
  let f : K.field.toSubgroup := Quotient.out φ.1
  have hfφ :
      (QuotientGroup.mk f :
        K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) = φ.1 :=
    Quotient.out_eq' φ.1
  have hfDegree : D.normalizedDegree K f =
      Multiplicative.ofAdd (1 : ZHat) := by
    calc
      D.normalizedDegree K f =
          D.extensionNormalizedDegree K L hLK (QuotientGroup.mk f) := rfl
      _ = D.extensionNormalizedDegree K L hLK φ.1 :=
        congrArg (D.extensionNormalizedDegree K L hLK) hfφ
      _ = (Multiplicative.ofAdd (1 : ZHat)) ^
            D.frobeniusExponent K L hLK φ :=
        D.extensionNormalizedDegree_frobenius_eq_pow K L hLK φ
      _ = Multiplicative.ofAdd (1 : ZHat) := by simp [hφ]
  have hfFixed : A.ρ f.1 aI.1 = aI.1 := by
    rw [← hfφ] at hfixed
    exact congrArg Subtype.val hfixed
  have hfPowFixed (n : ℕ) : A.ρ (f.1 ^ n) aI.1 = aI.1 := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, map_mul]
        change A.ρ (f.1 ^ n) (A.ρ f.1 aI.1) = aI.1
        rw [hfFixed, ih]
  have hsval : aP.1 = aI.1 := congrArg Subtype.val hsupport
  have hKfixed (k : K.field.toSubgroup) : A.ρ k.1 aI.1 = aI.1 := by
    obtain ⟨q, hqk⟩ := D.frobeniusRestriction_surjective K P.field P.below
      (QuotientGroup.mk k)
    obtain ⟨n, _hn, hqDegree⟩ := q.2
    let t : K.field.toSubgroup := Quotient.out q.1
    have htq :
        (QuotientGroup.mk t :
          K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field P.field P.below) = q.1 :=
      Quotient.out_eq' q.1
    have htDegree : D.normalizedDegree K t =
        (Multiplicative.ofAdd (1 : ZHat)) ^ n := by
      calc
        D.normalizedDegree K t =
            D.extensionNormalizedDegree K P.field P.below
              (QuotientGroup.mk t) := rfl
        _ = D.extensionNormalizedDegree K P.field P.below q.1 :=
          congrArg (D.extensionNormalizedDegree K P.field P.below) htq
        _ = _ := hqDegree
    let z : K.field.toSubgroup := t⁻¹ * f ^ n
    have hzInertia : z ∈ D.fieldInertiaWithin K.field := by
      rw [← D.normalizedDegree_ker K]
      change D.normalizedDegree K z = 1
      rw [map_mul, map_inv, map_pow, htDegree, hfDegree]
      simp
    let zI : (D.maximalUnramifiedField K.field).toSubgroup :=
      ⟨z.1, ⟨z.2, hzInertia⟩⟩
    have hzFixed : A.ρ z.1 aI.1 = aI.1 := aI.2 zI
    have htFixed : A.ρ t.1 aI.1 = aI.1 := by
      calc
        A.ρ t.1 aI.1 = A.ρ t.1 (A.ρ z.1 aI.1) :=
          congrArg (A.ρ t.1) hzFixed.symm
        _ = A.ρ (t.1 * z.1) aI.1 := by rw [map_mul]; rfl
        _ = A.ρ (f.1 ^ n) aI.1 := by simp [z]
        _ = aI.1 := hfPowFixed n
    have htk :
        (QuotientGroup.mk t :
          K.field.toSubgroup ⧸ extensionSubgroup K.field P.field P.below) =
        QuotientGroup.mk k := by
      calc
        QuotientGroup.mk t =
            D.extensionRestriction K.field P.field P.below (QuotientGroup.mk t) := rfl
        _ = D.extensionRestriction K.field P.field P.below q.1 :=
          congrArg (D.extensionRestriction K.field P.field P.below) htq
        _ = QuotientGroup.mk k := hqk
    have hrel : t⁻¹ * k ∈ extensionSubgroup K.field P.field P.below :=
      QuotientGroup.eq.mp htk
    let rP : P.field.toSubgroup := ⟨(t⁻¹ * k).1, hrel⟩
    have hrval : rP.1 = (t⁻¹ * k).1 := rfl
    have hrval' : rP.1 = t.1⁻¹ * k.1 := hrval
    have hrFixed : A.ρ (t.1⁻¹ * k.1) aI.1 = aI.1 := by
      rw [← hsval, ← hrval']
      exact aP.2 rP
    calc
      A.ρ k.1 aI.1 = A.ρ (t.1 * (t.1⁻¹ * k.1)) aI.1 := by simp
      _ = A.ρ t.1 (A.ρ (t.1⁻¹ * k.1) aI.1) := by rw [map_mul]; rfl
      _ = A.ρ t.1 aI.1 := by rw [hrFixed]
      _ = aI.1 := htFixed
  let aK : ambientFixedAddSubgroup A K.field := ⟨aI.1, hKfixed⟩
  refine ⟨aK, ?_⟩
  apply Subtype.ext
  rfl

end DegreeData

end representationDescent

end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_FrobeniusFixedFieldTower
attribute [-instance] _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.upperQuotient_groupInstance _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.chosenUnramifiedFrobeniusLift_exponent _root_.ClassFormation.DegreeData.frobeniusFixedFieldAction_coe _root_.ClassFormation.DegreeData.frobeniusQuotientRepresentation_apply _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.FiniteGaloisSubextension.intermediateFiniteAbelianOfCommutatorLe_field _root_.ClassFormation.FiniteGaloisSubextension.lowerQuotientEquiv_mk _root_.ClassFormation.FiniteGaloisSubextension.lowerQuotientEquiv_mk_coe _root_.ClassFormation.FiniteGaloisSubextension.lowerRestrictionHom_apply_coe _root_.ClassFormation.FiniteGaloisSubextension.mem_intermediateSubgroup_iff _root_.ClassFormation.FiniteGaloisSubextension.upperQuotientEquiv_mk_mk _root_.ClassFormation.FiniteGaloisSubextension.upperQuotientMk_apply _root_.ClassFormation.ValuationData.canonicalUnramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.canonicalValueQuotientHom_mk _root_.ClassFormation.ValuationData.canonicalValueReduction_one _root_.ClassFormation.ValuationData.unramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.conjugateStableAction_coe _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.mem_normFilterBasis_iff _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-!
Bundles finite towers of Frobenius fixed fields together with the normality and finiteness data
needed for norm and unit calculations.
-/

universe u

namespace ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The Frobenius fixed field bundled with its proved absolute finiteness.
This is the field object used by valuation and unit APIs. -/
noncomputable def frobeniusFixedAbstractField
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : DegreeData.FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK)
    [Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G)
        (D.frobeniusFixedField K L hLK σ)
        (le_baseField (D.frobeniusFixedField K L hLK σ)))] :
    FiniteAbstractField G where
  field := D.frobeniusFixedField K L hLK σ
  finite := inferInstance

/-- A finite normal tower between two Frobenius fixed fields.

The ambient Galois extension, both Frobenius elements, the fixed-field
inclusion, and exactly the finiteness hypotheses needed by the unit
representation are stored once.  In particular, downstream statements no
longer re-thread the proof-dependent subgroup inclusions and quotient
instances independently. -/
structure FrobeniusFixedFieldTower
    (D : DegreeData G) [IsTopologicalGroup G] where
  /-- The finite-residue field in which the ambient Galois extension begins. -/
  ambientBase : DegreeData.FiniteResidueAbstractField D
  /-- The ambient Galois subextension. -/
  ambient : GaloisSubextension ambientBase.field
  /-- The Frobenius element whose fixed field is the base of the tower. -/
  baseFrobenius :
    D.FrobeniusElements ambientBase ambient.field ambient.below
  /-- The Frobenius element whose fixed field is the top of the tower. -/
  fieldFrobenius :
    D.FrobeniusElements ambientBase ambient.field ambient.below
  /-- Inclusion of the top fixed field into the base fixed field. -/
  field_le_base :
    (D.frobeniusFixedField ambientBase ambient.field ambient.below
        fieldFrobenius).toSubgroup ≤
      (D.frobeniusFixedField ambientBase ambient.field ambient.below
        baseFrobenius).toSubgroup
  /-- The relative quotient between the two fixed fields is finite. -/
  finiteQuotient :
    Finite
      ((D.frobeniusFixedField ambientBase ambient.field ambient.below
          baseFrobenius).toSubgroup ⧸
        extensionSubgroup
          (D.frobeniusFixedField ambientBase ambient.field ambient.below
            baseFrobenius)
          (D.frobeniusFixedField ambientBase ambient.field ambient.below
            fieldFrobenius)
          field_le_base)
  /-- The base fixed field is finite over the distinguished base. -/
  baseAbsoluteFinite :
    Finite
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G)
          (D.frobeniusFixedField ambientBase ambient.field ambient.below
            baseFrobenius)
          (le_baseField
            (D.frobeniusFixedField ambientBase ambient.field ambient.below
              baseFrobenius)))
  /-- The top fixed field is finite over the distinguished base. -/
  fieldAbsoluteFinite :
    Finite
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G)
          (D.frobeniusFixedField ambientBase ambient.field ambient.below
            fieldFrobenius)
          (le_baseField
            (D.frobeniusFixedField ambientBase ambient.field ambient.below
              fieldFrobenius)))
  /-- The relative subgroup between the fixed fields is normal. -/
  normal :
    (extensionSubgroup
      (D.frobeniusFixedField ambientBase ambient.field ambient.below
        baseFrobenius)
      (D.frobeniusFixedField ambientBase ambient.field ambient.below
        fieldFrobenius)
      field_le_base).Normal
  /-- The two chosen ambient Frobenius elements commute. -/
  commute :
    baseFrobenius.1 * fieldFrobenius.1 =
      fieldFrobenius.1 * baseFrobenius.1

namespace FrobeniusFixedFieldTower

variable {D : DegreeData G} [IsTopologicalGroup G]

/-- The lower fixed field, finite over the distinguished base. -/
noncomputable def base (T : FrobeniusFixedFieldTower D) :
    FiniteAbstractField G := by
  letI : Finite
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G)
          (D.frobeniusFixedField T.ambientBase T.ambient.field T.ambient.below
            T.baseFrobenius)
          (le_baseField
            (D.frobeniusFixedField T.ambientBase T.ambient.field T.ambient.below
              T.baseFrobenius))) :=
    T.baseAbsoluteFinite
  exact D.frobeniusFixedAbstractField T.ambientBase T.ambient.field
    T.ambient.below T.baseFrobenius

/-- The upper fixed field, finite over the distinguished base. -/
noncomputable def field (T : FrobeniusFixedFieldTower D) :
    FiniteAbstractField G := by
  letI : Finite
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G)
          (D.frobeniusFixedField T.ambientBase T.ambient.field T.ambient.below
            T.fieldFrobenius)
          (le_baseField
            (D.frobeniusFixedField T.ambientBase T.ambient.field T.ambient.below
              T.fieldFrobenius))) :=
    T.fieldAbsoluteFinite
  exact D.frobeniusFixedAbstractField T.ambientBase T.ambient.field
    T.ambient.below T.fieldFrobenius

/-- The finite extension between the two bundled fixed fields. -/
noncomputable def extension (T : FrobeniusFixedFieldTower D) :
    FiniteAbstractFieldExtension G where
  field := T.field
  base := T.base
  below := T.field_le_base
  finiteQuotient := T.finiteQuotient

/-- A concrete lower-fixed-field element representing its Frobenius class. -/
structure Representative (T : FrobeniusFixedFieldTower D) where
  /-- The chosen element in the base fixed-field subgroup. -/
  element : T.extension.base.field.toSubgroup
  /-- The chosen element maps to the prescribed ambient Frobenius class. -/
  mapsToFrobenius :
    D.frobeniusFixedFieldToClosure T.ambientBase T.ambient.field
        T.ambient.below T.baseFrobenius element =
      D.frobeniusInClosure T.ambientBase T.ambient.field
        T.ambient.below T.baseFrobenius

/-- The extension subgroup of a bundled Frobenius fixed-field tower is normal. -/
instance extensionNormal (T : FrobeniusFixedFieldTower D) :
    (extensionSubgroup T.extension.base.field T.extension.field.field
      T.extension.below).Normal :=
  T.normal

/-- A representative which generates the finite fixed-field quotient. -/
structure CyclicGenerator (T : FrobeniusFixedFieldTower D)
    extends Representative T where
  /-- Every relative Galois element is a power of the representative's class. -/
  generates :
    ∀ x :
      T.extension.base.field.toSubgroup ⧸
        extensionSubgroup T.extension.base.field T.extension.field.field
          T.extension.below,
      x ∈ Subgroup.zpowers (QuotientGroup.mk toRepresentative.element)

/-- The Galois quotient of a bundled Frobenius fixed-field extension is finite. -/
instance extensionFinite (T : FrobeniusFixedFieldTower D) :
    Finite
      (T.extension.base.field.toSubgroup ⧸
        extensionSubgroup T.extension.base.field T.extension.field.field
          T.extension.below) :=
  T.finiteQuotient

/-- The lower Frobenius fixed field in the tower is finite over the distinguished base field. -/
instance baseAbsoluteFiniteInstance (T : FrobeniusFixedFieldTower D) :
    Finite
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G)
          (D.frobeniusFixedField T.ambientBase T.ambient.field T.ambient.below
            T.baseFrobenius)
          (le_baseField
            (D.frobeniusFixedField T.ambientBase T.ambient.field T.ambient.below
              T.baseFrobenius))) :=
  T.baseAbsoluteFinite

/-- The upper Frobenius fixed field in the tower is finite over the distinguished base field. -/
instance fieldAbsoluteFiniteInstance (T : FrobeniusFixedFieldTower D) :
    Finite
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G)
          (D.frobeniusFixedField T.ambientBase T.ambient.field T.ambient.below
            T.fieldFrobenius)
          (le_baseField
            (D.frobeniusFixedField T.ambientBase T.ambient.field T.ambient.below
              T.fieldFrobenius))) :=
  T.fieldAbsoluteFinite

end FrobeniusFixedFieldTower

/-- A Frobenius fixed-field tower whose ambient Galois extension is finite.
The additional finiteness is stored on the opaque quotient object exposed by
`GaloisSubextension`. -/
structure FiniteAmbientFrobeniusFixedFieldTower
    (D : DegreeData G) [IsTopologicalGroup G]
    extends FrobeniusFixedFieldTower D where
  /-- The ambient Galois quotient is finite. -/
  ambientFinite : Finite toFrobeniusFixedFieldTower.ambient.extensionQuotient

namespace FiniteAmbientFrobeniusFixedFieldTower

variable {D : DegreeData G} [IsTopologicalGroup G]

/--
The ambient Galois quotient stored in a finite Frobenius fixed-field tower is finite.
-/
instance ambientQuotientFinite
    (T : FiniteAmbientFrobeniusFixedFieldTower D) :
    Finite T.ambient.extensionQuotient :=
  T.ambientFinite

/-- Finiteness transported to the quotient presentation required by the
underlying Frobenius calculations. -/
noncomputable instance ambientRepresentedQuotientFinite
    (T : FiniteAmbientFrobeniusFixedFieldTower D) :
    Finite
      (T.ambientBase.field.toSubgroup ⧸
        extensionSubgroup T.ambientBase.field T.ambient.field
          T.ambient.below) :=
  Finite.of_equiv T.ambient.extensionQuotient
    T.ambient.extensionQuotientMulEquiv

end FiniteAmbientFrobeniusFixedFieldTower

/-- The power tower fixed by `φⁿ² ≤ φⁿ`.

Only data already required by the universal norm-descent construction is
stored: the finite ambient Galois extension, a degree-one Frobenius, its
positive exponent, and the three fixed-field finiteness witnesses.  The
fixed-field inclusion, normality, and commutation relation are consequences
of the power construction. -/
structure FrobeniusPowerFixedFieldTower
    (D : DegreeData G) [IsTopologicalGroup G] where
  /-- The finite-residue field at the base of the ambient extension. -/
  ambientBase : DegreeData.FiniteResidueAbstractField D
  /-- The finite ambient Galois subextension. -/
  ambient : FiniteGaloisSubextension ambientBase.field
  /-- A chosen degree-one Frobenius element in the ambient extension. -/
  frobenius :
    D.FrobeniusElements ambientBase ambient.field ambient.below
  /-- The chosen Frobenius has exponent one. -/
  exponent_one :
    D.frobeniusExponent ambientBase ambient.field ambient.below frobenius = 1
  /-- The positive exponent defining the first fixed field. -/
  n : ℕ
  /-- Positivity of the fixed-field exponent. -/
  n_pos : 0 < n
  /-- The fixed field of the `n`-th Frobenius power is finite over the distinguished base. -/
  baseAbsoluteFinite :
    let σ := D.frobeniusPowerOfDegreeOne ambientBase ambient.field
      ambient.below frobenius exponent_one n n_pos
    Finite
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G)
          (D.frobeniusFixedField ambientBase ambient.field ambient.below σ)
          (le_baseField
            (D.frobeniusFixedField ambientBase ambient.field ambient.below σ)))
  /-- The fixed field of the `n²`-th Frobenius power is finite over the distinguished base. -/
  fieldAbsoluteFinite :
    let σn := D.frobeniusPowerOfDegreeOne ambientBase ambient.field
      ambient.below frobenius exponent_one (n * n) (Nat.mul_pos n_pos n_pos)
    Finite
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G)
          (D.frobeniusFixedField ambientBase ambient.field ambient.below σn)
          (le_baseField
            (D.frobeniusFixedField ambientBase ambient.field ambient.below σn)))
  /-- The relative quotient between the `n`- and `n²`-power fixed fields is finite. -/
  relativeFinite :
    let σ := D.frobeniusPowerOfDegreeOne ambientBase ambient.field
      ambient.below frobenius exponent_one n n_pos
    let σn := D.frobeniusPowerOfDegreeOne ambientBase ambient.field
      ambient.below frobenius exponent_one (n * n) (Nat.mul_pos n_pos n_pos)
    let hTS := D.frobeniusPowerFixedField_le ambientBase ambient.field
      ambient.below frobenius exponent_one n n n_pos n_pos
    Finite
      ((D.frobeniusFixedField ambientBase ambient.field ambient.below σ).toSubgroup ⧸
        extensionSubgroup
          (D.frobeniusFixedField ambientBase ambient.field ambient.below σ)
          (D.frobeniusFixedField ambientBase ambient.field ambient.below σn)
          hTS)

namespace FrobeniusPowerFixedFieldTower

variable {D : DegreeData G} [IsTopologicalGroup G]

/-- Forget ambient finiteness while retaining its Galois structure. -/
noncomputable def ambientGalois (P : FrobeniusPowerFixedFieldTower D) :
    GaloisSubextension P.ambientBase.field :=
  P.ambient.toGaloisSubextension

/-- The Frobenius element `φⁿ` defining the lower fixed field. -/
def baseFrobenius (P : FrobeniusPowerFixedFieldTower D) :
    D.FrobeniusElements P.ambientBase P.ambient.field P.ambient.below :=
  D.frobeniusPowerOfDegreeOne P.ambientBase P.ambient.field P.ambient.below
    P.frobenius P.exponent_one P.n P.n_pos

/-- The Frobenius element `φⁿ²` defining the upper fixed field. -/
def fieldFrobenius (P : FrobeniusPowerFixedFieldTower D) :
    D.FrobeniusElements P.ambientBase P.ambient.field P.ambient.below :=
  D.frobeniusPowerOfDegreeOne P.ambientBase P.ambient.field P.ambient.below
    P.frobenius P.exponent_one (P.n * P.n)
      (Nat.mul_pos P.n_pos P.n_pos)

/-- The original Frobenius commutes with its `n`-th power. -/
theorem frobenius_commute_base (P : FrobeniusPowerFixedFieldTower D) :
    P.frobenius.1 * P.baseFrobenius.1 =
      P.baseFrobenius.1 * P.frobenius.1 := by
  simpa [baseFrobenius] using
    ((Commute.refl P.frobenius.1).pow_right P.n).eq

/-- The original Frobenius commutes with its `n²`-th power. -/
theorem frobenius_commute_field (P : FrobeniusPowerFixedFieldTower D) :
    P.frobenius.1 * P.fieldFrobenius.1 =
      P.fieldFrobenius.1 * P.frobenius.1 := by
  simpa [fieldFrobenius] using
    ((Commute.refl P.frobenius.1).pow_right (P.n * P.n)).eq

/-- Inclusion of the field fixed by `φⁿ²` into the field fixed by `φⁿ`. -/
theorem field_le_base (P : FrobeniusPowerFixedFieldTower D) :
    (D.frobeniusFixedField P.ambientBase P.ambient.field P.ambient.below
        P.fieldFrobenius).toSubgroup ≤
      (D.frobeniusFixedField P.ambientBase P.ambient.field P.ambient.below
        P.baseFrobenius).toSubgroup :=
  D.frobeniusPowerFixedField_le P.ambientBase P.ambient.field P.ambient.below
    P.frobenius P.exponent_one P.n P.n P.n_pos P.n_pos

/-- Relative finiteness in the fixed-field presentation used by the
Frobenius action and norm lemmas.  The witness is projected from the power
tower rather than requested again from callers. -/
instance relativeRepresentedQuotientFinite
    (P : FrobeniusPowerFixedFieldTower D) :
    Finite
      ((D.frobeniusFixedField P.ambientBase P.ambient.field P.ambient.below
          P.baseFrobenius).toSubgroup ⧸
        extensionSubgroup
          (D.frobeniusFixedField P.ambientBase P.ambient.field P.ambient.below
            P.baseFrobenius)
          (D.frobeniusFixedField P.ambientBase P.ambient.field P.ambient.below
            P.fieldFrobenius)
          P.field_le_base) :=
  P.relativeFinite

/-- Absolute finiteness of the lower fixed field in the presentation used by
the Frobenius action API. -/
instance baseRepresentedAbsoluteFinite
    (P : FrobeniusPowerFixedFieldTower D) :
    Finite
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G)
          (D.frobeniusFixedField P.ambientBase P.ambient.field P.ambient.below
            P.baseFrobenius)
          (le_baseField
            (D.frobeniusFixedField P.ambientBase P.ambient.field P.ambient.below
              P.baseFrobenius))) :=
  P.baseAbsoluteFinite

/-- Absolute finiteness of the upper fixed field in the presentation used by
the Frobenius action API. -/
instance fieldRepresentedAbsoluteFinite
    (P : FrobeniusPowerFixedFieldTower D) :
    Finite
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G)
          (D.frobeniusFixedField P.ambientBase P.ambient.field P.ambient.below
            P.fieldFrobenius)
          (le_baseField
            (D.frobeniusFixedField P.ambientBase P.ambient.field P.ambient.below
              P.fieldFrobenius))) :=
  P.fieldAbsoluteFinite

/-- The power construction as the canonical fixed-field tower bundle. -/
noncomputable def toFrobeniusFixedFieldTower
    (P : FrobeniusPowerFixedFieldTower D) [T2Space G] :
    FrobeniusFixedFieldTower D where
  ambientBase := P.ambientBase
  ambient := P.ambientGalois
  baseFrobenius := P.baseFrobenius
  fieldFrobenius := P.fieldFrobenius
  field_le_base := P.field_le_base
  finiteQuotient := P.relativeFinite
  baseAbsoluteFinite := P.baseAbsoluteFinite
  fieldAbsoluteFinite := P.fieldAbsoluteFinite
  normal :=
    D.frobeniusPowerFixedField_normal P.ambientBase P.ambient.field
      P.ambient.below P.frobenius P.exponent_one P.n P.n P.n_pos P.n_pos
  commute := by
    change P.baseFrobenius.1 * P.fieldFrobenius.1 =
      P.fieldFrobenius.1 * P.baseFrobenius.1
    simpa [baseFrobenius, fieldFrobenius] using
      ((Commute.refl P.frobenius.1).pow_pow P.n (P.n * P.n)).eq

/-- The power tower together with the already assumed finiteness of its
ambient extension. -/
noncomputable def toFiniteAmbientFrobeniusFixedFieldTower
    (P : FrobeniusPowerFixedFieldTower D) [T2Space G] :
    FiniteAmbientFrobeniusFixedFieldTower D where
  toFrobeniusFixedFieldTower := P.toFrobeniusFixedFieldTower
  ambientFinite := by
    change Finite P.ambient.toGaloisSubextension.extensionQuotient
    exact Finite.of_equiv P.ambient.extensionQuotient
      P.ambient.toGaloisExtensionQuotientMulEquiv

end FrobeniusPowerFixedFieldTower

end DegreeData

end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_FiniteFieldUnitMaps
attribute [-instance] _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.chosenUnramifiedFrobeniusLift_exponent _root_.ClassFormation.DegreeData.frobeniusQuotientRepresentation_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.ValuationData.canonicalUnramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.canonicalValueQuotientHom_mk _root_.ClassFormation.ValuationData.canonicalValueReduction_one _root_.ClassFormation.ValuationData.unramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.mem_normFilterBasis_iff _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

universe u v

namespace ClassFormation

open KummerTheory
open CyclicCohomology

/-!
# Finite-field unit maps

This module proves valuation invariance on Frobenius fixed fields and
constructs the induced actions, inclusions, and relative norms on the
corresponding finite unit groups.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace FiniteAbstractField

/-- Normality transports across the canonical residue-field enrichment. -/
instance toFiniteResidueAbstractField_extensionNormal
    (K : FiniteAbstractField G) (D : DegreeData G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (extensionSubgroup K.field L hLK).Normal] :
    (extensionSubgroup (K.toFiniteResidueAbstractField D).field L hLK).Normal := by
  change (extensionSubgroup K.field L hLK).Normal
  exact hnormal

/-- Relative finiteness transports across the canonical residue-field enrichment. -/
instance toFiniteResidueAbstractField_extensionFinite
    (K : FiniteAbstractField G) (D : DegreeData G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)] :
    Finite ((K.toFiniteResidueAbstractField D).field.toSubgroup ⧸
      extensionSubgroup (K.toFiniteResidueAbstractField D).field L hLK) := by
  change Finite
    (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)
  exact hfinite

end FiniteAbstractField

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

/-- Units stay units after inclusion into any finite extension.  The construction
uses this silently when all finitely many terms of `(*)` are placed in one
finite Galois field. -/
theorem fixedFieldInclusion_mem_unitAddSubgroup
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (u : v.unitAddSubgroup E.base) :
    fixedFieldInclusion A E.base.field E.field.field E.below u.1 ∈
      v.unitAddSubgroup E.field := by
  rw [v.mem_unitAddSubgroup_iff]
  apply Subtype.ext
  let ER := E.toFiniteResidueAbstractExtension D
  apply zHatMulNat_injective ER.residueDegree.property
  change (ER.residueDegree : ℕ) •
      ((v.valuationAt E.field
        (fixedFieldInclusion A E.base.field E.field.field E.below u.1) :
        v.valueGroup) : ZHat) =
    (ER.residueDegree : ℕ) • ((0 : v.valueGroup) : ZHat)
  have htower :=
    v.normalizedValuation_tower E
      (fixedFieldInclusion A E.base.field E.field.field E.below u.1)
  have htower' :
      (ER.residueDegree : ℕ) •
          ((v.valuationAt E.field
            (fixedFieldInclusion A E.base.field E.field.field E.below u.1) :
            v.valueGroup) : ZHat) =
        ((v.valuationAt E.base
          (relativeNorm A E.base.field E.field.field E.below
            (fixedFieldInclusion A E.base.field E.field.field E.below u.1)) :
              v.valueGroup) : ZHat) := by
    simpa [ER] using htower
  rw [htower']
  rw [show relativeNorm A E.base.field E.field.field E.below
      (fixedFieldInclusion A E.base.field E.field.field E.below u.1) =
        (E.degree : ℕ) • u.1 by
    exact relativeNorm_fixedFieldInclusion A E.toFiniteAbstractExtension u.1]
  rw [map_nsmul]
  have hu : v.valuationAt E.base u.1 = 0 := u.2
  simp [hu]

/-- Inclusion of units along an arbitrary finite extension. -/
def finiteUnitInclusion
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G) :
    v.unitAddSubgroup E.base →+ v.unitAddSubgroup E.field where
  toFun u := ⟨fixedFieldInclusion A E.base.field E.field.field E.below u.1,
    v.fixedFieldInclusion_mem_unitAddSubgroup E u⟩
  map_zero' := by apply Subtype.ext; rfl
  map_add' _ _ := by apply Subtype.ext; rfl

/-- Transporting a finite-unit inclusion along equality of its target field
does not change its ambient coefficient. -/
theorem finiteUnitInclusion_transport_coe
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (F : FiniteAbstractField G) (h : E.field = F)
    (u : v.unitAddSubgroup E.base) :
    (((h ▸ v.finiteUnitInclusion E u : v.unitAddSubgroup F).1 :
        ambientFixedAddSubgroup A F.field) : A.V) = u.1.1 := by
  cases h
  rfl

end ValuationData
end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_InfiniteUnitDescent
attribute [-instance] _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.chosenUnramifiedFrobeniusLift_exponent _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.ValuationData.canonicalUnramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.canonicalValueQuotientHom_mk _root_.ClassFormation.ValuationData.canonicalValueReduction_one _root_.ClassFormation.ValuationData.unramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.mem_normFilterBasis_iff _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

universe u v

namespace ClassFormation

open KummerTheory
open CyclicCohomology

/-!
# Infinite-level unit descent

This module bundles finite intermediate fields over a finite base, defines
the infinite unit subgroup, proves its action and norm stability, and
descends maximal-unramified norm equations from finite support.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace FiniteIntermediateField

/-- The canonical finite-field extension bundle carried by a finite
intermediate field over a bundled finite base. -/
noncomputable def toFiniteAbstractFieldExtension
    {E : ClosedSubgroup G} (K : FiniteAbstractField G)
    (M : FiniteIntermediateField E K.field) :
    FiniteAbstractFieldExtension G := by
  letI : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field M.field M.below) :=
    M.finite
  exact FiniteAbstractFieldExtension.ofInclusion M.field K M.below

/-- The upper endpoint of the canonical finite-field extension bundle. -/
noncomputable def toFiniteAbstractField
    {E : ClosedSubgroup G} (K : FiniteAbstractField G)
    (M : FiniteIntermediateField E K.field) : FiniteAbstractField G :=
  (M.toFiniteAbstractFieldExtension K).field

end FiniteIntermediateField

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

/-- Unit-valued strengthening of finite-support descent.  If the chosen
finite support is a unit, the descended K-rational element is a unit as
well. -/
theorem descend_maximalUnramified_fixed_unit_of_finiteSupport
    (v : ValuationData D A) [IsTopologicalGroup G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK)
    (hφ : D.frobeniusExponent
      (K.toFiniteResidueAbstractField D) L hLK φ = 1)
    (P : FiniteIntermediateField (D.maximalUnramifiedField L) K.field)
    [hPnormal : (extensionSubgroup K.field P.field P.below).Normal]
    (aI : ambientFixedAddSubgroup A (D.maximalUnramifiedField K.field))
    (aP : v.unitAddSubgroup (P.toFiniteAbstractField K))
    (hsupport :
      fixedFieldInclusion A P.field (D.maximalUnramifiedField L) P.above aP.1 =
        fixedFieldInclusion A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) aI)
    (hfixed :
      D.frobeniusQuotientAction A K.field L hLK φ.1
          (fixedFieldInclusion A (D.maximalUnramifiedField K.field)
            (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) aI) =
        fixedFieldInclusion A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) aI) :
    ∃ aK : v.unitAddSubgroup K,
      fixedFieldInclusion A K.field (D.maximalUnramifiedField K.field)
        (D.maximalUnramifiedField_le K.field) aK.1 = aI := by
  obtain ⟨bK, hbK⟩ :=
    D.descend_maximalUnramified_fixed_of_finiteSupport
      A (K.toFiniteResidueAbstractField D) L hLK φ hφ
        P aI aP.1 hsupport hfixed
  let : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field P.field P.below) :=
    P.finite
  let EP := P.toFiniteAbstractFieldExtension K
  have hKP :
      fixedFieldInclusion A K.field P.field P.below bK = aP.1 := by
    apply Subtype.ext
    have hsupportVal := congrArg
      (fun z : ambientFixedAddSubgroup A (D.maximalUnramifiedField L) => z.1)
      hsupport
    have hbKVal := congrArg
      (fun z : ambientFixedAddSubgroup A (D.maximalUnramifiedField K.field) => z.1)
      hbK
    exact hbKVal.trans hsupportVal.symm
  have htower := v.normalizedValuation_tower EP
    (fixedFieldInclusion A K.field P.field P.below bK)
  have hvalP :
      v.valuationAt EP.field
        (fixedFieldInclusion A K.field P.field P.below bK) = 0 := by
    rw [hKP]
    exact aP.2
  have hmul :
      (EP.degree : ℕ) •
        ((v.valuationAt K bK : v.valueGroup) : ZHat) = 0 := by
    let ER := EP.toFiniteResidueAbstractExtension D
    change (ER.residueDegree : ℕ) •
        ((v.valuationAt EP.field
          (fixedFieldInclusion A K.field P.field P.below bK) :
            v.valueGroup) : ZHat) =
      ((v.valuationAt K
        (relativeNorm A K.field P.field P.below
          (fixedFieldInclusion A K.field P.field P.below bK)) :
            v.valueGroup) : ZHat) at htower
    rw [hvalP] at htower
    rw [show relativeNorm A K.field P.field P.below
        (fixedFieldInclusion A K.field P.field P.below bK) =
          (EP.degree : ℕ) • bK by
      exact relativeNorm_fixedFieldInclusion A EP.toFiniteAbstractExtension bK,
      map_nsmul] at htower
    simpa using htower.symm
  have hbKunit : bK ∈ v.unitAddSubgroup K := by
    rw [v.mem_unitAddSubgroup_iff]
    apply Subtype.ext
    apply zHatMulNat_injective EP.degree.property
    change (EP.degree : ℕ) •
        ((v.valuationAt K bK : v.valueGroup) : ZHat) =
      (EP.degree : ℕ) • ((0 : v.valueGroup) : ZHat)
    simpa using hmul
  exact ⟨⟨bK, hbKunit⟩, hbK⟩

/-- An element of an infinite algebraic extension is a unit when it is
already a unit at some finite intermediate stage.  This is the literal
finite-support meaning of `U_E = \bigcup_M U_M` used. -/
def IsFiniteStageUnit
    (v : ValuationData D A) (E : ClosedSubgroup G)
    (K : FiniteAbstractField G)
    (a : ambientFixedAddSubgroup A E) : Prop :=
  ∃ M : FiniteIntermediateField E K.field,
    ∃ u : v.unitAddSubgroup (M.toFiniteAbstractField K),
      fixedFieldInclusion A M.field E M.above u.1 = a

/-- The actual finite-stage unit group `U_E` inside `A_E`. -/
noncomputable def infiniteUnitAddSubgroup
    (v : ValuationData D A) (E : ClosedSubgroup G)
    (K : FiniteAbstractField G)
    (hEK : E.toSubgroup ≤ K.field.toSubgroup) :
    AddSubgroup (ambientFixedAddSubgroup A E) where
  carrier := {a | v.IsFiniteStageUnit E K a}
  zero_mem' := by
    let M := FiniteIntermediateField.base E K.field hEK
    refine ⟨M, 0, ?_⟩
    rfl
  add_mem' := by
    intro a b ha hb
    rcases ha with ⟨M, u, hu⟩
    rcases hb with ⟨N, w, hw⟩
    let P := M.compositum N
    let hPfinite : Finite
        (K.field.toSubgroup ⧸ extensionSubgroup K.field P.field P.below) :=
      P.finite
    let hPM : P.field.toSubgroup ≤ M.field.toSubgroup := M.compositum_le_left N
    let hPN : P.field.toSubgroup ≤ N.field.toSubgroup := M.compositum_le_right N
    let hPMfinite : Finite
        (M.field.toSubgroup ⧸ extensionSubgroup M.field P.field hPM) :=
      FiniteIntermediateField.finite_extension_of_le
        P.below M.below hPM
    let hPNfinite : Finite
        (N.field.toSubgroup ⧸ extensionSubgroup N.field P.field hPN) :=
      FiniteIntermediateField.finite_extension_of_le
        P.below N.below hPN
    let : Finite
        ((M.toFiniteAbstractField K).field.toSubgroup ⧸
          extensionSubgroup (M.toFiniteAbstractField K).field P.field hPM) := by
      change Finite
        (M.field.toSubgroup ⧸ extensionSubgroup M.field P.field hPM)
      exact hPMfinite
    let : Finite
        ((N.toFiniteAbstractField K).field.toSubgroup ⧸
          extensionSubgroup (N.toFiniteAbstractField K).field P.field hPN) := by
      change Finite
        (N.field.toSubgroup ⧸ extensionSubgroup N.field P.field hPN)
      exact hPNfinite
    let EMP : FiniteAbstractFieldExtension G :=
      FiniteAbstractFieldExtension.ofInclusion
        P.field (M.toFiniteAbstractField K) hPM
    let ENP : FiniteAbstractFieldExtension G :=
      FiniteAbstractFieldExtension.ofInclusion
        P.field (N.toFiniteAbstractField K) hPN
    let hEMPfield : EMP.field = P.toFiniteAbstractField K :=
      FiniteAbstractField.eq_of_field_eq _ _ rfl
    let hENPfield : ENP.field = P.toFiniteAbstractField K :=
      FiniteAbstractField.eq_of_field_eq _ _ rfl
    let uP : v.unitAddSubgroup (P.toFiniteAbstractField K) :=
      hEMPfield ▸ v.finiteUnitInclusion EMP u
    let wP : v.unitAddSubgroup (P.toFiniteAbstractField K) :=
      hENPfield ▸ v.finiteUnitInclusion ENP w
    refine ⟨P, uP + wP, ?_⟩
    apply Subtype.ext
    have huval : u.1.1 = a.1 :=
      congrArg (fun x : ambientFixedAddSubgroup A E => x.1) hu
    have hwval : w.1.1 = b.1 :=
      congrArg (fun x : ambientFixedAddSubgroup A E => x.1) hw
    change uP.1.1 + wP.1.1 = a.1 + b.1
    have huP : uP.1.1 = u.1.1 :=
      v.finiteUnitInclusion_transport_coe EMP
        (P.toFiniteAbstractField K) hEMPfield u
    have hwP : wP.1.1 = w.1.1 :=
      v.finiteUnitInclusion_transport_coe ENP
        (P.toFiniteAbstractField K) hENPfield w
    rw [huP, hwP, huval, hwval]
  neg_mem' := by
    intro a ha
    rcases ha with ⟨M, u, hu⟩
    refine ⟨M, -u, ?_⟩
    apply Subtype.ext
    exact congrArg Neg.neg (congrArg Subtype.val hu)

/--
Characterizes `a ∈ v.infiniteUnitAddSubgroup E K hEK` by the equivalent condition
`v.IsFiniteStageUnit E K a`.
-/
@[simp]
theorem mem_infiniteUnitAddSubgroup_iff
    (v : ValuationData D A) (E : ClosedSubgroup G)
    (K : FiniteAbstractField G)
    (hEK : E.toSubgroup ≤ K.field.toSubgroup)
    (a : ambientFixedAddSubgroup A E) :
    a ∈ v.infiniteUnitAddSubgroup E K hEK ↔
      v.IsFiniteStageUnit E K a :=
  Iff.rfl

/-- The actual `G(\widetilde L/K)`-action preserves the finite-stage unit
group `U_{\widetilde L}`.  A unit is first moved to a finite Galois
refinement of its support; that refinement is stable under the chosen
representative, so the translated element still has finite unit support. -/
theorem frobeniusQuotientAction_mem_infiniteUnitAddSubgroup
    (v : ValuationData D A) [IsTopologicalGroup G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L))
    (ha : a ∈ v.infiniteUnitAddSubgroup (D.maximalUnramifiedField L) K
      (D.maximalUnramifiedField_le_of_le hLK)) :
    D.frobeniusQuotientAction A K.field L hLK q a ∈
      v.infiniteUnitAddSubgroup (D.maximalUnramifiedField L) K
        (D.maximalUnramifiedField_le_of_le hLK) := by
  let E := D.maximalUnramifiedField L
  let hEK := D.maximalUnramifiedField_le_of_le hLK
  let hEnormal : (extensionSubgroup K.field E hEK).Normal :=
    D.extensionSubgroup_maximalUnramifiedField_normal K.field L hLK
  rcases ha with ⟨M, u, hu⟩
  let R := M.galoisRefinement
  have hRM : R.field.toSubgroup ≤ M.field.toSubgroup :=
    M.galoisRefinement_le_field
  let hRfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field R.field R.below) :=
    R.finite
  let hRMfinite : Finite
      (M.field.toSubgroup ⧸ extensionSubgroup M.field R.field hRM) :=
    FiniteIntermediateField.finite_extension_of_le R.below M.below hRM
  let : Finite
      ((M.toFiniteAbstractField K).field.toSubgroup ⧸
        extensionSubgroup (M.toFiniteAbstractField K).field R.field hRM) := by
    change Finite
      (M.field.toSubgroup ⧸ extensionSubgroup M.field R.field hRM)
    exact hRMfinite
  let k : K.field.toSubgroup := Quotient.out q
  have hkq :
      (QuotientGroup.mk k :
        K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) = q :=
    Quotient.out_eq' q
  let EMR : FiniteAbstractFieldExtension G :=
    FiniteAbstractFieldExtension.ofInclusion
      R.field (M.toFiniteAbstractField K) hRM
  let ER := R.toFiniteAbstractFieldExtension K
  let hEMRfield : EMR.field = R.toFiniteAbstractField K :=
    FiniteAbstractField.eq_of_field_eq _ _ rfl
  let uR : v.unitAddSubgroup (R.toFiniteAbstractField K) :=
    hEMRfield ▸ v.finiteUnitInclusion EMR u
  let uR' : v.unitAddSubgroup (R.toFiniteAbstractField K) :=
    v.unitActionLinearMap ER
      (inferInstance : (extensionSubgroup K.field R.field R.below).Normal) k uR
  refine ⟨R, uR', ?_⟩
  rw [← hkq]
  apply Subtype.ext
  have huval : u.1.1 = a.1 :=
    congrArg (fun z : ambientFixedAddSubgroup A E => z.1) hu
  change A.ρ k.1 uR.1.1 = A.ρ k.1 a.1
  have huR : uR.1.1 = u.1.1 :=
    v.finiteUnitInclusion_transport_coe EMR
      (R.toFiniteAbstractField K) hEMRfield u
  rw [huR, huval]

/-- The Frobenius power sum used preserves the finite-stage unit
group of the maximal unramified extension. -/
theorem frobeniusPowerSum_mem_infiniteUnit_universalNormDescent
    (v : ValuationData D A) [IsTopologicalGroup G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (n : ℕ)
    (x : ambientFixedAddSubgroup A (D.maximalUnramifiedField L))
    (hx : x ∈ v.infiniteUnitAddSubgroup
      (D.maximalUnramifiedField L) K
      (D.maximalUnramifiedField_le_of_le hLK)) :
    D.frobeniusPowerSum A K.field L hLK φ n x ∈
      v.infiniteUnitAddSubgroup (D.maximalUnramifiedField L) K
        (D.maximalUnramifiedField_le_of_le hLK) := by
  unfold DegreeData.frobeniusPowerSum
  apply AddSubgroup.sum_mem
  intro i _
  exact v.frobeniusQuotientAction_mem_infiniteUnitAddSubgroup
    K L hLK (φ ^ i.1) x hx

/-- The relative norm from `\widetilde L` to `\widetilde K`, included back
in `A_{\widetilde L}`, preserves finite-stage units. -/
theorem maximalUnramifiedNorm_mem_infiniteUnitAddSubgroup
    (v : ValuationData D A) [IsTopologicalGroup G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L))
    (ha : a ∈ v.infiniteUnitAddSubgroup
      (D.maximalUnramifiedField L) K
      (D.maximalUnramifiedField_le_of_le hLK)) :
    letI : Finite
        ((D.maximalUnramifiedField K.field).toSubgroup ⧸
          extensionSubgroup (D.maximalUnramifiedField K.field)
            (D.maximalUnramifiedField L)
            (D.maximalUnramifiedField_mono hLK)) :=
      D.maximalUnramifiedExtension_finite K.field L hLK
    fixedFieldInclusion A (D.maximalUnramifiedField K.field)
        (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
        (relativeNorm A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) a)
      ∈ v.infiniteUnitAddSubgroup (D.maximalUnramifiedField L) K
        (D.maximalUnramifiedField_le_of_le hLK) := by
  let : Finite
      ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) :=
    D.maximalUnramifiedExtension_finite K.field L hLK
  let I := D.maximalUnramifiedField K.field
  let E := D.maximalUnramifiedField L
  let hEI := D.maximalUnramifiedField_mono hLK
  let N := relativeNorm A I E hEI
  let : Fintype (I.toSubgroup ⧸ extensionSubgroup I E hEI) :=
    Fintype.ofFinite _
  let qK (q : I.toSubgroup ⧸ extensionSubgroup I E hEI) :
      K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK :=
    let r : I.toSubgroup := Quotient.out q
    let k : K.field.toSubgroup :=
      ⟨r.1, (D.maximalUnramifiedField_le K.field) r.2⟩
    QuotientGroup.mk k
  let f (q : I.toSubgroup ⧸ extensionSubgroup I E hEI) :
      ambientFixedAddSubgroup A E :=
    D.frobeniusQuotientAction A K.field L hLK (qK q) a
  have hterm (q : I.toSubgroup ⧸ extensionSubgroup I E hEI) :
      f q ∈ v.infiniteUnitAddSubgroup E K
        (D.maximalUnramifiedField_le_of_le hLK) := by
    exact
      v.frobeniusQuotientAction_mem_infiniteUnitAddSubgroup
        K L hLK (qK q) a ha
  have hsum :
      ∑ q : I.toSubgroup ⧸ extensionSubgroup I E hEI, f q ∈
        v.infiniteUnitAddSubgroup E K
          (D.maximalUnramifiedField_le_of_le hLK) :=
    AddSubgroup.sum_mem _ (fun q _ => hterm q)
  have heq :
      fixedFieldInclusion A I E hEI (N a) =
        ∑ q : I.toSubgroup ⧸ extensionSubgroup I E hEI, f q := by
    apply Subtype.ext
    rw [fixedFieldInclusion_coe, relativeNorm_apply_coe]
    rw [relativeNormValue]
    change
      ∑ q : I.toSubgroup ⧸ extensionSubgroup I E hEI,
          relativeCosetAction A I E hEI a q =
        (AddSubgroup.subtype (ambientFixedAddSubgroup A E))
          (∑ q : I.toSubgroup ⧸ extensionSubgroup I E hEI, f q)
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro q _
    let r : I.toSubgroup := Quotient.out q
    have hrq : (QuotientGroup.mk r :
        I.toSubgroup ⧸ extensionSubgroup I E hEI) = q :=
      Quotient.out_eq' q
    change relativeCosetAction A I E hEI a q = (f q).1
    calc
      relativeCosetAction A I E hEI a q =
          relativeCosetAction A I E hEI a (QuotientGroup.mk r) :=
        congrArg (relativeCosetAction A I E hEI a) hrq.symm
      _ = A.ρ r.1 a.1 := relativeCosetAction_mk A I E hEI a r
      _ = (f q).1 := by rfl
  rw [heq]
  exact hsum

/-- A maximal-unramified norm of a finite-stage unit descends to a genuine
unit of `K` once it is fixed by a degree-one Frobenius lift. -/
theorem descend_maximalUnramifiedNorm_unit
    (v : ValuationData D A) [IsTopologicalGroup G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (φ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK)
    (hφ : D.frobeniusExponent
      (K.toFiniteResidueAbstractField D) L hLK φ = 1)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L))
    (ha : a ∈ v.infiniteUnitAddSubgroup (D.maximalUnramifiedField L) K
      (D.maximalUnramifiedField_le_of_le hLK))
    (hfixed :
      letI : Finite
          ((D.maximalUnramifiedField K.field).toSubgroup ⧸
            extensionSubgroup (D.maximalUnramifiedField K.field)
              (D.maximalUnramifiedField L)
              (D.maximalUnramifiedField_mono hLK)) :=
        D.maximalUnramifiedExtension_finite K.field L hLK
      let N := relativeNorm A (D.maximalUnramifiedField K.field)
        (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
      let J := fixedFieldInclusion A (D.maximalUnramifiedField K.field)
        (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
      D.frobeniusQuotientAction A K.field L hLK φ.1 (J (N a)) = J (N a)) :
    letI : Finite
        ((D.maximalUnramifiedField K.field).toSubgroup ⧸
          extensionSubgroup (D.maximalUnramifiedField K.field)
            (D.maximalUnramifiedField L)
            (D.maximalUnramifiedField_mono hLK)) :=
      D.maximalUnramifiedExtension_finite K.field L hLK
    ∃ aK : v.unitAddSubgroup K,
      fixedFieldInclusion A K.field (D.maximalUnramifiedField K.field)
        (D.maximalUnramifiedField_le K.field) aK.1 =
        relativeNorm A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) a := by
  let : Finite
      ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) :=
    D.maximalUnramifiedExtension_finite K.field L hLK
  let I := D.maximalUnramifiedField K.field
  let E := D.maximalUnramifiedField L
  let hEI := D.maximalUnramifiedField_mono hLK
  let N := relativeNorm A I E hEI
  let J := fixedFieldInclusion A I E hEI
  let hEnormal : (extensionSubgroup K.field E
      (D.maximalUnramifiedField_le_of_le hLK)).Normal :=
    D.extensionSubgroup_maximalUnramifiedField_normal K.field L hLK
  have hmem : J (N a) ∈ v.infiniteUnitAddSubgroup E K
      (D.maximalUnramifiedField_le_of_le hLK) :=
    v.maximalUnramifiedNorm_mem_infiniteUnitAddSubgroup K L hLK a ha
  rcases hmem with ⟨Q, aQ, haQ⟩
  let R := Q.galoisRefinement
  let hRQ : R.field.toSubgroup ≤ Q.field.toSubgroup :=
    Q.galoisRefinement_le_field
  let hQabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) Q.field (le_baseField Q.field)) :=
    Q.absoluteFinite
  let hRfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field R.field R.below) :=
    R.finite
  let hRQfinite : Finite
      (Q.field.toSubgroup ⧸ extensionSubgroup Q.field R.field hRQ) :=
    FiniteIntermediateField.finite_extension_of_le R.below Q.below hRQ
  let : Finite
      ((Q.toFiniteAbstractField K).field.toSubgroup ⧸
        extensionSubgroup (Q.toFiniteAbstractField K).field R.field hRQ) := by
    change Finite
      (Q.field.toSubgroup ⧸ extensionSubgroup Q.field R.field hRQ)
    exact hRQfinite
  let hRnormal : (extensionSubgroup K.field R.field R.below).Normal :=
    FiniteIntermediateField.galoisRefinement_normal Q
  let EQR : FiniteAbstractFieldExtension G :=
    FiniteAbstractFieldExtension.ofInclusion
      R.field (Q.toFiniteAbstractField K) hRQ
  let hEQRfield : EQR.field = R.toFiniteAbstractField K :=
    FiniteAbstractField.eq_of_field_eq _ _ rfl
  let aR : v.unitAddSubgroup (R.toFiniteAbstractField K) :=
    hEQRfield ▸ v.finiteUnitInclusion EQR aQ
  have haR : fixedFieldInclusion A R.field E R.above aR.1 = J (N a) := by
    apply Subtype.ext
    change aR.1.1 = (J (N a)).1
    have haRcoe : aR.1.1 = aQ.1.1 :=
      v.finiteUnitInclusion_transport_coe EQR
        (R.toFiniteAbstractField K) hEQRfield aQ
    rw [haRcoe]
    exact congrArg Subtype.val haQ
  exact v.descend_maximalUnramified_fixed_unit_of_finiteSupport
    K L hLK φ hφ R (N a) aR haR hfixed

end ValuationData
end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_InfiniteUnitNormSubgroup
attribute [-instance] _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.chosenUnramifiedFrobeniusLift_exponent _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.ValuationData.canonicalUnramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.canonicalValueQuotientHom_mk _root_.ClassFormation.ValuationData.canonicalValueReduction_one _root_.ClassFormation.ValuationData.unramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.mem_normFilterBasis_iff _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

universe u

namespace ClassFormation

open KummerTheory
open CyclicCohomology

/-!
# Infinite unit norm subgroups

This module defines the finite-level and infinite unit norm ranges, proves
their tower compatibility, and compares them with the ambient norm
subgroups.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

/-- The image `N_{M/K} U_M` from one finite intermediate field. -/
def finiteIntermediateUnitNormRange
    (v : ValuationData D A) (E : ClosedSubgroup G)
    (K : FiniteAbstractField G)
    (M : FiniteIntermediateField E K.field) :
    AddSubgroup (ambientFixedAddSubgroup A K.field) := by
  letI : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field M.field M.below) :=
    M.finite
  exact ((relativeNorm A K.field M.field M.below).comp
    (v.unitAddSubgroup (M.toFiniteAbstractField K)).subtype).range

/-- The universal unit norm group
`N_{E/K} U_E = ⋂_M N_{M/K} U_M`. -/
def infiniteUnitNormSubgroup
    (v : ValuationData D A) (E : ClosedSubgroup G)
    (K : FiniteAbstractField G) :
    AddSubgroup (ambientFixedAddSubgroup A K.field) :=
  ⨅ M : FiniteIntermediateField E K.field,
    v.finiteIntermediateUnitNormRange E K M

/--
Characterizes `a ∈ v.infiniteUnitNormSubgroup E K` by the equivalent condition `∀ M :
FiniteIntermediateField E K.field, a ∈ v.finiteIntermediateUnitNormRange E K M`.
-/
@[simp]
theorem mem_infiniteUnitNormSubgroup_iff
    (v : ValuationData D A) (E : ClosedSubgroup G)
    (K : FiniteAbstractField G)
    (a : ambientFixedAddSubgroup A K.field) :
    a ∈ v.infiniteUnitNormSubgroup E K ↔
      ∀ M : FiniteIntermediateField E K.field,
        a ∈ v.finiteIntermediateUnitNormRange E K M := by
  simp [infiniteUnitNormSubgroup]

/--
Proves the bound `v.finiteIntermediateUnitNormRange E K M ≤ finiteIntermediateNormRange A E
K.field M`.
-/
theorem finiteIntermediateUnitNormRange_le_normRange
    (v : ValuationData D A) (E : ClosedSubgroup G)
    (K : FiniteAbstractField G)
    (M : FiniteIntermediateField E K.field) :
    v.finiteIntermediateUnitNormRange E K M ≤
      finiteIntermediateNormRange A E K.field M := by
  let hMfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field M.field M.below) :=
    M.finite
  change
    ((relativeNorm A K.field M.field M.below).comp
      (v.unitAddSubgroup (M.toFiniteAbstractField K)).subtype).range ≤
        (relativeNorm A K.field M.field M.below).range
  rintro a ⟨u, hu⟩
  refine ⟨u.1, ?_⟩
  change relativeNorm A K.field M.field M.below u.1 = a at hu
  exact hu

/-- Proves the bound `v.infiniteUnitNormSubgroup E K ≤ infiniteNormSubgroup A E K.field`. -/
theorem infiniteUnitNormSubgroup_le_normSubgroup
    (v : ValuationData D A) (E : ClosedSubgroup G)
    (K : FiniteAbstractField G) :
    v.infiniteUnitNormSubgroup E K ≤ infiniteNormSubgroup A E K.field := by
  intro a ha
  rw [mem_infiniteNormSubgroup_iff]
  intro M
  exact v.finiteIntermediateUnitNormRange_le_normRange E K M
    ((v.mem_infiniteUnitNormSubgroup_iff E K a).1 ha M)

end ValuationData
end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_ChosenDegreeOneFrobenius
attribute [-instance] _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.chosenUnramifiedFrobeniusLift_exponent _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.ValuationData.canonicalUnramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.canonicalValueQuotientHom_mk _root_.ClassFormation.ValuationData.canonicalValueReduction_one _root_.ClassFormation.ValuationData.unramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

universe u

namespace ClassFormation

open CyclicCohomology

/-!
# The chosen degree-one Frobenius element

Surjectivity of the normalized degree supplies a Frobenius-semigroup element
of exponent one.  The chosen object and its specification are kept together
here so the multiplicativity proof can consume a named choice boundary.
-/

noncomputable section

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- A chosen degree-one element of `G(\widetilde L/K)`, packaged as an
element of the Frobenius semigroup. -/
noncomputable def chosenDegreeOneFrobeniusElement (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal] :
    D.FrobeniusElements K L hLK := by
  let hsurj := D.extensionNormalizedDegreeContinuous_surjective K L hLK
    (Multiplicative.ofAdd (1 : ZHat))
  refine ⟨Classical.choose hsurj, 1, Nat.one_pos, ?_⟩
  rw [pow_one, ← D.extensionNormalizedDegreeContinuous_apply]
  exact Classical.choose_spec hsurj

/--
Establishes the identity `D.frobeniusExponent K L hLK (D.chosenDegreeOneFrobeniusElement K L hLK)
= 1`.
-/
@[simp]
theorem frobeniusExponent_chosenDegreeOneFrobeniusElement (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal] :
    D.frobeniusExponent K L hLK
        (D.chosenDegreeOneFrobeniusElement K L hLK) = 1 := by
  apply proCIntegerOne_pow_nat_injective
  calc
    (Multiplicative.ofAdd (1 : ZHat)) ^
        D.frobeniusExponent K L hLK
          (D.chosenDegreeOneFrobeniusElement K L hLK) =
      D.extensionNormalizedDegree K L hLK
        (D.chosenDegreeOneFrobeniusElement K L hLK).1 :=
      (D.extensionNormalizedDegree_frobenius_eq_pow K L hLK
        (D.chosenDegreeOneFrobeniusElement K L hLK)).symm
    _ = Multiplicative.ofAdd (1 : ZHat) := by
      rw [← D.extensionNormalizedDegreeContinuous_apply]
      change D.extensionNormalizedDegreeContinuous K L hLK
        (Classical.choose
          (D.extensionNormalizedDegreeContinuous_surjective K L hLK
            (Multiplicative.ofAdd (1 : ZHat)))) =
          Multiplicative.ofAdd (1 : ZHat)
      exact Classical.choose_spec
        (D.extensionNormalizedDegreeContinuous_surjective K L hLK
          (Multiplicative.ofAdd (1 : ZHat)))
    _ = (Multiplicative.ofAdd (1 : ZHat)) ^ (1 : ℕ) := by simp

end DegreeData

end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_FrobeniusDescent
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientQuotientFinite _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientRepresentedQuotientFinite _root_.ClassFormation.DegreeData.FiniteTower.totalQuotientFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.baseAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.fieldAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.baseRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.fieldRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.relativeRepresentedQuotientFinite _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientAddCommGroup _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.ClassFormation.finiteNormQuotientAddCommGroup _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.chosenUnramifiedFrobeniusLift_exponent _root_.ClassFormation.DegreeData.frobeniusExponent_chosenDegreeOneFrobeniusElement _root_.ClassFormation.DegreeData.frobeniusExponent_powerOfDegreeOne _root_.ClassFormation.DegreeData.frobeniusFixedFieldAction_coe _root_.ClassFormation.DegreeData.frobeniusPowerOfDegreeOne_coe _root_.ClassFormation.DegreeData.frobeniusPowerSum_coe _root_.ClassFormation.DegreeData.frobeniusQuotientAction_mk _root_.ClassFormation.DegreeData.frobeniusQuotientRepresentation_apply _root_.ClassFormation.DegreeData.maximalUnramifiedNormClass_eq_zero_iff _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientInfiniteEquiv_maximalUnramifiedNormClass _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientLift_maximalUnramifiedNormClass _root_.ClassFormation.DegreeData.maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClass _root_.ClassFormation.DegreeData.mem_maximalUnramifiedField_iff _root_.ClassFormation.DegreeData.mem_maximalUnramifiedNormSubgroup_iff _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteAbstractField.normToBase_index_eq_degree _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_eq_one_iff _root_.ClassFormation.FiniteGaloisSubextension.toGaloisSubextension_isTotallyRamified_iff _root_.ClassFormation.FiniteGaloisSubextension.toGaloisSubextension_isUnramified_iff _root_.ClassFormation.ValuationData.canonicalUnramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.canonicalValueQuotientHom_mk _root_.ClassFormation.ValuationData.canonicalValueReduction_one _root_.ClassFormation.ValuationData.mem_infiniteUnitAddSubgroup_iff _root_.ClassFormation.ValuationData.mem_infiniteUnitNormSubgroup_iff _root_.ClassFormation.ValuationData.mem_unitAddSubgroup_iff _root_.ClassFormation.ValuationData.oneValue_coe _root_.ClassFormation.ValuationData.unitRepresentation_quotient_mk_apply _root_.ClassFormation.ValuationData.unramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.valuationAt_chosenPrimeElement _root_.ClassFormation.ValuationData.valuationAt_coe _root_.ClassFormation.ValuationData.valueModulo_apply _root_.ClassFormation.absoluteConjugateCosetEquiv_mk _root_.ClassFormation.canonicalValueQuotientMap_mk _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.finiteNormClass_add _root_.ClassFormation.finiteNormClass_eq_zero_iff _root_.ClassFormation.finiteNormClass_nsmul _root_.ClassFormation.finiteNormClass_sub _root_.ClassFormation.finiteNormClass_zero _root_.ClassFormation.finiteNormQuotientConcreteEquiv_finiteNormClass _root_.ClassFormation.finiteNormQuotientLift_finiteNormClass _root_.ClassFormation.finiteReciprocityNaturalityConjugation_mk _root_.ClassFormation.mem_nsmulImage_iff _root_.ClassFormation.normalExtensionAction_coe _root_.ClassFormation.nsmulImage_top _root_.ClassFormation.relativeConjugateCosetEquiv_mk _root_.ClassFormation.relativeCosetAction_mk _root_.ClassFormation.relativeCosetAction_zero _root_.ClassFormation.relativeNorm_apply_coe _root_.ClassFormation.relativeNorm_self _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.extensionFixedEndomorphism_apply_val _root_.KummerTheory.extensionFixedKernelElement_val _root_.KummerTheory.extensionFixedRepresentation_quotient_mk_apply_val _root_.KummerTheory.mem_extensionSubgroup_iff _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.ClassFormation.DegreeData.inertiaConjugationCosetEquiv_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ClassFormation

open CyclicCohomology

/-!
# The abstract reciprocity construction: descent from the Frobenius semigroup

The two maps on `G(\widetilde L/K)`--restriction to `G(L/K)` and normalized
degree--are jointly injective.  This is the group-theoretic fact used when two Frobenius lifts have the same
restriction and degree.
-/

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The image of `G_L` in `G_K / I_L`. -/
def extensionImageInInertiaQuotient (D : DegreeData G)
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal] :
    Subgroup (K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK) :=
  (extensionSubgroup K L hLK).map
    (QuotientGroup.mk' (D.extensionInertiaWithin K L hLK))

/-- The image of `G_L` in `G_K / I_L` is closed.  This is the compact-image
step implicit in the Galois correspondence used. -/
theorem extensionImageInInertiaQuotient_isClosed
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)] :
    IsClosed (D.extensionImageInInertiaQuotient K.field L hLK : Set
      (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)) := by
  let : IsClosed
      (D.extensionInertiaWithin K.field L hLK : Set K.field.toSubgroup) :=
    D.extensionInertiaWithin_isClosed K L hLK
  let E := extensionSubgroup K.field L hLK
  have hEclosed : IsClosed (E : Set K.field.toSubgroup) := by
    have hcarrier : (E : Set K.field.toSubgroup) =
        ((fun x : K.field.toSubgroup => (x : G)) ⁻¹' (L : Set G)) := by
      rfl
    rw [hcarrier]
    exact L.isClosed'.preimage continuous_subtype_val
  let : E.FiniteIndex :=
    @Subgroup.finiteIndex_of_finite_quotient K.field.toSubgroup _ E hLfinite
  have hEopen : IsOpen (E : Set K.field.toSubgroup) :=
    E.isOpen_of_isClosed_of_finiteIndex hEclosed
  change IsClosed
    ((QuotientGroup.mk' (D.extensionInertiaWithin K.field L hLK)) ''
      (E : Set K.field.toSubgroup))
  exact (D.extensionImageInInertiaQuotient K.field L hLK).isClosed_of_isOpen
    (QuotientGroup.isOpenMap_coe
      (N := D.extensionInertiaWithin K.field L hLK)
      (E : Set K.field.toSubgroup) hEopen)

/-- If a Frobenius lift restricts trivially to `L`, its fixed field contains
`L` (equivalently `G_Σ ≤ G_L`). -/
theorem frobeniusFixedField_le_of_restriction_eq_one
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (σ : D.FrobeniusElements K L hLK)
    (hσ : D.frobeniusRestriction K L hLK σ = 1) :
    (D.frobeniusFixedField K L hLK σ).toSubgroup ≤
      L.toSubgroup := by
  let H := D.extensionInertiaWithin K.field L hLK
  let E := extensionSubgroup K.field L hLK
  let Q := K.field.toSubgroup ⧸ H
  let J : Subgroup Q := D.extensionImageInInertiaQuotient K.field L hLK
  have hσJ : σ.1 ∈ J := by
    let k : K.field.toSubgroup := Quotient.out σ.1
    have hkq : QuotientGroup.mk k = σ.1 := Quotient.out_eq' σ.1
    have hkE : k ∈ E := by
      have hq : (QuotientGroup.mk k :
          K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK) = 1 := by
        change D.extensionRestriction K.field L hLK
          (QuotientGroup.mk k : K.field.toSubgroup ⧸ H) = 1
        rw [hkq]
        exact hσ
      simpa using QuotientGroup.eq.mp hq.symm
    exact ⟨k, hkE, hkq⟩
  have hClosureJ :
      (D.frobeniusClosure K L hLK σ).toSubgroup ≤ J := by
    change (Subgroup.closure (Set.range (fun _ : Unit => σ.1))).topologicalClosure ≤ J
    apply Subgroup.topologicalClosure_minimal
    · rw [Subgroup.closure_le]
      rintro q ⟨u, rfl⟩
      exact hσJ
    · exact D.extensionImageInInertiaQuotient_isClosed K L hLK
  rintro g ⟨k, hkClosure, rfl⟩
  have hkJ : (QuotientGroup.mk k : Q) ∈ J := hClosureJ hkClosure
  rcases hkJ with ⟨e, heE, heq⟩
  have hdiff : e⁻¹ * k ∈ H := QuotientGroup.eq.mp heq
  have hdiffE : e⁻¹ * k ∈ E := hdiff.1
  have hkE : k ∈ E := by
    have := E.mul_mem heE hdiffE
    simpa [mul_assoc] using this
  change (k : G) ∈ L
  exact hkE

/--
`frobeniusRestriction` satisfies the multiplication formula `D.frobeniusRestriction K L hLK (σ *
τ) = D.frobeniusRestriction K L hLK σ * D.frobeniusRestriction K L hLK τ`.
-/
@[simp]
theorem frobeniusRestriction_mul (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ τ : D.FrobeniusElements K L hLK) :
    D.frobeniusRestriction K L hLK (σ * τ) =
      D.frobeniusRestriction K L hLK σ *
        D.frobeniusRestriction K L hLK τ := by
  change D.extensionRestriction K.field L hLK (σ.1 * τ.1) =
    D.extensionRestriction K.field L hLK σ.1 *
      D.extensionRestriction K.field L hLK τ.1
  exact map_mul _ _ _

end DegreeData

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_MainMultiplicativity_FrobeniusActionRemainder
attribute [-instance] _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.chosenUnramifiedFrobeniusLift_exponent _root_.ClassFormation.DegreeData.frobeniusExponent_chosenDegreeOneFrobeniusElement _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.ValuationData.canonicalUnramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.canonicalValueQuotientHom_mk _root_.ClassFormation.ValuationData.canonicalValueReduction_one _root_.ClassFormation.ValuationData.unramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.mem_normFilterBasis_iff _root_.ClassFormation.orbitQuotientClosedCyclicEquiv_mk _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Frobenius action remainders

This file develops the Frobenius exponent, conjugation, quotient-action, and
action-remainder identities used by reciprocity-map multiplicativity.
-/

universe u

namespace ClassFormation

open KummerTheory
open CyclicCohomology

noncomputable section

open CategoryTheory

section frobeniusAlgebra

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The exponent is additive under multiplication in the Frobenius
semigroup. -/
@[simp]
theorem frobeniusExponent_mul (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ₁ σ₂ : D.FrobeniusElements K L hLK) :
    D.frobeniusExponent K L hLK (σ₁ * σ₂) =
      D.frobeniusExponent K L hLK σ₁ +
      D.frobeniusExponent K L hLK σ₂ := by
  apply proCIntegerOne_pow_nat_injective
  calc
    (Multiplicative.ofAdd (1 : ZHat)) ^
        D.frobeniusExponent K L hLK (σ₁ * σ₂) =
      D.extensionNormalizedDegree K L hLK (σ₁ * σ₂).1 :=
        (D.extensionNormalizedDegree_frobenius_eq_pow K L hLK
          (σ₁ * σ₂)).symm
    _ = D.extensionNormalizedDegree K L hLK σ₁.1 *
        D.extensionNormalizedDegree K L hLK σ₂.1 := by
      rw [frobeniusMul_coe, map_mul]
    _ = (Multiplicative.ofAdd (1 : ZHat)) ^
            D.frobeniusExponent K L hLK σ₁ *
        (Multiplicative.ofAdd (1 : ZHat)) ^
            D.frobeniusExponent K L hLK σ₂ := by
      rw [D.extensionNormalizedDegree_frobenius_eq_pow,
        D.extensionNormalizedDegree_frobenius_eq_pow]
    _ = (Multiplicative.ofAdd (1 : ZHat)) ^
            (D.frobeniusExponent K L hLK σ₁ +
              D.frobeniusExponent K L hLK σ₂) := by
      rw [pow_add]

end DegreeData

end frobeniusAlgebra

section frobeniusQuotientActions

/-!
Mathlib's `Rep ℤ G` requires its coefficient ring and acting group in the
same universe, so this representation-bearing portion has `G : IntegralRepGroupType`.
-/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- A Frobenius element fixes the elements of its actual fixed field,
viewed inside `A_{\widetilde L}`. -/
theorem frobeniusQuotientAction_fixedFieldInclusion (D : DegreeData G)
    (A : Rep ℤ G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (a : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ)) :
    D.frobeniusQuotientAction A K.field L hLK σ.1
        (fixedFieldInclusion A (D.frobeniusFixedField K L hLK σ)
          (D.maximalUnramifiedField L)
          (D.fieldInertia_le_frobeniusFixedField K L hLK σ) a) =
      fixedFieldInclusion A (D.frobeniusFixedField K L hLK σ)
        (D.maximalUnramifiedField L)
        (D.fieldInertia_le_frobeniusFixedField K L hLK σ) a := by
  let k : K.field.toSubgroup := Quotient.out σ.1
  have hσk : σ.1 = QuotientGroup.mk k := (Quotient.out_eq' σ.1).symm
  have hσClosure : σ.1 ∈
      (D.frobeniusClosure K L hLK σ).toSubgroup := by
    exact Subgroup.le_topologicalClosure _
      (Subgroup.subset_closure (by simp))
  have hkFixed : k ∈ D.frobeniusFixedSubgroupWithin K L hLK σ := by
    change QuotientGroup.mk k ∈
      (D.frobeniusClosure K L hLK σ).toSubgroup
    rw [← hσk]
    exact hσClosure
  rw [← D.extensionSubgroup_frobeniusFixedField K L hLK σ] at hkFixed
  obtain ⟨s, hs⟩ := hkFixed
  rw [hσk]
  apply Subtype.ext
  change A.ρ k.1 a.1 = a.1
  let sFixed : (D.frobeniusFixedField K L hLK σ).toSubgroup :=
    ⟨s.1, ⟨s, hs.1, rfl⟩⟩
  have hsval : sFixed.1 = k.1 := hs.2
  rw [← hsval]
  exact a.2 sFixed

end DegreeData

end frobeniusQuotientActions

section actionRemainderAlgebra

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- For the left `Rep` action, the remainder corresponding to the
right-action notation is `φⁿσ⁻¹`. -/
def frobeniusActionRemainder (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ σ : D.FrobeniusElements K L hLK) :
    K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK :=
  φ.1 ^ D.frobeniusExponent K L hLK σ * σ.1⁻¹

/-- If `φ` has Frobenius exponent one, its action remainder has normalized
degree zero. -/
theorem frobeniusActionRemainder_mem_degreeKernel (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ σ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1) :
    D.frobeniusActionRemainder K L hLK φ σ ∈
      (D.extensionNormalizedDegreeContinuous K L hLK).toMonoidHom.ker := by
  change D.extensionNormalizedDegree K L hLK
      (φ.1 ^ D.frobeniusExponent K L hLK σ * σ.1⁻¹) = 1
  rw [map_mul, map_pow, map_inv,
    D.extensionNormalizedDegree_frobenius_eq_pow K L hLK σ,
    D.extensionNormalizedDegree_frobenius_eq_pow K L hLK φ, hφ]
  simp

/-- Conjugate adapted to the left action:
`σ₄ˡ = φⁿ²σ₁φ⁻ⁿ²`. -/
def frobeniusActionConjugate (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ σ : D.FrobeniusElements K L hLK) (m : ℕ) :
    D.FrobeniusElements K L hLK := by
  let n := D.frobeniusExponent K L hLK σ
  refine ⟨φ.1 ^ m * σ.1 * φ.1⁻¹ ^ m, n,
    D.frobeniusExponent_pos K L hLK σ, ?_⟩
  rw [map_mul, map_mul, map_pow, map_pow, map_inv,
    D.extensionNormalizedDegree_frobenius_eq_pow K L hLK σ]
  simp [n, mul_assoc]

/-- The underlying quotient element of the Frobenius action conjugate. -/
@[simp]
theorem frobeniusActionConjugate_coe (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ σ : D.FrobeniusElements K L hLK) (m : ℕ) :
    (D.frobeniusActionConjugate K L hLK φ σ m).1 =
      φ.1 ^ m * σ.1 * φ.1⁻¹ ^ m := by
  simp [frobeniusActionConjugate]

/-- Frobenius action conjugation preserves the Frobenius exponent. -/
@[simp]
theorem frobeniusExponent_actionConjugate (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ σ : D.FrobeniusElements K L hLK) (m : ℕ) :
    D.frobeniusExponent K L hLK
        (D.frobeniusActionConjugate K L hLK φ σ m) =
      D.frobeniusExponent K L hLK σ := by
  apply proCIntegerOne_pow_nat_injective
  calc
    (Multiplicative.ofAdd (1 : ZHat)) ^
        D.frobeniusExponent K L hLK
          (D.frobeniusActionConjugate K L hLK φ σ m) =
      D.extensionNormalizedDegree K L hLK
        (D.frobeniusActionConjugate K L hLK φ σ m).1 :=
          (D.extensionNormalizedDegree_frobenius_eq_pow K L hLK
            (D.frobeniusActionConjugate K L hLK φ σ m)).symm
    _ = (Multiplicative.ofAdd (1 : ZHat)) ^
          D.frobeniusExponent K L hLK σ := by
      rw [frobeniusActionConjugate_coe, map_mul, map_mul, map_pow, map_pow,
        map_inv,
        D.extensionNormalizedDegree_frobenius_eq_pow K L hLK σ]
      simp [mul_assoc]

/-- The fixed field of the left-action conjugate
`φᵐσφ⁻ᵐ` is the corresponding conjugate of the fixed field of
`σ`.  The representative is only used to express the quotient
conjugation in the ambient absolute Galois group. -/
theorem conjugate_frobeniusFixedField_actionConjugate
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ σ : D.FrobeniusElements K L hLK) (m : ℕ) :
    let q := φ.1 ^ m
    let k : K.field.toSubgroup := Quotient.out q
    conjugateClosedSubgroup
        (D.frobeniusFixedField K L hLK σ) k.1⁻¹ =
      D.frobeniusFixedField K L hLK
        (D.frobeniusActionConjugate K L hLK φ σ m) := by
  dsimp only
  let q := φ.1 ^ m
  let k : K.field.toSubgroup := Quotient.out q
  let σ' := D.frobeniusActionConjugate K L hLK φ σ m
  have hkq :
      (QuotientGroup.mk k :
        K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) = q :=
    Quotient.out_eq' q
  have hσ' : σ'.1 = q * σ.1 * q⁻¹ := by
    simp [σ', q, frobeniusActionConjugate_coe]
  ext x
  change x ∈ conjugateClosedSubgroup
      (D.frobeniusFixedField K L hLK σ) k.1⁻¹ ↔
    x ∈ D.frobeniusFixedField K L hLK σ'
  rw [conjugateClosedSubgroup_mem]
  constructor
  · intro hx
    obtain ⟨t, htClosure, htx⟩ := hx
    let xK : K.field.toSubgroup := ⟨x, by
      have htK : t.1 ∈ K.field.toSubgroup := t.2
      have htxval : t.1 = k.1⁻¹ * x * k.1 := by simpa using htx
      have hxval : x = k.1 * t.1 * k.1⁻¹ := by
        calc
          x = k.1 * (k.1⁻¹ * x * k.1) * k.1⁻¹ := by
            simp [mul_assoc]
          _ = k.1 * t.1 * k.1⁻¹ := by rw [htxval]
      rw [hxval]
      exact K.field.toSubgroup.mul_mem
        (K.field.toSubgroup.mul_mem k.2 htK) (K.field.toSubgroup.inv_mem k.2)⟩
    have htClosure' : QuotientGroup.mk t ∈
        (closedSubgroupGenerated ({σ.1} : Set
          (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK))).toSubgroup := by
      simpa [DegreeData.frobeniusClosure] using htClosure
    have hxClosure' : q * QuotientGroup.mk t * q⁻¹ ∈
        (closedSubgroupGenerated ({σ'.1} : Set
          (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK))).toSubgroup := by
      rw [hσ']
      exact (mem_closedSubgroupGenerated_conjugate_iff
        q σ.1 (QuotientGroup.mk t)).mp htClosure'
    have hxClosure : QuotientGroup.mk xK ∈
        (D.frobeniusClosure K L hLK σ').toSubgroup := by
      have hxK : xK = k * t * k⁻¹ := by
        apply Subtype.ext
        dsimp [xK]
        have htxval : t.1 = k.1⁻¹ * x * k.1 := by simpa using htx
        calc
          x = k.1 * (k.1⁻¹ * x * k.1) * k.1⁻¹ := by
            simp [mul_assoc]
          _ = k.1 * t.1 * k.1⁻¹ := by rw [htxval]
      rw [hxK]
      change (QuotientGroup.mk k :
          K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) *
          QuotientGroup.mk t * (QuotientGroup.mk k)⁻¹ ∈ _
      rw [hkq]
      simpa [DegreeData.frobeniusClosure] using hxClosure'
    exact ⟨xK, hxClosure, rfl⟩
  · intro hx
    obtain ⟨t, htClosure, htx⟩ := hx
    let yK : K.field.toSubgroup := ⟨k.1⁻¹ * x * k.1, by
      have htK : t.1 ∈ K.field.toSubgroup := t.2
      rw [← htx]
      exact K.field.toSubgroup.mul_mem
        (K.field.toSubgroup.mul_mem (K.field.toSubgroup.inv_mem k.2) htK) k.2⟩
    have htClosure' : QuotientGroup.mk t ∈
        (closedSubgroupGenerated ({σ'.1} : Set
          (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK))).toSubgroup := by
      simpa [DegreeData.frobeniusClosure] using htClosure
    have hyClosure' : QuotientGroup.mk yK ∈
        (closedSubgroupGenerated ({σ.1} : Set
          (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK))).toSubgroup := by
      apply (mem_closedSubgroupGenerated_conjugate_iff
        q σ.1 (QuotientGroup.mk yK)).mpr
      have hyK : k * yK * k⁻¹ = t := by
        apply Subtype.ext
        dsimp [yK]
        simpa [mul_assoc] using htx.symm
      have hyKq : q * QuotientGroup.mk yK * q⁻¹ =
          (QuotientGroup.mk t :
            K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) := by
        rw [← hkq]
        simpa using congrArg
          (fun z : K.field.toSubgroup =>
            (QuotientGroup.mk z :
              K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)) hyK
      rw [hyKq]
      rw [← hσ']
      exact htClosure'
    exact ⟨yK, by simpa [DegreeData.frobeniusClosure] using hyClosure', by simp [yK]⟩

end DegreeData

end actionRemainderAlgebra

section actionRemainderMultiplication

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Left-action translation of `τ₃=τ₂τ₄`: conjugation moves to
the second factor and the order reverses. -/
theorem frobeniusActionRemainder_mul (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ σ₁ σ₂ : D.FrobeniusElements K L hLK) :
    D.frobeniusActionRemainder K L hLK φ (σ₁ * σ₂) =
      D.frobeniusActionRemainder K L hLK φ
          (D.frobeniusActionConjugate K L hLK φ σ₂
            (D.frobeniusExponent K L hLK σ₁)) *
        D.frobeniusActionRemainder K L hLK φ σ₁ := by
  simp [frobeniusActionRemainder, frobeniusExponent_mul,
    frobeniusActionConjugate_coe, frobeniusExponent_actionConjugate,
    frobeniusMul_coe, pow_add, mul_assoc]
  have hp : φ.1 ^ D.frobeniusExponent K L hLK σ₁ *
      φ.1 ^ D.frobeniusExponent K L hLK σ₂ =
      φ.1 ^ D.frobeniusExponent K L hLK σ₂ *
        φ.1 ^ D.frobeniusExponent K L hLK σ₁ := by
    rw [← pow_add, ← pow_add, Nat.add_comm]
  calc
    φ.1 ^ D.frobeniusExponent K L hLK σ₁ *
          (φ.1 ^ D.frobeniusExponent K L hLK σ₂ *
            (σ₂.1⁻¹ * σ₁.1⁻¹)) =
        (φ.1 ^ D.frobeniusExponent K L hLK σ₁ *
          φ.1 ^ D.frobeniusExponent K L hLK σ₂) *
            (σ₂.1⁻¹ * σ₁.1⁻¹) := by rw [mul_assoc]
    _ = (φ.1 ^ D.frobeniusExponent K L hLK σ₂ *
          φ.1 ^ D.frobeniusExponent K L hLK σ₁) *
            (σ₂.1⁻¹ * σ₁.1⁻¹) := by rw [hp]
    _ = φ.1 ^ D.frobeniusExponent K L hLK σ₂ *
          (φ.1 ^ D.frobeniusExponent K L hLK σ₁ *
            (σ₂.1⁻¹ * σ₁.1⁻¹)) := by rw [mul_assoc]

end DegreeData

end actionRemainderMultiplication

section fixedFieldRemainderActions

/-!
Mathlib's `Rep ℤ G` requires its coefficient ring and acting group in the
same universe, so this representation-bearing portion has `G : IntegralRepGroupType`.
-/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- On the fixed field of `σ`, the left-action remainder acts exactly as
the `n`-th power of `φ`. -/
theorem frobeniusActionRemainder_apply_fixedField (D : DegreeData G)
    (A : Rep ℤ G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ σ : D.FrobeniusElements K L hLK)
    (a : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ)) :
    D.frobeniusQuotientAction A K.field L hLK
        (D.frobeniusActionRemainder K L hLK φ σ)
        (fixedFieldInclusion A (D.frobeniusFixedField K L hLK σ)
          (D.maximalUnramifiedField L)
          (D.fieldInertia_le_frobeniusFixedField K L hLK σ) a) =
      D.frobeniusQuotientAction A K.field L hLK
        (φ.1 ^ D.frobeniusExponent K L hLK σ)
        (fixedFieldInclusion A (D.frobeniusFixedField K L hLK σ)
          (D.maximalUnramifiedField L)
          (D.fieldInertia_le_frobeniusFixedField K L hLK σ) a) := by
  let aI := fixedFieldInclusion A
    (D.frobeniusFixedField K L hLK σ)
    (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField K L hLK σ) a
  let B := D.frobeniusQuotientRepresentation A K.field L hLK
  have hfix : B.ρ σ.1 aI = aI := by
    change D.frobeniusQuotientAction A K.field L hLK σ.1 aI = aI
    exact D.frobeniusQuotientAction_fixedFieldInclusion A K L hLK σ a
  have hinv : B.ρ σ.1⁻¹ aI = aI := by
    have hmul : B.ρ (σ.1⁻¹ * σ.1) aI = aI := by
      rw [inv_mul_cancel, map_one]
      rfl
    rw [map_mul] at hmul
    change B.ρ σ.1⁻¹ (B.ρ σ.1 aI) = aI at hmul
    rw [hfix] at hmul
    exact hmul
  change B.ρ
      (φ.1 ^ D.frobeniusExponent K L hLK σ * σ.1⁻¹) aI =
    B.ρ (φ.1 ^ D.frobeniusExponent K L hLK σ) aI
  rw [map_mul]
  change B.ρ (φ.1 ^ D.frobeniusExponent K L hLK σ) (B.ρ σ.1⁻¹ aI) =
    B.ρ (φ.1 ^ D.frobeniusExponent K L hLK σ) aI
  rw [hinv]

end DegreeData

end fixedFieldRemainderActions

end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_MainMultiplicativity_ConjugatePrimeNorm
attribute [-instance] _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.chosenUnramifiedFrobeniusLift_exponent _root_.ClassFormation.DegreeData.frobeniusExponent_chosenDegreeOneFrobeniusElement _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.ValuationData.canonicalUnramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.canonicalValueQuotientHom_mk _root_.ClassFormation.ValuationData.canonicalValueReduction_one _root_.ClassFormation.ValuationData.unramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.mem_normFilterBasis_iff _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Norms of primes in conjugate Frobenius fixed fields

This file transports prime elements across Frobenius-action conjugation and
proves equality of their relative norms in the base fixed field.
-/

universe u

namespace ClassFormation

open KummerTheory
open CyclicCohomology

noncomputable section

open CategoryTheory

section conjugatePrimeNorms

/-!
Mathlib's `Rep ℤ G` requires its coefficient ring and acting group in the
same universe, so this representation-bearing portion has `G : IntegralRepGroupType`.
-/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The prime used for the conjugate Frobenius fixed field may be chosen
as the conjugate of a prime in the original fixed field.  Conjugation compatibility of normalized valuations preserves primality, while conjugation equivariance of the relative
norm and the fact that the conjugating representative lies in `G_K` give
equality of the two norms in `A_K`. -/
theorem exists_primeElement_frobeniusActionConjugate_norm_eq
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (φ σ : D.FrobeniusElements
      (K.toFiniteResidueAbstractField D) L hLK) (m : ℕ)
    (π : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK σ))
    (hπ :
      let KR := K.toFiniteResidueAbstractField D
      let Sigma : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK σ,
          D.frobeniusFixedField_absoluteFinite K L hLK σ⟩
      v.IsPrimeElement Sigma π) :
    let KR := K.toFiniteResidueAbstractField D
    let σ' := D.frobeniusActionConjugate KR L hLK φ σ m
    let S := D.frobeniusFixedField KR L hLK σ
    let S' := D.frobeniusFixedField KR L hLK σ'
    let hSK := D.frobeniusFixedField_le KR L hLK σ
    let hS'K := D.frobeniusFixedField_le KR L hLK σ'
    letI : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field S hSK) :=
      D.frobeniusFixedField_finite KR L hLK σ
    letI : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field S' hS'K) :=
      D.frobeniusFixedField_finite KR L hLK σ'
    let Sigma' : FiniteAbstractField G :=
      ⟨S', D.frobeniusFixedField_absoluteFinite K L hLK σ'⟩
    ∃ π' : ambientFixedAddSubgroup A S',
      v.IsPrimeElement Sigma' π' ∧
        relativeNorm A K.field S' hS'K π' =
          relativeNorm A K.field S hSK π := by
  dsimp only
  let KR := K.toFiniteResidueAbstractField D
  let hLnormalKR : (extensionSubgroup KR.field L hLK).Normal := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal
  let hLfiniteKR : Finite
      (KR.field.toSubgroup ⧸ extensionSubgroup KR.field L hLK) := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLfinite
  let σ' := D.frobeniusActionConjugate KR L hLK φ σ m
  let S := D.frobeniusFixedField KR L hLK σ
  let S' := D.frobeniusFixedField KR L hLK σ'
  let hSK := D.frobeniusFixedField_le KR L hLK σ
  let hS'K := D.frobeniusFixedField_le KR L hLK σ'
  let hSfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field S hSK) :=
    D.frobeniusFixedField_finite KR L hLK σ
  let hS'finite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field S' hS'K) :=
    D.frobeniusFixedField_finite KR L hLK σ'
  let hSabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) S (le_baseField S)) :=
    D.frobeniusFixedField_absoluteFinite K L hLK σ
  let hS'absolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) S' (le_baseField S')) :=
    D.frobeniusFixedField_absoluteFinite K L hLK σ'
  let Sigma : FiniteAbstractField G := ⟨S, hSabsolute⟩
  let Sigma' : FiniteAbstractField G := ⟨S', hS'absolute⟩
  let q := φ.1 ^ m
  let k : K.field.toSubgroup := Quotient.out q
  let s : G := k.1⁻¹
  let C := conjugateClosedSubgroup S s
  let Kc := conjugateClosedSubgroup K.field s
  let hCS := conjugateClosedSubgroup_mono hSK s
  have hC : C = S' := by
    simpa [C, S, S', σ', q, k, s] using
      D.conjugate_frobeniusFixedField_actionConjugate KR L hLK φ σ m
  have hKc : Kc = K.field := by
    ext x
    change x ∈ conjugateClosedSubgroup K.field s ↔ x ∈ K.field
    rw [conjugateClosedSubgroup_mem]
    constructor
    · intro hx
      change x ∈ K.field.toSubgroup
      simpa [s, mul_assoc] using K.field.toSubgroup.mul_mem
        (K.field.toSubgroup.mul_mem k.2 hx) (K.field.toSubgroup.inv_mem k.2)
    · intro hx
      change s * x * s⁻¹ ∈ K.field.toSubgroup
      simpa [s] using K.field.toSubgroup.mul_mem
        (K.field.toSubgroup.mul_mem (K.field.toSubgroup.inv_mem k.2) hx) k.2
  let hCabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) C (le_baseField C)) :=
    Finite.of_equiv
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G) S (le_baseField S))
      (by
        simpa [C, baseField] using
          (absoluteConjugateCosetEquiv S s).symm)
  let SigmaC : FiniteAbstractField G := Sigma.conjugate s
  let πC : ambientFixedAddSubgroup A C :=
    conjugateFixedElement A S s π
  let π' : ambientFixedAddSubgroup A S' :=
    ⟨πC.1, by rw [← hC]; exact πC.2⟩
  have hπC : v.IsPrimeElement SigmaC πC := by
    change v.valuationAt Sigma π = v.oneValue at hπ
    change v.valuationAt SigmaC πC = v.oneValue
    have hconj : v.valuationAt SigmaC πC = v.valuationAt Sigma π := by
      simpa [C, SigmaC, Sigma, πC] using
        v.normalizedValuation_conjugate Sigma s π
    exact hconj.trans hπ
  have hπ' : v.IsPrimeElement Sigma' π' := by
    change v.valuationAt SigmaC πC = v.oneValue at hπC
    change v.valuationAt Sigma' π' = v.oneValue
    have valuation_transport
        (C₀ S₀ : FiniteAbstractField G)
        (h : C₀.field = S₀.field)
        (aC : ambientFixedAddSubgroup A C₀.field)
        (aS : ambientFixedAddSubgroup A S₀.field)
        (ha : aC.1 = aS.1) :
        v.valuationAt S₀ aS = v.valuationAt C₀ aC := by
      cases C₀ with
      | mk C₀ hC₀ =>
          cases S₀ with
          | mk S₀ hS₀ =>
              dsimp only at h
              subst S₀
              congr 1
              exact Subtype.ext ha.symm
    have hSigmaField : SigmaC.field = Sigma'.field := by
      change C = S'
      exact hC
    have hv : v.valuationAt Sigma' π' = v.valuationAt SigmaC πC :=
      valuation_transport SigmaC Sigma' hSigmaField πC π' rfl
    exact hv.trans hπC
  refine ⟨π', hπ', ?_⟩
  let hCSfinite : Finite
      (Kc.toSubgroup ⧸ extensionSubgroup Kc C hCS) :=
    finite_conjugateExtension K.field S hSK s
  have hnormC := relativeNorm_conjugate_apply A K.field S hSK s π
  apply Subtype.ext
  have relativeNorm_transport
      (K₀ K₁ L₀ L₁ : ClosedSubgroup G)
      (h₀ : L₀.toSubgroup ≤ K₀.toSubgroup)
      (h₁ : L₁.toSubgroup ≤ K₁.toSubgroup)
      [Finite (K₀.toSubgroup ⧸ extensionSubgroup K₀ L₀ h₀)]
      [Finite (K₁.toSubgroup ⧸ extensionSubgroup K₁ L₁ h₁)]
      (hK₀ : K₀ = K₁) (hL₀ : L₀ = L₁)
      (a₀ : ambientFixedAddSubgroup A L₀)
      (a₁ : ambientFixedAddSubgroup A L₁)
      (ha : a₀.1 = a₁.1) :
      ((relativeNorm A K₀ L₀ h₀ a₀ :
        ambientFixedAddSubgroup A K₀) : A.V) =
      ((relativeNorm A K₁ L₁ h₁ a₁ :
        ambientFixedAddSubgroup A K₁) : A.V) := by
    subst K₁
    subst L₁
    have ha' : a₀ = a₁ := Subtype.ext ha
    subst a₁
    rfl
  have hleft :
      ((relativeNorm A K.field S' hS'K π' :
        ambientFixedAddSubgroup A K.field) : A.V) =
      ((relativeNorm A Kc C hCS πC :
        ambientFixedAddSubgroup A Kc) : A.V) := by
    exact (relativeNorm_transport Kc K.field C S' hCS hS'K
      hKc hC πC π' rfl).symm
  calc
    ((relativeNorm A K.field S' hS'K π' :
        ambientFixedAddSubgroup A K.field) : A.V) =
        ((relativeNorm A Kc C hCS πC :
          ambientFixedAddSubgroup A Kc) : A.V) := hleft
    _ = ((conjugateFixedElement A K.field s
        (relativeNorm A K.field S hSK π) :
          ambientFixedAddSubgroup A Kc) : A.V) :=
      congrArg Subtype.val hnormC
    _ = ((relativeNorm A K.field S hSK π :
        ambientFixedAddSubgroup A K.field) : A.V) := by
      rw [conjugateFixedElement_coe]
      have hs : s⁻¹ = k.1 := by simp [s]
      rw [hs]
      change A.ρ k.1 (relativeNorm A K.field S hSK π).1 =
        (relativeNorm A K.field S hSK π).1
      exact (relativeNorm A K.field S hSK π).2 k

end DegreeData

end conjugatePrimeNorms

end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_MainMultiplicativity_CorrectionSum
attribute [-instance] _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Correction sums for reciprocity multiplicativity

This file packages the three correction coefficients and action elements,
proves their degree-zero property, and identifies their action-difference sum.
-/

universe u

namespace ClassFormation

open KummerTheory
open CyclicCohomology

noncomputable section

open CategoryTheory
open scoped BigOperators

section correctionActionDegrees

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- All three actual correction actions have normalized degree zero, as
required by the universal norm-descent lemma. -/
theorem frobeniusMultiplicativityCorrectionAction_mem_degreeKernel
    (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ σ₁ σ₂ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1) :
    let σ₄ := D.frobeniusActionConjugate K L hLK φ σ₂
      (D.frobeniusExponent K L hLK σ₁)
    let τ₁ := D.frobeniusActionRemainder K L hLK φ σ₁
    let τ₄ := D.frobeniusActionRemainder K L hLK φ σ₄
    ∀ i : Fin 3,
      frobeniusMultiplicativityCorrectionAction τ₁ τ₄ i ∈
        (D.extensionNormalizedDegreeContinuous K L hLK).toMonoidHom.ker := by
  dsimp only
  let σ₄ := D.frobeniusActionConjugate K L hLK φ σ₂
    (D.frobeniusExponent K L hLK σ₁)
  let τ₁ := D.frobeniusActionRemainder K L hLK φ σ₁
  let τ₄ := D.frobeniusActionRemainder K L hLK φ σ₄
  have hτ₁ := D.frobeniusActionRemainder_mem_degreeKernel
    K L hLK φ σ₁ hφ
  have hτ₄ := D.frobeniusActionRemainder_mem_degreeKernel
    K L hLK φ σ₄ hφ
  intro i
  fin_cases i
  · exact hτ₄
  · exact hτ₁
  · exact hτ₄

end DegreeData

end correctionActionDegrees

end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_MainMultiplicativity_PrimeUnitDifferences
attribute [-instance] _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.chosenUnramifiedFrobeniusLift_exponent _root_.ClassFormation.DegreeData.frobeniusExponent_chosenDegreeOneFrobeniusElement _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.ValuationData.canonicalUnramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.canonicalValueQuotientHom_mk _root_.ClassFormation.ValuationData.canonicalValueReduction_one _root_.ClassFormation.ValuationData.unramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.mem_normFilterBasis_iff _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite-stage unit differences of Frobenius primes

This file proves that differences of Frobenius fixed-field primes, including
differences from quotient-action translates, come from finite-stage units.
-/

universe u

namespace ClassFormation

open KummerTheory
open CyclicCohomology

noncomputable section

open CategoryTheory

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Two prime elements coming from Frobenius fixed fields differ by a
finite-stage unit after inclusion in `A_{\widetilde L}`. The common stage is
their finite compositum, which is unramified over both fixed fields. -/
theorem frobeniusPrimeDifference_mem_infiniteUnitAddSubgroup
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (σ τ : D.FrobeniusElements
      (K.toFiniteResidueAbstractField D) L hLK)
    (πσ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK σ))
    (πτ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK τ))
    (hπσ :
      let KR := K.toFiniteResidueAbstractField D
      let Sigma : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK σ,
          D.frobeniusFixedField_absoluteFinite K L hLK σ⟩
      v.IsPrimeElement Sigma πσ)
    (hπτ :
      let KR := K.toFiniteResidueAbstractField D
      let Tau : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK τ,
          D.frobeniusFixedField_absoluteFinite K L hLK τ⟩
      v.IsPrimeElement Tau πτ) :
    let KR := K.toFiniteResidueAbstractField D
    let E := D.maximalUnramifiedField L
    let pσ := fixedFieldInclusion A
      (D.frobeniusFixedField KR L hLK σ) E
      (D.fieldInertia_le_frobeniusFixedField KR L hLK σ) πσ
    let pτ := fixedFieldInclusion A
      (D.frobeniusFixedField KR L hLK τ) E
      (D.fieldInertia_le_frobeniusFixedField KR L hLK τ) πτ
    pσ - pτ ∈ v.infiniteUnitAddSubgroup E K
      (D.maximalUnramifiedField_le_of_le hLK) := by
  dsimp only
  let KR := K.toFiniteResidueAbstractField D
  let hLnormalKR : (extensionSubgroup KR.field L hLK).Normal := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal
  let hLfiniteKR : Finite
      (KR.field.toSubgroup ⧸ extensionSubgroup KR.field L hLK) := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLfinite
  let E := D.maximalUnramifiedField L
  let S := D.frobeniusFixedField KR L hLK σ
  let T := D.frobeniusFixedField KR L hLK τ
  let hSK : S.toSubgroup ≤ K.field.toSubgroup :=
    D.frobeniusFixedField_le KR L hLK σ
  let hTK : T.toSubgroup ≤ K.field.toSubgroup :=
    D.frobeniusFixedField_le KR L hLK τ
  let M := D.frobeniusFixedIntermediateField KR L hLK σ
  let N := D.frobeniusFixedIntermediateField KR L hLK τ
  let P := M.compositum N
  let hPS : P.field.toSubgroup ≤ S.toSubgroup :=
    M.compositum_le_left N
  let hPT : P.field.toSubgroup ≤ T.toSubgroup :=
    M.compositum_le_right N
  let hSabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) S (le_baseField S)) :=
    D.frobeniusFixedField_absoluteFinite K L hLK σ
  let hTabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) T (le_baseField T)) :=
    D.frobeniusFixedField_absoluteFinite K L hLK τ
  let Sigma : FiniteAbstractField G := ⟨S, hSabsolute⟩
  let Tau : FiniteAbstractField G := ⟨T, hTabsolute⟩
  let hPfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field P.field P.below) := P.finite
  let Pi : FiniteAbstractField G := P.toFiniteAbstractField K
  let hPSfinite : Finite
      (S.toSubgroup ⧸ extensionSubgroup S P.field hPS) :=
    FiniteIntermediateField.finite_extension_of_le P.below hSK hPS
  let hPTfinite : Finite
      (T.toSubgroup ⧸ extensionSubgroup T P.field hPT) :=
    FiniteIntermediateField.finite_extension_of_le P.below hTK hPT
  let EPS : FiniteAbstractFieldExtension G :=
    { field := Pi
      base := Sigma
      below := hPS
      finiteQuotient := hPSfinite }
  let EPT : FiniteAbstractFieldExtension G :=
    { field := Pi
      base := Tau
      below := hPT
      finiteQuotient := hPTfinite }
  have hPSunramified :
      EPS.IsUnramified D := by
    change D.fieldInertia S ≤ P.field.toSubgroup
    have hSI : D.fieldInertia S = D.fieldInertia L := by
      simpa [S] using
        D.frobeniusFixedField_fieldInertia KR L hLK σ
    rw [hSI]
    exact P.above
  have hPTunramified :
      EPT.IsUnramified D := by
    change D.fieldInertia T ≤ P.field.toSubgroup
    have hTI : D.fieldInertia T = D.fieldInertia L := by
      simpa [T] using
        D.frobeniusFixedField_fieldInertia KR L hLK τ
    rw [hTI]
    exact P.above
  let πσP := fixedFieldInclusion A S P.field hPS πσ
  let πτP := fixedFieldInclusion A T P.field hPT πτ
  have hπσP : v.IsPrimeElement Pi πσP := by
    exact v.prime_of_unramified EPS hPSunramified πσ hπσ
  have hπτP : v.IsPrimeElement Pi πτP := by
    exact v.prime_of_unramified EPT hPTunramified πτ hπτ
  let uP : v.unitAddSubgroup Pi :=
    ⟨πσP - πτP,
      v.sub_mem_unitAddSubgroup_of_prime Pi hπτP hπσP⟩
  rw [v.mem_infiniteUnitAddSubgroup_iff]
  refine ⟨P, uP, ?_⟩
  apply Subtype.ext
  rfl

/-- The difference between a prime and any `G(\widetilde L/K)`-translate
of it is a finite-stage unit.  A finite Galois refinement of the prime's
fixed field supplies a stage stable under the chosen quotient
representative. -/
theorem frobeniusPrime_actionDifference_mem_infiniteUnitAddSubgroup
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (σ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK)
    (π : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK σ))
    (hπ :
      let KR := K.toFiniteResidueAbstractField D
      let Sigma : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK σ,
          D.frobeniusFixedField_absoluteFinite K L hLK σ⟩
      v.IsPrimeElement Sigma π)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) :
    let KR := K.toFiniteResidueAbstractField D
    let E := D.maximalUnramifiedField L
    let p := fixedFieldInclusion A
      (D.frobeniusFixedField KR L hLK σ) E
      (D.fieldInertia_le_frobeniusFixedField KR L hLK σ) π
    p - D.frobeniusQuotientAction A K.field L hLK q p ∈
      v.infiniteUnitAddSubgroup E K
        (D.maximalUnramifiedField_le_of_le hLK) := by
  dsimp only
  let KR := K.toFiniteResidueAbstractField D
  let hLnormalKR : (extensionSubgroup KR.field L hLK).Normal := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal
  let hLfiniteKR : Finite
      (KR.field.toSubgroup ⧸ extensionSubgroup KR.field L hLK) := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLfinite
  let E := D.maximalUnramifiedField L
  let S := D.frobeniusFixedField KR L hLK σ
  let hSK : S.toSubgroup ≤ K.field.toSubgroup :=
    D.frobeniusFixedField_le KR L hLK σ
  let M := D.frobeniusFixedIntermediateField KR L hLK σ
  let hEnormal : (extensionSubgroup K.field E
      (D.maximalUnramifiedField_le_of_le hLK)).Normal :=
    D.extensionSubgroup_maximalUnramifiedField_normal K.field L hLK
  let P := M.galoisRefinement
  let hPS : P.field.toSubgroup ≤ S.toSubgroup :=
    M.galoisRefinement_le_field
  let hSabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) S (le_baseField S)) :=
    D.frobeniusFixedField_absoluteFinite K L hLK σ
  let Sigma : FiniteAbstractField G := ⟨S, hSabsolute⟩
  let hPfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field P.field P.below) := P.finite
  let Pi : FiniteAbstractField G := P.toFiniteAbstractField K
  let hPSfinite : Finite
      (S.toSubgroup ⧸ extensionSubgroup S P.field hPS) :=
    FiniteIntermediateField.finite_extension_of_le P.below hSK hPS
  let hPnormal : (extensionSubgroup K.field P.field P.below).Normal := by
    exact FiniteIntermediateField.galoisRefinement_normal M
  let EPS : FiniteAbstractFieldExtension G :=
    { field := Pi
      base := Sigma
      below := hPS
      finiteQuotient := hPSfinite }
  let EPK : FiniteAbstractFieldExtension G :=
    { field := Pi
      base := K
      below := P.below
      finiteQuotient := hPfinite }
  have hPSunramified :
      EPS.IsUnramified D := by
    change D.fieldInertia S ≤ P.field.toSubgroup
    have hSI : D.fieldInertia S = D.fieldInertia L := by
      simpa [S] using
        D.frobeniusFixedField_fieldInertia KR L hLK σ
    rw [hSI]
    exact P.above
  let πP := fixedFieldInclusion A S P.field hPS π
  have hπP : v.IsPrimeElement Pi πP := by
    exact v.prime_of_unramified EPS hPSunramified π hπ
  let k : K.field.toSubgroup := Quotient.out q
  let πqP := normalExtensionAction A K.field P.field P.below hPnormal k πP
  have hπqP : v.IsPrimeElement Pi πqP := by
    change v.valuationAt Pi πP = v.oneValue at hπP
    change v.valuationAt Pi πqP = v.oneValue
    calc
      v.valuationAt Pi πqP = v.valuationAt Pi πP := by
        have hvaluation :=
          v.valuationAt_normalExtensionAction EPK hPnormal k πP
        change v.valuationAt Pi
            (normalExtensionAction A K.field P.field P.below hPnormal k πP) =
          v.valuationAt Pi πP at hvaluation
        exact hvaluation
      _ = v.oneValue := hπP
  let uP : v.unitAddSubgroup Pi :=
    ⟨πP - πqP,
      v.sub_mem_unitAddSubgroup_of_prime Pi hπqP hπP⟩
  rw [v.mem_infiniteUnitAddSubgroup_iff]
  refine ⟨P, uP, ?_⟩
  have hkq : (QuotientGroup.mk k :
      K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) = q :=
    Quotient.out_eq' q
  rw [← hkq, D.frobeniusQuotientAction_mk]
  apply Subtype.ext
  rfl

end DegreeData

end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_MainMultiplicativity_FiniteStageCorrections
attribute [-instance] _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.chosenUnramifiedFrobeniusLift_exponent _root_.ClassFormation.DegreeData.frobeniusExponent_chosenDegreeOneFrobeniusElement _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.ValuationData.canonicalUnramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.canonicalValueQuotientHom_mk _root_.ClassFormation.ValuationData.canonicalValueReduction_one _root_.ClassFormation.ValuationData.unramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.mem_normFilterBasis_iff _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite-stage correction terms for reciprocity multiplicativity

This file proves that the alternating Frobenius power sum and each coefficient
of the three-term correction identity are genuine finite-stage units.
-/

universe u

namespace ClassFormation

open KummerTheory
open CyclicCohomology

noncomputable section

open CategoryTheory

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The alternating Frobenius power sum used in multiplicativity is a genuine
finite-stage unit. Splitting the long sum into two blocks expresses it as
power sums of differences of prime elements. -/
theorem frobeniusPowerSum_alternating_mem_infiniteUnitAddSubgroup
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (φ σ₁ σ₂ : D.FrobeniusElements
      (K.toFiniteResidueAbstractField D) L hLK)
    (π₁ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK σ₁))
    (π₃ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK
        (σ₁ * σ₂)))
    (π₄ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK
        (D.frobeniusActionConjugate (K.toFiniteResidueAbstractField D)
          L hLK φ σ₂
          (D.frobeniusExponent (K.toFiniteResidueAbstractField D)
            L hLK σ₁))))
    (hπ₁ :
      let KR := K.toFiniteResidueAbstractField D
      let Sigma1 : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK σ₁,
          D.frobeniusFixedField_absoluteFinite K L hLK σ₁⟩
      v.IsPrimeElement Sigma1 π₁)
    (hπ₃ :
      let KR := K.toFiniteResidueAbstractField D
      let Sigma3 : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK (σ₁ * σ₂),
          D.frobeniusFixedField_absoluteFinite K L hLK (σ₁ * σ₂)⟩
      v.IsPrimeElement Sigma3 π₃)
    (hπ₄ :
      let KR := K.toFiniteResidueAbstractField D
      let σ₄ := D.frobeniusActionConjugate KR L hLK φ σ₂
        (D.frobeniusExponent KR L hLK σ₁)
      let Sigma4 : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK σ₄,
          D.frobeniusFixedField_absoluteFinite K L hLK σ₄⟩
      v.IsPrimeElement Sigma4 π₄) :
    let KR := K.toFiniteResidueAbstractField D
    let σ₃ := σ₁ * σ₂
    let σ₄ := D.frobeniusActionConjugate KR L hLK φ σ₂
      (D.frobeniusExponent KR L hLK σ₁)
    let p₁ := fixedFieldInclusion A
      (D.frobeniusFixedField KR L hLK σ₁)
      (D.maximalUnramifiedField L)
      (D.fieldInertia_le_frobeniusFixedField KR L hLK σ₁) π₁
    let p₃ := fixedFieldInclusion A
      (D.frobeniusFixedField KR L hLK σ₃)
      (D.maximalUnramifiedField L)
      (D.fieldInertia_le_frobeniusFixedField KR L hLK σ₃) π₃
    let p₄ := fixedFieldInclusion A
      (D.frobeniusFixedField KR L hLK σ₄)
      (D.maximalUnramifiedField L)
      (D.fieldInertia_le_frobeniusFixedField KR L hLK σ₄) π₄
    let u := D.frobeniusPowerSum A KR.field L hLK φ.1
        (D.frobeniusExponent KR L hLK σ₄) p₄ +
      D.frobeniusPowerSum A KR.field L hLK φ.1
        (D.frobeniusExponent KR L hLK σ₁) p₁ -
      D.frobeniusPowerSum A KR.field L hLK φ.1
        (D.frobeniusExponent KR L hLK σ₃) p₃
    u ∈ v.infiniteUnitAddSubgroup (D.maximalUnramifiedField L) K
      (D.maximalUnramifiedField_le_of_le hLK) := by
  dsimp only
  let KR := K.toFiniteResidueAbstractField D
  let hLnormalKR : (extensionSubgroup KR.field L hLK).Normal := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal
  let hLfiniteKR : Finite
      (KR.field.toSubgroup ⧸ extensionSubgroup KR.field L hLK) := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLfinite
  let σ₃ := σ₁ * σ₂
  let σ₄ := D.frobeniusActionConjugate KR L hLK φ σ₂
    (D.frobeniusExponent KR L hLK σ₁)
  let p₁ := fixedFieldInclusion A
    (D.frobeniusFixedField KR L hLK σ₁)
    (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField KR L hLK σ₁) π₁
  let p₃ := fixedFieldInclusion A
    (D.frobeniusFixedField KR L hLK σ₃)
    (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField KR L hLK σ₃) π₃
  let p₄ := fixedFieldInclusion A
    (D.frobeniusFixedField KR L hLK σ₄)
    (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField KR L hLK σ₄) π₄
  let n₁ := D.frobeniusExponent KR L hLK σ₁
  let n₃ := D.frobeniusExponent KR L hLK σ₃
  let n₄ := D.frobeniusExponent KR L hLK σ₄
  let U := v.infiniteUnitAddSubgroup (D.maximalUnramifiedField L) K
    (D.maximalUnramifiedField_le_of_le hLK)
  have h₄₃ : p₄ - p₃ ∈ U := by
    exact D.frobeniusPrimeDifference_mem_infiniteUnitAddSubgroup
      A v K L hLK σ₄ σ₃ π₄ π₃ hπ₄ hπ₃
  have h₁₃ : p₁ - p₃ ∈ U := by
    exact D.frobeniusPrimeDifference_mem_infiniteUnitAddSubgroup
      A v K L hLK σ₁ σ₃ π₁ π₃ hπ₁ hπ₃
  have h₃action : p₃ - D.frobeniusQuotientAction A KR.field L hLK
      (φ.1 ^ n₄) p₃ ∈ U := by
    exact D.frobeniusPrime_actionDifference_mem_infiniteUnitAddSubgroup
      A v K L hLK σ₃ π₃ hπ₃ (φ.1 ^ n₄)
  have h₁shift : p₁ - D.frobeniusQuotientAction A KR.field L hLK
      (φ.1 ^ n₄) p₃ ∈ U := by
    have heq : p₁ - D.frobeniusQuotientAction A KR.field L hLK
        (φ.1 ^ n₄) p₃ = (p₁ - p₃) +
          (p₃ - D.frobeniusQuotientAction A KR.field L hLK
            (φ.1 ^ n₄) p₃) := by
      abel
    rw [heq]
    exact U.add_mem h₁₃ h₃action
  have hn₃ : n₃ = n₄ + n₁ := by
    simp [n₁, n₃, n₄, σ₃, σ₄, Nat.add_comm]
  let u := D.frobeniusPowerSum A KR.field L hLK φ.1 n₄ p₄ +
    D.frobeniusPowerSum A KR.field L hLK φ.1 n₁ p₁ -
    D.frobeniusPowerSum A KR.field L hLK φ.1 n₃ p₃
  have huEq : u =
      D.frobeniusPowerSum A KR.field L hLK φ.1 n₄ (p₄ - p₃) +
      D.frobeniusPowerSum A KR.field L hLK φ.1 n₁
        (p₁ - D.frobeniusQuotientAction A KR.field L hLK
          (φ.1 ^ n₄) p₃) := by
    dsimp [u]
    rw [D.frobeniusPowerSum_sub_universalNormDescent,
      D.frobeniusPowerSum_sub_universalNormDescent, hn₃,
      D.frobeniusPowerSum_add]
    abel
  have hsum₄₃ : D.frobeniusPowerSum A KR.field L hLK φ.1 n₄
      (p₄ - p₃) ∈ U :=
    v.frobeniusPowerSum_mem_infiniteUnit_universalNormDescent
      K L hLK φ.1 n₄ (p₄ - p₃) h₄₃
  have hsum₁ : D.frobeniusPowerSum A KR.field L hLK φ.1 n₁
      (p₁ - D.frobeniusQuotientAction A KR.field L hLK
        (φ.1 ^ n₄) p₃) ∈ U :=
    v.frobeniusPowerSum_mem_infiniteUnit_universalNormDescent
      K L hLK φ.1 n₁ _ h₁shift
  rw [show D.frobeniusPowerSum A KR.field L hLK φ.1 n₄ p₄ +
      D.frobeniusPowerSum A KR.field L hLK φ.1 n₁ p₁ -
      D.frobeniusPowerSum A KR.field L hLK φ.1 n₃ p₃ = u from rfl,
    huEq]
  exact U.add_mem hsum₄₃ hsum₁

/-- Each of the three correction coefficients in the group-ring
identity is a finite-stage unit.  In the left-action translation the
product is `τ₄τ₁`, so the third coefficient is `p₃-τ₁p₃`; it is
acted on by `τ₄` in `frobeniusMultiplicativityCorrectionAction`. -/
theorem frobeniusCorrectionTerms_mem_infiniteUnitAddSubgroup
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (φ σ₁ σ₂ : D.FrobeniusElements
      (K.toFiniteResidueAbstractField D) L hLK)
    (π₁ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK σ₁))
    (π₃ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK
        (σ₁ * σ₂)))
    (π₄ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK
        (D.frobeniusActionConjugate (K.toFiniteResidueAbstractField D)
          L hLK φ σ₂
          (D.frobeniusExponent (K.toFiniteResidueAbstractField D)
            L hLK σ₁))))
    (hπ₁ :
      let KR := K.toFiniteResidueAbstractField D
      let Sigma1 : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK σ₁,
          D.frobeniusFixedField_absoluteFinite K L hLK σ₁⟩
      v.IsPrimeElement Sigma1 π₁)
    (hπ₃ :
      let KR := K.toFiniteResidueAbstractField D
      let Sigma3 : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK (σ₁ * σ₂),
          D.frobeniusFixedField_absoluteFinite K L hLK (σ₁ * σ₂)⟩
      v.IsPrimeElement Sigma3 π₃)
    (hπ₄ :
      let KR := K.toFiniteResidueAbstractField D
      let σ₄ := D.frobeniusActionConjugate KR L hLK φ σ₂
        (D.frobeniusExponent KR L hLK σ₁)
      let Sigma4 : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK σ₄,
          D.frobeniusFixedField_absoluteFinite K L hLK σ₄⟩
      v.IsPrimeElement Sigma4 π₄) :
    let KR := K.toFiniteResidueAbstractField D
    let σ₃ := σ₁ * σ₂
    let σ₄ := D.frobeniusActionConjugate KR L hLK φ σ₂
      (D.frobeniusExponent KR L hLK σ₁)
    let p₁ := fixedFieldInclusion A
      (D.frobeniusFixedField KR L hLK σ₁)
      (D.maximalUnramifiedField L)
      (D.fieldInertia_le_frobeniusFixedField KR L hLK σ₁) π₁
    let p₃ := fixedFieldInclusion A
      (D.frobeniusFixedField KR L hLK σ₃)
      (D.maximalUnramifiedField L)
      (D.fieldInertia_le_frobeniusFixedField KR L hLK σ₃) π₃
    let p₄ := fixedFieldInclusion A
      (D.frobeniusFixedField KR L hLK σ₄)
      (D.maximalUnramifiedField L)
      (D.fieldInertia_le_frobeniusFixedField KR L hLK σ₄) π₄
    let τ₁ := D.frobeniusActionRemainder KR L hLK φ σ₁
    ∀ i : Fin 3,
      (![p₄ - p₃, p₁ - p₃,
          p₃ - D.frobeniusQuotientAction A KR.field L hLK τ₁ p₃] :
        Fin 3 → ambientFixedAddSubgroup A
          (D.maximalUnramifiedField L)) i ∈
        v.infiniteUnitAddSubgroup (D.maximalUnramifiedField L) K
      (D.maximalUnramifiedField_le_of_le hLK) := by
  dsimp only
  let KR := K.toFiniteResidueAbstractField D
  let hLnormalKR : (extensionSubgroup KR.field L hLK).Normal := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal
  let hLfiniteKR : Finite
      (KR.field.toSubgroup ⧸ extensionSubgroup KR.field L hLK) := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLfinite
  let σ₃ := σ₁ * σ₂
  let σ₄ := D.frobeniusActionConjugate KR L hLK φ σ₂
    (D.frobeniusExponent KR L hLK σ₁)
  let p₁ := fixedFieldInclusion A
    (D.frobeniusFixedField KR L hLK σ₁)
    (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField KR L hLK σ₁) π₁
  let p₃ := fixedFieldInclusion A
    (D.frobeniusFixedField KR L hLK σ₃)
    (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField KR L hLK σ₃) π₃
  let p₄ := fixedFieldInclusion A
    (D.frobeniusFixedField KR L hLK σ₄)
    (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField KR L hLK σ₄) π₄
  let τ₁ := D.frobeniusActionRemainder KR L hLK φ σ₁
  have h₄₃ := D.frobeniusPrimeDifference_mem_infiniteUnitAddSubgroup
    A v K L hLK σ₄ σ₃ π₄ π₃ hπ₄ hπ₃
  have h₁₃ := D.frobeniusPrimeDifference_mem_infiniteUnitAddSubgroup
    A v K L hLK σ₁ σ₃ π₁ π₃ hπ₁ hπ₃
  have h₃action :=
    D.frobeniusPrime_actionDifference_mem_infiniteUnitAddSubgroup
      A v K L hLK σ₃ π₃ hπ₃ τ₁
  intro i
  fin_cases i
  · change p₄ - p₃ ∈ _
    exact h₄₃
  · change p₁ - p₃ ∈ _
    exact h₁₃
  · change p₃ - D.frobeniusQuotientAction A KR.field L hLK τ₁ p₃ ∈ _
    exact h₃action


end DegreeData

end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_MainMultiplicativity_FrobeniusPowerSumRelation
attribute [-instance] _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The Frobenius power-sum relation for reciprocity multiplicativity

This file proves the three-term action identity obtained from the Frobenius
action remainders and their associated fixed-field prime elements.
-/

universe u

namespace ClassFormation

open KummerTheory
open CyclicCohomology

noncomputable section

open CategoryTheory

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The three Frobenius power sums attached to `σ₁`, `σ₁σ₂`, and the
left-action conjugate of `σ₂` satisfy the action-difference relation used by
universal norm descent. -/
theorem frobeniusPowerSum_mul_action_sub (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ σ₁ σ₂ : D.FrobeniusElements K L hLK)
    (π₁ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ₁))
    (π₃ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK (σ₁ * σ₂)))
    (π₄ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK
        (D.frobeniusActionConjugate K L hLK φ σ₂
          (D.frobeniusExponent K L hLK σ₁)))) :
    let σ₃ := σ₁ * σ₂
    let σ₄ := D.frobeniusActionConjugate K L hLK φ σ₂
      (D.frobeniusExponent K L hLK σ₁)
    let p₁ := fixedFieldInclusion A
      (D.frobeniusFixedField K L hLK σ₁)
      (D.maximalUnramifiedField L)
      (D.fieldInertia_le_frobeniusFixedField K L hLK σ₁) π₁
    let p₃ := fixedFieldInclusion A
      (D.frobeniusFixedField K L hLK σ₃)
      (D.maximalUnramifiedField L)
      (D.fieldInertia_le_frobeniusFixedField K L hLK σ₃) π₃
    let p₄ := fixedFieldInclusion A
      (D.frobeniusFixedField K L hLK σ₄)
      (D.maximalUnramifiedField L)
      (D.fieldInertia_le_frobeniusFixedField K L hLK σ₄) π₄
    let τ₁ := D.frobeniusActionRemainder K L hLK φ σ₁
    let τ₄ := D.frobeniusActionRemainder K L hLK φ σ₄
    let u := D.frobeniusPowerSum A K.field L hLK φ.1
        (D.frobeniusExponent K L hLK σ₄) p₄ +
      D.frobeniusPowerSum A K.field L hLK φ.1
        (D.frobeniusExponent K L hLK σ₁) p₁ -
      D.frobeniusPowerSum A K.field L hLK φ.1
        (D.frobeniusExponent K L hLK σ₃) p₃
    D.frobeniusQuotientAction A K.field L hLK φ.1 u - u =
      (D.frobeniusQuotientAction A K.field L hLK τ₄ p₄ - p₄) +
      (D.frobeniusQuotientAction A K.field L hLK τ₁ p₁ - p₁) +
      (p₃ - D.frobeniusQuotientAction A K.field L hLK (τ₄ * τ₁) p₃) := by
  let σ₃ := σ₁ * σ₂
  let σ₄ := D.frobeniusActionConjugate K L hLK φ σ₂
    (D.frobeniusExponent K L hLK σ₁)
  let p₁ := fixedFieldInclusion A
    (D.frobeniusFixedField K L hLK σ₁)
    (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField K L hLK σ₁) π₁
  let p₃ := fixedFieldInclusion A
    (D.frobeniusFixedField K L hLK σ₃)
    (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField K L hLK σ₃) π₃
  let p₄ := fixedFieldInclusion A
    (D.frobeniusFixedField K L hLK σ₄)
    (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField K L hLK σ₄) π₄
  let s₁ := D.frobeniusPowerSum A K.field L hLK φ.1
    (D.frobeniusExponent K L hLK σ₁) p₁
  let s₃ := D.frobeniusPowerSum A K.field L hLK φ.1
    (D.frobeniusExponent K L hLK σ₃) p₃
  let s₄ := D.frobeniusPowerSum A K.field L hLK φ.1
    (D.frobeniusExponent K L hLK σ₄) p₄
  let τ₁ := D.frobeniusActionRemainder K L hLK φ σ₁
  let τ₃ := D.frobeniusActionRemainder K L hLK φ σ₃
  let τ₄ := D.frobeniusActionRemainder K L hLK φ σ₄
  have h₁ :
      D.frobeniusQuotientAction A K.field L hLK τ₁ p₁ =
        D.frobeniusQuotientAction A K.field L hLK
          (φ.1 ^ D.frobeniusExponent K L hLK σ₁) p₁ := by
    exact D.frobeniusActionRemainder_apply_fixedField
      A K L hLK φ σ₁ π₁
  have h₃ :
      D.frobeniusQuotientAction A K.field L hLK τ₃ p₃ =
        D.frobeniusQuotientAction A K.field L hLK
          (φ.1 ^ D.frobeniusExponent K L hLK σ₃) p₃ := by
    exact D.frobeniusActionRemainder_apply_fixedField
      A K L hLK φ σ₃ π₃
  have h₄ :
      D.frobeniusQuotientAction A K.field L hLK τ₄ p₄ =
        D.frobeniusQuotientAction A K.field L hLK
          (φ.1 ^ D.frobeniusExponent K L hLK σ₄) p₄ := by
    exact D.frobeniusActionRemainder_apply_fixedField
      A K L hLK φ σ₄ π₄
  have hτ : τ₃ = τ₄ * τ₁ := by
    exact D.frobeniusActionRemainder_mul K L hLK φ σ₁ σ₂
  change
    D.frobeniusQuotientAction A K.field L hLK φ.1
          (s₄ + s₁ - s₃) - (s₄ + s₁ - s₃) =
      (D.frobeniusQuotientAction A K.field L hLK τ₄ p₄ - p₄) +
        (D.frobeniusQuotientAction A K.field L hLK τ₁ p₁ - p₁) +
        (p₃ -
          D.frobeniusQuotientAction A K.field L hLK (τ₄ * τ₁) p₃)
  have hmap :
      D.frobeniusQuotientAction A K.field L hLK φ.1 (s₄ + s₁ - s₃) =
        D.frobeniusQuotientAction A K.field L hLK φ.1 s₄ +
          D.frobeniusQuotientAction A K.field L hLK φ.1 s₁ -
          D.frobeniusQuotientAction A K.field L hLK φ.1 s₃ := by
    change
      D.frobeniusQuotientActionLinearMap A K.field L hLK φ.1
          (s₄ + s₁ - s₃) =
        D.frobeniusQuotientActionLinearMap A K.field L hLK φ.1 s₄ +
          D.frobeniusQuotientActionLinearMap A K.field L hLK φ.1 s₁ -
          D.frobeniusQuotientActionLinearMap A K.field L hLK φ.1 s₃
    rw [map_sub, map_add]
  rw [hmap]
  calc
    _ =
        (D.frobeniusQuotientAction A K.field L hLK φ.1 s₄ - s₄) +
          (D.frobeniusQuotientAction A K.field L hLK φ.1 s₁ - s₁) -
          (D.frobeniusQuotientAction A K.field L hLK φ.1 s₃ - s₃) := by
      abel
    _ =
        (D.frobeniusQuotientAction A K.field L hLK
            (φ.1 ^ D.frobeniusExponent K L hLK σ₄) p₄ - p₄) +
          (D.frobeniusQuotientAction A K.field L hLK
            (φ.1 ^ D.frobeniusExponent K L hLK σ₁) p₁ - p₁) -
          (D.frobeniusQuotientAction A K.field L hLK
            (φ.1 ^ D.frobeniusExponent K L hLK σ₃) p₃ - p₃) := by
      dsimp only [s₁, s₃, s₄]
      rw [D.frobeniusPowerSum_action_sub,
        D.frobeniusPowerSum_action_sub,
        D.frobeniusPowerSum_action_sub]
    _ =
        (D.frobeniusQuotientAction A K.field L hLK τ₄ p₄ - p₄) +
          (D.frobeniusQuotientAction A K.field L hLK τ₁ p₁ - p₁) +
          (p₃ -
            D.frobeniusQuotientAction A K.field L hLK (τ₄ * τ₁) p₃) := by
      rw [← h₄, ← h₁, ← h₃, hτ]
      abel

end DegreeData

end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_MainMultiplicativity_NormClassRelation
attribute [-instance] _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Norm-class relations for reciprocity multiplicativity

This file passes the alternating Frobenius power-sum norm relation to the
maximal-unramified norm quotient and then to the reciprocity map.
-/

universe u

namespace ClassFormation

open KummerTheory
open CyclicCohomology

noncomputable section

open CategoryTheory

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Applying the relative norm from the maximal unramified extension to the
alternating Frobenius power sum gives the alternating sum of the three
finite fixed-field norms. -/
theorem relativeNorm_frobeniusPowerSum_alternating
    (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (φ σ₁ σ₂ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (π₁ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ₁))
    (π₃ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK (σ₁ * σ₂)))
    (π₄ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK
        (D.frobeniusActionConjugate K L hLK φ σ₂
          (D.frobeniusExponent K L hLK σ₁)))) :
    let σ₃ := σ₁ * σ₂
    let σ₄ := D.frobeniusActionConjugate K L hLK φ σ₂
      (D.frobeniusExponent K L hLK σ₁)
    let S₁ := D.frobeniusFixedField K L hLK σ₁
    let S₃ := D.frobeniusFixedField K L hLK σ₃
    let S₄ := D.frobeniusFixedField K L hLK σ₄
    let hS₁K := D.frobeniusFixedField_le K L hLK σ₁
    let hS₃K := D.frobeniusFixedField_le K L hLK σ₃
    let hS₄K := D.frobeniusFixedField_le K L hLK σ₄
    let p₁ := fixedFieldInclusion A S₁ (D.maximalUnramifiedField L)
      (D.fieldInertia_le_frobeniusFixedField K L hLK σ₁) π₁
    let p₃ := fixedFieldInclusion A S₃ (D.maximalUnramifiedField L)
      (D.fieldInertia_le_frobeniusFixedField K L hLK σ₃) π₃
    let p₄ := fixedFieldInclusion A S₄ (D.maximalUnramifiedField L)
      (D.fieldInertia_le_frobeniusFixedField K L hLK σ₄) π₄
    let u := D.frobeniusPowerSum A K.field L hLK φ.1
        (D.frobeniusExponent K L hLK σ₄) p₄ +
      D.frobeniusPowerSum A K.field L hLK φ.1
        (D.frobeniusExponent K L hLK σ₁) p₁ -
      D.frobeniusPowerSum A K.field L hLK φ.1
        (D.frobeniusExponent K L hLK σ₃) p₃
    letI : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field S₁ hS₁K) :=
      D.frobeniusFixedField_finite K L hLK σ₁
    letI : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field S₃ hS₃K) :=
      D.frobeniusFixedField_finite K L hLK σ₃
    letI : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field S₄ hS₄K) :=
      D.frobeniusFixedField_finite K L hLK σ₄
    letI : Finite
        ((D.maximalUnramifiedField K.field).toSubgroup ⧸
          extensionSubgroup (D.maximalUnramifiedField K.field)
            (D.maximalUnramifiedField L)
            (D.maximalUnramifiedField_mono hLK)) :=
      D.maximalUnramifiedExtension_finite K.field L hLK
    ((relativeNorm A (D.maximalUnramifiedField K.field)
      (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) u :
        ambientFixedAddSubgroup A (D.maximalUnramifiedField K.field)) : A.V) =
      ((relativeNorm A K.field S₄ hS₄K π₄ +
        relativeNorm A K.field S₁ hS₁K π₁ -
        relativeNorm A K.field S₃ hS₃K π₃ :
          ambientFixedAddSubgroup A K.field) : A.V) := by
  dsimp only
  let σ₃ := σ₁ * σ₂
  let σ₄ := D.frobeniusActionConjugate K L hLK φ σ₂
    (D.frobeniusExponent K L hLK σ₁)
  let S₁ := D.frobeniusFixedField K L hLK σ₁
  let S₃ := D.frobeniusFixedField K L hLK σ₃
  let S₄ := D.frobeniusFixedField K L hLK σ₄
  let hS₁K := D.frobeniusFixedField_le K L hLK σ₁
  let hS₃K := D.frobeniusFixedField_le K L hLK σ₃
  let hS₄K := D.frobeniusFixedField_le K L hLK σ₄
  let p₁ := fixedFieldInclusion A S₁ (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField K L hLK σ₁) π₁
  let p₃ := fixedFieldInclusion A S₃ (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField K L hLK σ₃) π₃
  let p₄ := fixedFieldInclusion A S₄ (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField K L hLK σ₄) π₄
  let s₁ := D.frobeniusPowerSum A K.field L hLK φ.1
    (D.frobeniusExponent K L hLK σ₁) p₁
  let s₃ := D.frobeniusPowerSum A K.field L hLK φ.1
    (D.frobeniusExponent K L hLK σ₃) p₃
  let s₄ := D.frobeniusPowerSum A K.field L hLK φ.1
    (D.frobeniusExponent K L hLK σ₄) p₄
  let u := s₄ + s₁ - s₃
  let hS₁finite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field S₁ hS₁K) :=
    D.frobeniusFixedField_finite K L hLK σ₁
  let hS₃finite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field S₃ hS₃K) :=
    D.frobeniusFixedField_finite K L hLK σ₃
  let hS₄finite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field S₄ hS₄K) :=
    D.frobeniusFixedField_finite K L hLK σ₄
  let hIfinite : Finite
      ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) :=
    D.maximalUnramifiedExtension_finite K.field L hLK
  have h₁ := (D.frobeniusNormIdentities A K L hLK φ σ₁ hφ π₁).1
  have h₃ := (D.frobeniusNormIdentities A K L hLK φ σ₃ hφ π₃).1
  have h₄ := (D.frobeniusNormIdentities A K L hLK φ σ₄ hφ π₄).1
  let N := relativeNorm A (D.maximalUnramifiedField K.field)
    (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
  change ((N (s₄ + s₁ - s₃) :
      ambientFixedAddSubgroup A (D.maximalUnramifiedField K.field)) : A.V) = _
  rw [map_sub, map_add]
  change (N s₄).1 + (N s₁).1 - (N s₃).1 = _
  rw [← h₄, ← h₁, ← h₃]
  rfl

/-- Final quotient step in reciprocity multiplicativity.  Once the maximal-unramified
norm of `u` descends to a universal norm in `A_K`, the alternating norm
relation is exactly the desired equality of reciprocity classes. -/
theorem maximalUnramifiedNormClass_add_eq_of_relativeNorm
    (D : DegreeData G) (A : Rep ℤ G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    [Finite
      ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK))]
    (r₁ r₂ r₃ : ambientFixedAddSubgroup A K.field)
    (u : ambientFixedAddSubgroup A (D.maximalUnramifiedField L))
    (hnorm :
      ((relativeNorm A (D.maximalUnramifiedField K.field)
        (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) u :
          ambientFixedAddSubgroup A (D.maximalUnramifiedField K.field)) : A.V) =
        ((r₁ + r₂ - r₃ : ambientFixedAddSubgroup A K.field) : A.V))
    (huniversal : ∃ aK : ambientFixedAddSubgroup A K.field,
      fixedFieldInclusion A K.field (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField_le K.field) aK =
        relativeNorm A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) u ∧
      aK ∈ D.maximalUnramifiedNormSubgroup A K.field L) :
    D.maximalUnramifiedNormClass A K.field L r₁ +
        D.maximalUnramifiedNormClass A K.field L r₂ =
      D.maximalUnramifiedNormClass A K.field L r₃ := by
  obtain ⟨aK, hdescend, haK⟩ := huniversal
  have hsum : r₁ + r₂ - r₃ = aK := by
    apply Subtype.ext
    exact hnorm.symm.trans (congrArg Subtype.val hdescend).symm
  have hmem : r₁ + r₂ - r₃ ∈
      D.maximalUnramifiedNormSubgroup A K.field L := by
    rw [hsum]
    exact haK
  have hzero := (D.maximalUnramifiedNormClass_eq_zero_iff
    A K.field L (r₁ + r₂ - r₃)).2 hmem
  rw [map_sub, map_add] at hzero
  exact sub_eq_zero.mp hzero

/-- Prime-choice independence converts an equality of the three explicit
norm classes into reciprocity multiplicativity's equality for the canonical reciprocity
map. -/
theorem reciprocityMap_mul_of_primeNormClass_eq
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (σ₁ σ₂ : D.FrobeniusElements
      (K.toFiniteResidueAbstractField D) L hLK)
    (π₁ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK σ₁))
    (π₂ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK σ₂))
    (π₃ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK
        (σ₁ * σ₂)))
    (hπ₁ :
      let KR := K.toFiniteResidueAbstractField D
      let Sigma1 : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK σ₁,
          D.frobeniusFixedField_absoluteFinite K L hLK σ₁⟩
      v.IsPrimeElement Sigma1 π₁)
    (hπ₂ :
      let KR := K.toFiniteResidueAbstractField D
      let Sigma2 : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK σ₂,
          D.frobeniusFixedField_absoluteFinite K L hLK σ₂⟩
      v.IsPrimeElement Sigma2 π₂)
    (hπ₃ :
      let KR := K.toFiniteResidueAbstractField D
      let Sigma3 : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK (σ₁ * σ₂),
          D.frobeniusFixedField_absoluteFinite K L hLK (σ₁ * σ₂)⟩
      v.IsPrimeElement Sigma3 π₃)
    (hclasses :
      let KR := K.toFiniteResidueAbstractField D
      let S₁ := D.frobeniusFixedField KR L hLK σ₁
      let S₂ := D.frobeniusFixedField KR L hLK σ₂
      let S₃ := D.frobeniusFixedField KR L hLK (σ₁ * σ₂)
      let hS₁K := D.frobeniusFixedField_le KR L hLK σ₁
      let hS₂K := D.frobeniusFixedField_le KR L hLK σ₂
      let hS₃K := D.frobeniusFixedField_le KR L hLK (σ₁ * σ₂)
      letI : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field S₁ hS₁K) :=
        D.frobeniusFixedField_finite KR L hLK σ₁
      letI : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field S₂ hS₂K) :=
        D.frobeniusFixedField_finite KR L hLK σ₂
      letI : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field S₃ hS₃K) :=
        D.frobeniusFixedField_finite KR L hLK (σ₁ * σ₂)
      D.maximalUnramifiedNormClass A K.field L
          (relativeNorm A K.field S₁ hS₁K π₁) +
        D.maximalUnramifiedNormClass A K.field L
          (relativeNorm A K.field S₂ hS₂K π₂) =
        D.maximalUnramifiedNormClass A K.field L
          (relativeNorm A K.field S₃ hS₃K π₃)) :
    D.reciprocityMap A v K L hLK (σ₁ * σ₂) =
      D.reciprocityMap A v K L hLK σ₁ +
        D.reciprocityMap A v K L hLK σ₂ := by
  let KR := K.toFiniteResidueAbstractField D
  let hLnormalKR : (extensionSubgroup KR.field L hLK).Normal := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal
  let hLfiniteKR : Finite
      (KR.field.toSubgroup ⧸ extensionSubgroup KR.field L hLK) := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLfinite
  let hS₁finite : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field
      (D.frobeniusFixedField KR L hLK σ₁)
      (D.frobeniusFixedField_le KR L hLK σ₁)) :=
    D.frobeniusFixedField_finite KR L hLK σ₁
  let hS₂finite : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field
      (D.frobeniusFixedField KR L hLK σ₂)
      (D.frobeniusFixedField_le KR L hLK σ₂)) :=
    D.frobeniusFixedField_finite KR L hLK σ₂
  let hS₃finite : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field
      (D.frobeniusFixedField KR L hLK (σ₁ * σ₂))
      (D.frobeniusFixedField_le KR L hLK (σ₁ * σ₂))) :=
    D.frobeniusFixedField_finite KR L hLK (σ₁ * σ₂)
  have h₁ := D.reciprocityValueOfPrime_eq_reciprocityMap
    A v hAxiom K L hLK σ₁ π₁ hπ₁
  have h₂ := D.reciprocityValueOfPrime_eq_reciprocityMap
    A v hAxiom K L hLK σ₂ π₂ hπ₂
  have h₃ := D.reciprocityValueOfPrime_eq_reciprocityMap
    A v hAxiom K L hLK (σ₁ * σ₂) π₃ hπ₃
  rw [← h₃, ← h₁, ← h₂]
  simpa only [reciprocityValueOfPrime, KR,
    FiniteAbstractField.toFiniteResidueAbstractField] using hclasses.symm

end DegreeData

end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_MainFiniteReciprocity
attribute [-instance] _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.mem_normFilterBasis_iff _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

universe u

namespace ClassFormation

open KummerTheory

open CyclicCohomology

open CategoryTheory
open scoped BigOperators


/-!
# The abstract reciprocity construction, the finite reciprocity equivalence

This file carries out the descent preparation.  The reciprocity
value on the Frobenius semigroup is first mapped to the finite norm quotient.
We then compare two lifts by their positive Frobenius exponents, construct
the degree-zero quotient between unequal lifts, and prove that this quotient
has zero finite reciprocity value.  Finally reciprocity multiplicativity supplies
additivity on the Frobenius semigroup, so the lift supplied by the finite degree-quotient decomposition descends to the additive reciprocity homomorphism of the finite reciprocity equivalence.
-/

noncomputable section

section finiteReciprocityValues

/-! Mathlib's `Rep ℤ G` forces its representation-bearing group `G` to `Type 0`. -/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The reciprocity value of a Frobenius element after passage from the
universal norm quotient to the finite quotient by `N_{L/K} A_L`. -/
def finiteReciprocityValue (D : DegreeData G) (A : Rep ℤ G)
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (σ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK) :
    FiniteNormQuotient A K.field L hLK :=
  D.maximalUnramifiedToFiniteNormQuotient A K.field L hLK
    (D.reciprocityMap A v K L hLK σ)

end DegreeData

end finiteReciprocityValues

section frobeniusLiftAlgebra

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The quotient between two Frobenius lifts when the exponent of the first
is strictly smaller.  Its exponent is the positive difference. -/
def frobeniusLiftDifference (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ τ : D.FrobeniusElements K L hLK)
    (hdegree : D.frobeniusExponent K L hLK σ <
      D.frobeniusExponent K L hLK τ) :
    D.FrobeniusElements K L hLK := by
  let nσ := D.frobeniusExponent K L hLK σ
  let nτ := D.frobeniusExponent K L hLK τ
  let m := nτ - nσ
  have hm : 0 < m := Nat.sub_pos_of_lt hdegree
  refine ⟨σ.1⁻¹ * τ.1, m, hm, ?_⟩
  rw [map_mul, map_inv,
    D.extensionNormalizedDegree_frobenius_eq_pow K L hLK σ,
    D.extensionNormalizedDegree_frobenius_eq_pow K L hLK τ]
  have hle : nσ ≤ nτ := Nat.le_of_lt hdegree
  change ((Multiplicative.ofAdd (1 : ZHat) : ZHatMul) ^ nσ)⁻¹ *
      (Multiplicative.ofAdd (1 : ZHat) : ZHatMul) ^ nτ =
    (Multiplicative.ofAdd (1 : ZHat) : ZHatMul) ^ m
  rw [← Nat.add_sub_of_le hle, pow_add]
  simp [m]

/-- The difference of two Frobenius lifts coerces to their ambient quotient difference. -/
@[simp]
theorem frobeniusLiftDifference_coe (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ τ : D.FrobeniusElements K L hLK)
    (hdegree : D.frobeniusExponent K L hLK σ <
      D.frobeniusExponent K L hLK τ) :
    (D.frobeniusLiftDifference K L hLK σ τ hdegree).1 =
      σ.1⁻¹ * τ.1 :=
  by simp [frobeniusLiftDifference]

/-- Multiplying the smaller lift by its quotient recovers the larger lift. -/
theorem mul_frobeniusLiftDifference (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ τ : D.FrobeniusElements K L hLK)
    (hdegree : D.frobeniusExponent K L hLK σ <
      D.frobeniusExponent K L hLK τ) :
    σ * D.frobeniusLiftDifference K L hLK σ τ hdegree = τ := by
  apply Subtype.ext
  rw [frobeniusMul_coe, frobeniusLiftDifference_coe]
  simp

end DegreeData

end frobeniusLiftAlgebra

section trivialRestrictionValues

/-! Mathlib's `Rep ℤ G` forces its representation-bearing group `G` to `Type 0`. -/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- A Frobenius lift restricting trivially to `L` has zero value in the
finite norm quotient. Its fixed field contains `L`, so its norm to `K` factors through
`N_{L/K}`. -/
theorem finiteReciprocityValue_eq_zero_of_restriction_eq_one
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (σ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK)
    (hσ : D.frobeniusRestriction
      (K.toFiniteResidueAbstractField D) L hLK σ = 1) :
    D.finiteReciprocityValue A v K L hLK σ = 0 := by
  let KR := K.toFiniteResidueAbstractField D
  let hLnormalKR : (extensionSubgroup KR.field L hLK).Normal := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal
  let S := D.frobeniusFixedField KR L hLK σ
  let hSK : S.toSubgroup ≤ K.field.toSubgroup :=
    D.frobeniusFixedField_le KR L hLK σ
  let hSL : S.toSubgroup ≤ L.toSubgroup :=
    D.frobeniusFixedField_le_of_restriction_eq_one
      KR L hLK σ hσ
  let hSfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field S hSK) :=
    D.frobeniusFixedField_finite KR L hLK σ
  let hSLfinite : Finite
      (L.toSubgroup ⧸ extensionSubgroup L S hSL) :=
    FiniteIntermediateField.finite_extension_of_le hSK hLK hSL
  let hSabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) S (le_baseField S)) :=
    D.frobeniusFixedField_absoluteFinite K L hLK σ
  let Sigma : FiniteAbstractField G := ⟨S, hSabsolute⟩
  rw [finiteReciprocityValue,
    D.reciprocityMap_eq_chosenPrime A v K L hLK σ]
  change D.maximalUnramifiedToFiniteNormQuotient A K.field L hLK
      (D.maximalUnramifiedNormClass A K.field L
        (relativeNorm A K.field S hSK (v.chosenPrimeElement Sigma))) = 0
  rw [D.maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClass]
  apply (finiteNormClass_eq_zero_iff A K.field L hLK _).2
  change relativeNorm A K.field S hSK (v.chosenPrimeElement Sigma) ∈
    (relativeNorm A K.field L hLK).range
  refine ⟨relativeNorm A L S hSL (v.chosenPrimeElement Sigma), ?_⟩
  let T : DegreeData.FiniteTower G :=
    { top := S
      middle := L
      base := K.field
      top_le_middle := hSL
      middle_le_base := hLK
      finiteTopQuotient := hSLfinite
      finiteBaseQuotient := hLfinite }
  exact T.norm_trans_apply A (v.chosenPrimeElement Sigma)

end DegreeData

end trivialRestrictionValues

section chosenFrobeniusLifts

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- A specified Frobenius lift of a finite Galois automorphism, chosen from
the surjectivity in the finite degree-quotient decomposition. -/
def chosenFiniteReciprocityFrobeniusLift (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (q : K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK) :
    D.FrobeniusElements K L hLK :=
  Classical.choose (D.frobeniusRestriction_surjective K L hLK q)

/-- The chosen finite-reciprocity Frobenius lift restricts to the prescribed Frobenius element. -/
@[simp]
theorem frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (q : K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK) :
    D.frobeniusRestriction K L hLK
      (D.chosenFiniteReciprocityFrobeniusLift K L hLK q) = q :=
  Classical.choose_spec (D.frobeniusRestriction_surjective K L hLK q)

end DegreeData

end chosenFrobeniusLifts

section finiteReciprocityHom

/-! Mathlib's `Rep ℤ G` forces its representation-bearing group `G` to `Type 0`. -/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The canonical candidate underlying the finite reciprocity equivalence, obtained by
choosing the finite degree-quotient decomposition lift and evaluating in the finite norm
quotient.  Lift-independence and additivity are reduced to the concrete
steps above and reciprocity multiplicativity, respectively. -/
def finiteReciprocityCandidate (D : DegreeData G) (A : Rep ℤ G)
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)] :
    Additive (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK) →
      FiniteNormQuotient A K.field L hLK :=
  fun q => D.finiteReciprocityValue A v K L hLK
    (D.chosenFiniteReciprocityFrobeniusLift
      (K.toFiniteResidueAbstractField D) L hLK q.toMul)

/-- The finite reciprocity candidate evaluates a norm class through its chosen Frobenius lift. -/
@[simp]
theorem finiteReciprocityCandidate_apply (D : DegreeData G) (A : Rep ℤ G)
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (q : Additive
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)) :
    D.finiteReciprocityCandidate A v K L hLK q =
      D.finiteReciprocityValue A v K L hLK
        (D.chosenFiniteReciprocityFrobeniusLift
          (K.toFiniteResidueAbstractField D) L hLK q.toMul) :=
  rfl

/-- The finite reciprocity candidate sends the zero norm class to the identity. -/
@[simp]
theorem finiteReciprocityCandidate_zero (D : DegreeData G) (A : Rep ℤ G)
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)] :
    D.finiteReciprocityCandidate A v K L hLK 0 = 0 := by
  apply D.finiteReciprocityValue_eq_zero_of_restriction_eq_one
  exact D.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift
    (K.toFiniteResidueAbstractField D) L hLK
      (1 : K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)

end DegreeData

end finiteReciprocityHom

/-!
# The abstract reciprocity construction, the unramified norm-quotient equivalence

This file proves the generator calculation in the unramified case: the finite reciprocity equivalence sends arithmetic Frobenius to the prime
class.  That class generates the finite norm quotient, so the resulting
reciprocity homomorphism is promoted to an additive equivalence.
-/

end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_NormQuotient
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue
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

/-- A homomorphism descended through the norm quotient agrees with the original homomorphism on
representatives. -/
@[simp]
theorem normQuotientLift_normClass {K L : Type u} {M : Type v} [Field K] [Field L]
    [Algebra K L] [Group M] (f : Kˣ →* M)
    (h : localNormSubgroup K L ≤ f.ker) (x : Kˣ) :
    normQuotientLift f h (normClass K L x) = f x := by
  rfl

/-- Identify a norm quotient with any concrete quotient once its defining
subgroup has been identified.  This is the sole public boundary for such
representation changes. -/
def normQuotientEquivOfSubgroupEq
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (N : Subgroup Kˣ) (h : localNormSubgroup K L = N) :
    NormQuotient K L ≃* Kˣ ⧸ N := by
  change (Kˣ ⧸ localNormSubgroup K L) ≃* (Kˣ ⧸ N)
  exact QuotientGroup.quotientMulEquivOfEq h

/-- After identifying the norm subgroup with another subgroup, a norm class maps to the
corresponding quotient class. -/
@[simp]
theorem normQuotientEquivOfSubgroupEq_normClass
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (N : Subgroup Kˣ) (h : localNormSubgroup K L = N) (x : Kˣ) :
    normQuotientEquivOfSubgroupEq K L N h (normClass K L x) =
      QuotientGroup.mk x := by
  change QuotientGroup.quotientMulEquivOfEq h (QuotientGroup.mk x) =
    QuotientGroup.mk x
  exact QuotientGroup.quotientMulEquivOfEq_mk h x

/-- Identify two norm quotients when their defining norm subgroups agree. -/
def normQuotientEquivOfNormSubgroupEq
    (K L M : Type u) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    (h : localNormSubgroup K L = localNormSubgroup K M) :
    NormQuotient K L ≃* NormQuotient K M := by
  change (Kˣ ⧸ localNormSubgroup K L) ≃* (Kˣ ⧸ localNormSubgroup K M)
  exact QuotientGroup.quotientMulEquivOfEq h

/-- An equality of norm subgroups identifies norm classes represented by the same base-field unit.
An equality of norm subgroups identifies norm classes represented by the same base-field unit. -/
@[simp]
theorem normQuotientEquivOfNormSubgroupEq_normClass
    (K L M : Type u) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    (h : localNormSubgroup K L = localNormSubgroup K M) (x : Kˣ) :
    normQuotientEquivOfNormSubgroupEq K L M h (normClass K L x) =
      normClass K M x := by
  change QuotientGroup.quotientMulEquivOfEq h (QuotientGroup.mk x) =
    QuotientGroup.mk x
  exact QuotientGroup.quotientMulEquivOfEq_mk h x

/-- First isomorphism theorem with an opaque norm quotient as its source. -/
def normQuotientEquivOfSurjective
    {K L : Type u} {M : Type v} [Field K] [Field L] [Algebra K L]
    [Group M] (f : Kˣ →* M) (hf : Function.Surjective f)
    (hker : f.ker = localNormSubgroup K L) : NormQuotient K L ≃* M := by
  change (Kˣ ⧸ localNormSubgroup K L) ≃* M
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)

/-- The first-isomorphism equivalence sends a norm class to the image of its representative. -/
@[simp]
theorem normQuotientEquivOfSurjective_normClass
    {K L : Type u} {M : Type v} [Field K] [Field L] [Algebra K L]
    [Group M] (f : Kˣ →* M) (hf : Function.Surjective f)
    (hker : f.ker = localNormSubgroup K L) (x : Kˣ) :
    normQuotientEquivOfSurjective f hf hker (normClass K L x) = f x := by
  change
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf))
        (QuotientGroup.mk x) = f x
  rw [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

/-! ### Surjectivity and equality refinements for norm quotients -/

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Completion_ChosenLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

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

noncomputable instance chosenFinitePlaceBaseValued
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    Valued
      (ChosenFinitePlaceBaseCompletion (K := K) w₀) ℝ≥0 :=
  finitePlaceCompletionValued
    (HeightOneSpectrum.adicAbv K w₀)
    (HeightOneSpectrum.isNonarchimedean_adicAbv K w₀)

noncomputable instance chosenFinitePlaceBaseValuativeRel
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    ValuativeRel
      (ChosenFinitePlaceBaseCompletion (K := K) w₀) :=
  finitePlaceCompletionValuativeRel
    (HeightOneSpectrum.adicAbv K w₀)
    (HeightOneSpectrum.isNonarchimedean_adicAbv K w₀)

noncomputable instance
    chosenFinitePlaceBaseValuationIsNontrivial
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    (Valued.v :
      Valuation
        (ChosenFinitePlaceBaseCompletion (K := K) w₀)
        ℝ≥0).IsNontrivial :=
  (inferInstance :
    (NormedField.valuation
      (K := ChosenFinitePlaceBaseCompletion (K := K) w₀)).IsNontrivial)

noncomputable instance chosenFinitePlaceBaseValuationCompatible
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    (Valued.v :
      Valuation
        (ChosenFinitePlaceBaseCompletion (K := K) w₀)
        ℝ≥0).Compatible :=
  Valuation.Compatible.ofValuation _

noncomputable instance
    chosenFinitePlaceBaseValuativeRelIsNontrivial
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    ValuativeRel.IsNontrivial
      (ChosenFinitePlaceBaseCompletion (K := K) w₀) :=
  (ValuativeRel.isNontrivial_iff_isNontrivial
    (Valued.v :
      Valuation
        (ChosenFinitePlaceBaseCompletion (K := K) w₀)
        ℝ≥0)).2 inferInstance

noncomputable instance chosenFinitePlaceBaseIsValuativeTopology
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    IsValuativeTopology
      (ChosenFinitePlaceBaseCompletion (K := K) w₀) :=
  isValuativeTopology_of_valued_ofValuation
    (ChosenFinitePlaceBaseCompletion (K := K) w₀) ℝ≥0

noncomputable instance
    chosenFinitePlaceBaseIsNonarchimedeanLocalField
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    IsNonarchimedeanLocalField
      (ChosenFinitePlaceBaseCompletion (K := K) w₀) :=
  { toIsValuativeTopology := inferInstance
    toLocallyCompactSpace := inferInstance
    toIsNontrivial := inferInstance }
end
end


