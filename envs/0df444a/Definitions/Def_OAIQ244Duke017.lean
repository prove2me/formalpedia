-- Prove2me | Definitions.Def_OAIQ244Duke017
-- name    : OAIQ244Duke017
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:17:48.465688+00:00
-- url     : https://prove2.me/theorems/24077f65-735b-44a6-bd1b-560e0a77acdc
-- title:
--   Definitions bundle OAIQ244Duke017 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 191 declarations of OpenAI's Lean: 50 definitions, 7 instances and 134 theorems. The definitions and types are `CyclicCohomology.cyclic_H1_iso_HminusOne`, `CyclicCohomology.fixedPiEquiv`, `CyclicCohomology.instMulDistribMulActionForall_solutions`, `CyclicCohomology.instMulDistribMulActionForall_solutions_1`, `CyclicCohomology.subgroupGeneratorOfGenerator`, `CyclicCohomology.unitsH1IsoTateHminusOne`, `FiniteIdeleGroup.fractionalIdeal`, `FiniteIdeleGroup.integralSubgroup`, `FiniteIdeleGroup.supportedAt`, `FiniteIdeleGroup.valuationVector`, `FiniteIdeleGroup.valuationVectorAdd`, `FiniteIdeleGroup.valuationVectorSection`, `FractionalIdealGroup.countVector`, `FractionalIdealGroup.factorization`, `FractionalIdealGroup.factorizationEquiv`, `FractionalIdealGroup.primePowerHom`, `IdeleGroup.finiteComponentContinuous`, `IdeleGroup.fractionalIdeal`, `IdeleGroup.idealClass`, `IdeleGroup.infiniteComponentContinuous`, `IdeleGroup.integralAtFinitePlaces`, `IdeleGroup.supportedAt`, `LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.principalUnitClassQuotientKerEquivClassOfLe`, `LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.principalUnitGradedPiece`, `LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.principalUnitGradedPieceEquivSubquotient`, `LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.principalUnitGradedPieceMk`, `LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.quotientModuloPrincipalUnitClassEquivQuotientOfLe`, `LocalFieldTheory.DiscreteValuationField.ValuedNorm.MapsFiltrationLevels`, `LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageClassInQuotient`, `LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageSubgroup`, `LocalFieldTheory.DiscreteValuationField.ValuedNorm.mapLevelOfMapsFiltrationLevels`, `LocalFieldTheory.DiscreteValuationField.ValuedNorm.principalUnitGradedPieceMapOfMapsFiltrationLevels`, `LocalFieldTheory.DiscreteValuationField.ValuedNorm.principalUnitSubquotientMapOfMapsFiltrationLevels`, `LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientMapOfMapsFiltrationLevels`, `LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange`, `LocalFieldTheory.localCompleteDVF`, `RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction`, `RelativeIdeleGroup.Cohomology.ideleClassNorm`, `RelativeIdeleGroup.Cohomology.instMulDistribMulActionAlgEquivClassGroup`, `RelativeIdeleGroup.Cohomology.principalIdeleMulDistribMulAction` and 10 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Idele_Basic`, `AlgebraicNumberTheory_Idele_ClassGroup_Core`, `AlgebraicNumberTheory_Idele_Cohomology_Herbrand`, `AlgebraicNumberTheory_Idele_Extension_BaseChange`, `AlgebraicNumberTheory_Idele_Extension_ClassGroup`, `AlgebraicNumberTheory_Idele_Extension_GaloisDescent`, `AlgebraicNumberTheory_Idele_IdealMap`, `AlgebraicNumberTheory_Idele_LocallyCompact`, `AlgebraicNumberTheory_Idele_SPlaces`, `AlgebraicNumberTheory_Idele_Topology`, `Cyclic_GaloisCohomology`, `Cyclic_Herbrand_HerbrandLowDegree_BinaryProduct`, `Cyclic_Herbrand_HerbrandLowDegree_Product`, `Cyclic_Herbrand_Induced`, `Cyclic_Herbrand_NormalBasisLattice`, `Cyclic_Herbrand_Permutation_Module`, `Cyclic_Herbrand_Product`, `LocalField_DiscreteValuationField_NormFiltration`, `LocalField_DiscreteValuationField_Units`, `LocalField_NonarchimedeanLocalField_FiniteExtensionCompleteDVF`, `LocalField_NonarchimedeanLocalField_IdealQuotients`, `LocalField_NonarchimedeanLocalField_PrincipalUnits`, `LocalField_NonarchimedeanLocalField_ResidueUnits`, `LocalField_NonarchimedeanLocalField_SeparableNormValuation`, `Valuation_DiscreteValuationField_Basic`, `Valuation_DiscreteValuationField_Complete`, `Valuation_DiscreteValuationField_FiniteExtension_Degree`, `Valuation_DiscreteValuationField_FiniteExtension_Uniqueness`, `Valuation_DiscreteValuationField_Henselian`, `Valuation_DiscreteValuationField_IntegralClosure`, `Valuation_DiscreteValuationField_ValuationExtension`, `Valuation_ValuedAdicComplete`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke000`, `OAIQ244Duke001`, `OAIQ244Duke002`, `OAIQ244Duke003`, `OAIQ244Duke004`, `OAIQ244Duke005` and `OAIQ244Duke006` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke027`, `OAIQ244Duke028`, `OAIQ244Duke029`, `OAIQ244Duke030`, `OAIQ244Duke031`, `OAIQ244Duke033`, `OAIQ244Duke034` and `OAIQ244Duke036`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.CharP.Subring
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.GroupWithZero.Action.Prod
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.LinearMap.Polynomial
import Mathlib.Algebra.Module.Shrink
import Mathlib.Algebra.Order.Hom.Units
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.FieldTheory.SeparableClosure
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
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RepresentationTheory.Homological.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RepresentationTheory.Homological.GroupHomology.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.Algebra.Valued.ValuativeRel
import Mathlib.Topology.Algebra.Valued.ValuedField
import Definitions.Def_OAIQ244Duke000
import Definitions.Def_OAIQ244Duke001
import Definitions.Def_OAIQ244Duke002
import Definitions.Def_OAIQ244Duke003
import Definitions.Def_OAIQ244Duke004
import Definitions.Def_OAIQ244Duke005
import Definitions.Def_OAIQ244Duke006

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Basic
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

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

namespace FiniteIdeleGroup

variable {K}

/-- A finite idele is a local integral unit at all but finitely many finite
places. -/
theorem eventually_mem_localUnits (a : FiniteIdeleGroup K) :
    ∀ᶠ v in Filter.cofinite,
      a v ∈ (v.adicCompletionIntegers K).units :=
  a.2

end FiniteIdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Extension_BaseChange
attribute [-instance] _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.RelativeIdeleGroup.classInclusion_mk _root_.RelativeIdeleGroup.classNorm_mk _root_.RelativeIdeleGroup.finiteComponent_coe _root_.RelativeIdeleGroup.infiniteComponent_coe _root_.RelativeIdeleGroup.scalarConjugation_baseAdele_apply _root_.intermediateAdeleInclusion_tmul _root_.relativeAdeleFiniteComponent_tmul _root_.relativeAdeleInfiniteComponent_tmul _root_.topFieldToOneStep_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

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

namespace RelativeIdeleGroup

/-- Reynolds averaging for the finite Galois action. -/
def galoisAverage
    (z : RelativeAdeleRing K L) :
    RelativeAdeleRing K L :=
  ((Fintype.card (L ≃ₐ[K] L) : K)⁻¹) •
    ∑ σ : L ≃ₐ[K] L, conjugation K L σ z

omit [NumberField L] in
theorem galoisAverage_eq_of_fixed
    [IsGalois K L]
    (z : RelativeAdeleRing K L)
    (hz : ∀ σ : L ≃ₐ[K] L,
      conjugation K L σ z = z) :
    galoisAverage K L z = z := by
  rw [galoisAverage]
  simp_rw [hz]
  rw [Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul K, ← mul_smul,
    inv_mul_cancel₀
      (Nat.cast_ne_zero.mpr Fintype.card_ne_zero),
    one_smul]

omit [NumberField L] in
theorem galoisAverage_tmul
    [IsGalois K L]
    (a : NumberField.AdeleRing (𝓞 K) K) (x : L) :
    galoisAverage K L (a ⊗ₜ[K] x) =
      adeleInclusion K L
        (a * algebraMap K
          (NumberField.AdeleRing (𝓞 K) K)
          ((Fintype.card (L ≃ₐ[K] L) : K)⁻¹ *
            Algebra.trace K L x)) := by
  rw [galoisAverage]
  simp_rw [conjugation_tmul]
  rw [← TensorProduct.tmul_sum,
    ← trace_eq_sum_automorphisms x]
  change
    ((Fintype.card (L ≃ₐ[K] L) : K)⁻¹) •
        (a ⊗ₜ[K]
          algebraMap K L (Algebra.trace K L x)) =
      (a * algebraMap K
        (NumberField.AdeleRing (𝓞 K) K)
        ((Fintype.card (L ≃ₐ[K] L) : K)⁻¹ *
          Algebra.trace K L x)) ⊗ₜ[K] 1
  rw [TensorProduct.smul_tmul',
    Algebra.algebraMap_eq_smul_one]
  rw [← TensorProduct.smul_tmul]
  congr 1
  simp [Algebra.smul_def, map_mul, mul_assoc, mul_comm]

omit [NumberField L] in
theorem galoisAverage_mem_adeleInclusion_range
    [IsGalois K L]
    (z : RelativeAdeleRing K L) :
    ∃ a : NumberField.AdeleRing (𝓞 K) K,
      adeleInclusion K L a = galoisAverage K L z := by
  induction z using OAI.tensorInductionOn with
  | tmul a x =>
      refine ⟨a * algebraMap K
        (NumberField.AdeleRing (𝓞 K) K)
        ((Fintype.card (L ≃ₐ[K] L) : K)⁻¹ *
          Algebra.trace K L x), ?_⟩
      exact (galoisAverage_tmul K L a x).symm
  | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      refine ⟨a + b, ?_⟩
      rw [map_add, ha, hb]
      simp [galoisAverage, Finset.sum_add_distrib,
        smul_add]

omit [NumberField L] in
theorem exists_adele_eq_of_galois_fixed
    [IsGalois K L]
    (z : RelativeAdeleRing K L)
    (hz : ∀ σ : L ≃ₐ[K] L,
      conjugation K L σ z = z) :
    ∃ a : NumberField.AdeleRing (𝓞 K) K,
      adeleInclusion K L a = z := by
  obtain ⟨a, ha⟩ :=
    galoisAverage_mem_adeleInclusion_range K L z
  exact ⟨a, ha.trans (galoisAverage_eq_of_fixed K L z hz)⟩

/-- The subgroup of relative ideles fixed by every Galois automorphism. -/
def galoisFixedSubgroup :
    Subgroup (RelativeIdeleGroup K L) := by
  letI := relativeIdeleMulDistribMulAction K L
  exact FixedPoints.subgroup (L ≃ₐ[K] L) (RelativeIdeleGroup K L)

omit [NumberField L] in
/-- In the canonical tensor-product presentation,
the fixed relative ideles are exactly the ideles of the base field. -/
theorem inclusion_range_eq_galoisFixedSubgroup
    [IsGalois K L] :
    (inclusion K L).range =
      galoisFixedSubgroup K L := by
  ext u
  constructor
  · rintro ⟨a, rfl⟩ σ
    exact smul_inclusion K L σ a
  · intro hu
    have hfixed :
        ∀ σ : L ≃ₐ[K] L,
          conjugation K L σ
              (u : RelativeAdeleRing K L) =
            (u : RelativeAdeleRing K L) := by
      intro σ
      exact congrArg Units.val (hu σ)
    obtain ⟨a, ha⟩ :=
      exists_adele_eq_of_galois_fixed K L
        (u : RelativeAdeleRing K L) hfixed
    have hfixedInv :
        ∀ σ : L ≃ₐ[K] L,
          conjugation K L σ
              ((u⁻¹ : RelativeIdeleGroup K L) :
                RelativeAdeleRing K L) =
            ((u⁻¹ : RelativeIdeleGroup K L) :
              RelativeAdeleRing K L) := by
      intro σ
      have huσ : conjugationIdele K L σ u = u := by
        simpa only [smul_def] using hu σ
      exact congrArg Units.val (by
        change conjugationIdele K L σ u⁻¹ = u⁻¹
        rw [map_inv, huσ])
    obtain ⟨b, hb⟩ :=
      exists_adele_eq_of_galois_fixed K L
        ((u⁻¹ : RelativeIdeleGroup K L) :
          RelativeAdeleRing K L) hfixedInv
    unfold adeleInclusion at ha hb
    change
      (Algebra.TensorProduct.includeLeft
        (R := K) (S := K)
        (A := NumberField.AdeleRing (𝓞 K) K) (B := L)) a =
          (u : RelativeAdeleRing K L) at ha
    change
      (Algebra.TensorProduct.includeLeft
        (R := K) (S := K)
        (A := NumberField.AdeleRing (𝓞 K) K) (B := L)) b =
          ((u⁻¹ : RelativeIdeleGroup K L) :
            RelativeAdeleRing K L) at hb
    let q : (NumberField.AdeleRing (𝓞 K) K)ˣ :=
      { val := a
        inv := b
        val_inv := by
          apply
            (Algebra.TensorProduct.includeLeft_injective
              (R := K) (S := K)
              (A := NumberField.AdeleRing (𝓞 K) K) (B := L)
              (FaithfulSMul.algebraMap_injective K L))
          rw [map_mul, ha, hb]
          exact u.val_inv
        inv_val := by
          apply
            (Algebra.TensorProduct.includeLeft_injective
              (R := K) (S := K)
              (A := NumberField.AdeleRing (𝓞 K) K) (B := L)
              (FaithfulSMul.algebraMap_injective K L))
          rw [map_mul, hb, ha]
          exact u.inv_val }
    refine ⟨(IdeleGroup.equivAdeleRingUnits
      (K := K)).symm q, ?_⟩
    apply Units.ext
    change adeleInclusion K L (q :
      NumberField.AdeleRing (𝓞 K) K) =
        (u : RelativeAdeleRing K L)
    exact ha

end RelativeIdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Extension_ClassGroup
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

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
/-- The scalar-extension map `C_K → C_L` is injective. -/
theorem classInclusion_injective :
    Function.Injective (classInclusion K L) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  unfold classInclusion
  rw [QuotientGroup.ker_map,
    comap_principalSubgroup K L]
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (QuotientGroup.eq_one_iff a).2 ha
  · intro hz
    have hz1 : z = 1 := Subgroup.mem_bot.mp hz
    obtain ⟨a, rfl⟩ :=
      QuotientGroup.mk_surjective z
    exact ⟨a, (QuotientGroup.eq_one_iff a).1 hz1, rfl⟩

end RelativeIdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_IdealMap
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IdeleGroup.finiteComponent_principalIdele _root_.IdeleGroup.infiniteComponent_principalIdele _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.RelativeIdeleGroup.classInclusion_mk _root_.RelativeIdeleGroup.classNorm_mk _root_.RelativeIdeleGroup.inclusion_principalIdele _root_.RelativeIdeleGroup.norm_inclusion _root_.RelativeIdeleGroup.norm_principalIdele _root_.RelativeIdeleGroup.smul_inclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The ideal attached to an idele

This file formalizes the ideal map from ideles. Its construction
is explicit: local discrete valuations form a finitely supported integer
vector, and unique factorization of fractional ideals identifies that vector
with a nonzero fractional ideal.  We prove both stages surjective and identify
the kernel with the ideles integral at every finite place.
-/

open scoped NumberField RestrictedProduct WithZero
open NumberField IsDedekindDomain

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace FiniteIdeleGroup

/-- The set of finite places where a finite idele is not an integral unit is
finite. -/
theorem finite_nonLocalUnits (a : FiniteIdeleGroup K) :
    {v : HeightOneSpectrum (𝓞 K) |
      a v ∉ (v.adicCompletionIntegers K).units}.Finite :=
  Filter.eventually_cofinite.mp a.2

/-- The finitely supported family of normalized local orders of a finite
idele. -/
def valuationVectorAdd (a : FiniteIdeleGroup K) :
    HeightOneSpectrum (𝓞 K) →₀ ℤ :=
  Finsupp.onFinset (finite_nonLocalUnits a).toFinset
    (fun v => (localOrder v (a v)).toAdd) (fun v hv => by
      rw [Set.Finite.mem_toFinset]
      intro hmem
      exact hv ((localOrder_eq_zero_iff v (a v)).2 hmem))

@[simp]
theorem valuationVectorAdd_apply (a : FiniteIdeleGroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    valuationVectorAdd a v = (localOrder v (a v)).toAdd :=
  rfl

/-- The finite valuation vector is a homomorphism from finite ideles to the
free abelian group on finite places. -/
def valuationVector :
    FiniteIdeleGroup K →* Multiplicative
      (HeightOneSpectrum (𝓞 K) →₀ ℤ) :=
  MonoidHom.mk' (fun a => Multiplicative.ofAdd (valuationVectorAdd a))
    fun a b => by
      apply Multiplicative.ext
      ext v
      exact congrArg Multiplicative.toAdd
        (map_mul (localOrder v) (a v) (b v))

@[simp]
theorem valuationVector_apply (a : FiniteIdeleGroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    (valuationVector a).toAdd v =
      (localOrder v (a v)).toAdd :=
  rfl

@[simp]
theorem localOrder_chosenLocalOrderSection
    (v : HeightOneSpectrum (𝓞 K)) (n : ℤ) :
    (localOrder v (chosenLocalOrderSection v n)).toAdd = n := by
  rw [localOrder_apply]
  change -WithZero.log
    (Valued.v (Classical.choose
      (HeightOneSpectrum.valuedAdicCompletion_surjective K v
        (WithZero.exp (-n))))) = n
  rw [Classical.choose_spec
    (HeightOneSpectrum.valuedAdicCompletion_surjective K v
      (WithZero.exp (-n)))]
  simp

/-- A finite idele with a prescribed finitely supported valuation vector. -/
def valuationVectorSection
    (e : HeightOneSpectrum (𝓞 K) →₀ ℤ) :
    FiniteIdeleGroup K :=
  ⟨fun v => chosenLocalOrderSection v (e v), by
    filter_upwards [e.support.eventually_cofinite_notMem] with v hv
    apply (localOrder_eq_zero_iff v _).1
    rw [localOrder_chosenLocalOrderSection, Finsupp.notMem_support_iff.mp hv]⟩

@[simp]
theorem valuationVector_valuationVectorSection
    (e : HeightOneSpectrum (𝓞 K) →₀ ℤ) :
    valuationVector (valuationVectorSection e) =
      Multiplicative.ofAdd e := by
  apply Multiplicative.ext
  ext v
  rw [valuationVector_apply]
  change (localOrder v (chosenLocalOrderSection v (e v))).toAdd = e v
  rw [localOrder_chosenLocalOrderSection]

theorem valuationVector_surjective :
    Function.Surjective (valuationVector (K := K)) := by
  intro e
  refine ⟨valuationVectorSection e.toAdd, ?_⟩
  exact valuationVector_valuationVectorSection e.toAdd

end FiniteIdeleGroup

namespace FractionalIdealGroup

/-- The homomorphism sending an integer exponent to the corresponding
power of a finite prime. -/
def primePowerHom (v : HeightOneSpectrum (𝓞 K)) :
    Multiplicative ℤ →* FractionalIdealGroup K :=
  MonoidHom.mk' (fun n => prime v ^ n.toAdd) fun m n => by
    simp [zpow_add]

/-- Reconstruct a fractional ideal from its finitely supported vector
of prime exponents. -/
def factorization :
    Multiplicative (HeightOneSpectrum (𝓞 K) →₀ ℤ) →*
      FractionalIdealGroup K :=
  MonoidHom.mk' (fun exps =>
      exps.toAdd.prod fun v n => primePowerHom v (Multiplicative.ofAdd n))
    fun a b => by
      exact Finsupp.prod_hom_add_index (fun v => primePowerHom v)

@[simp]
theorem factorization_val (exps :
    Multiplicative (HeightOneSpectrum (𝓞 K) →₀ ℤ)) :
    ((factorization exps : FractionalIdealGroup K) :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      exps.toAdd.prod fun v n =>
        (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ n := by
  classical
  simp [factorization, primePowerHom, prime, Finsupp.prod]

theorem finite_count_support (I : FractionalIdealGroup K) :
    {v : HeightOneSpectrum (𝓞 K) |
      FractionalIdeal.count K v
        (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0}.Finite :=
  Filter.eventually_cofinite.mp
    (FractionalIdeal.finite_factors
      (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K))

/-- The finitely supported vector of prime exponents of a nonzero
fractional ideal. -/
def countVector (I : FractionalIdealGroup K) :
    HeightOneSpectrum (𝓞 K) →₀ ℤ :=
  Finsupp.onFinset (finite_count_support I).toFinset
    (fun v => FractionalIdeal.count K v
      (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K))
    (fun v hv => by
      rw [Set.Finite.mem_toFinset]
      exact hv)

@[simp]
theorem countVector_apply (I : FractionalIdealGroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    countVector I v =
      FractionalIdeal.count K v
        (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :=
  rfl

@[simp]
theorem count_factorization (exps :
    Multiplicative (HeightOneSpectrum (𝓞 K) →₀ ℤ))
    (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v
      ((factorization exps : FractionalIdealGroup K) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      exps.toAdd v := by
  rw [factorization_val]
  exact FractionalIdeal.count_finsuppProd K v exps.toAdd

theorem ext_count {I J : FractionalIdealGroup K}
    (h : ∀ v : HeightOneSpectrum (𝓞 K),
      FractionalIdeal.count K v
        (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      FractionalIdeal.count K v
        (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) :
    I = J := by
  apply Units.ext
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization'
      K (Units.ne_zero I),
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization'
      K (Units.ne_zero J)]
  exact finprod_congr fun v => congrArg
    (fun n : ℤ =>
      (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ n) (h v)

theorem factorization_injective :
    Function.Injective (factorization (K := K)) := by
  intro a b hab
  apply Multiplicative.ext
  ext v
  rw [← count_factorization a v, ← count_factorization b v, hab]

theorem factorization_surjective :
    Function.Surjective (factorization (K := K)) := by
  intro I
  refine ⟨Multiplicative.ofAdd (countVector I), ?_⟩
  apply ext_count
  intro v
  rw [count_factorization]
  change countVector I v =
    FractionalIdeal.count K v
      (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
  exact countVector_apply I v

/-- Multiplicative unique factorization of nonzero fractional ideals by
finite primes. -/
def factorizationEquiv :
    Multiplicative (HeightOneSpectrum (𝓞 K) →₀ ℤ) ≃*
      FractionalIdealGroup K :=
  MulEquiv.ofBijective (factorization (K := K))
    ⟨factorization_injective, factorization_surjective⟩

end FractionalIdealGroup

namespace FiniteIdeleGroup

/-- The fractional ideal attached to a finite idele. -/
def fractionalIdeal :
    FiniteIdeleGroup K →* FractionalIdealGroup K :=
  (FractionalIdealGroup.factorizationEquiv (K := K)).toMonoidHom.comp
    (valuationVector (K := K))

theorem fractionalIdeal_surjective :
    Function.Surjective (fractionalIdeal (K := K)) :=
  (FractionalIdealGroup.factorizationEquiv (K := K)).surjective.comp
    valuationVector_surjective

/-- Finite ideles integral at every finite place. -/
def integralSubgroup : Subgroup (FiniteIdeleGroup K) where
  carrier := {a | ∀ v : HeightOneSpectrum (𝓞 K),
    a v ∈ (v.adicCompletionIntegers K).units}
  one_mem' v := (v.adicCompletionIntegers K).units.one_mem
  mul_mem' ha hb v :=
    (v.adicCompletionIntegers K).units.mul_mem (ha v) (hb v)
  inv_mem' ha v :=
    (v.adicCompletionIntegers K).units.inv_mem (ha v)

@[simp]
theorem mem_integralSubgroup_iff (a : FiniteIdeleGroup K) :
    a ∈ integralSubgroup ↔
      ∀ v : HeightOneSpectrum (𝓞 K),
        a v ∈ (v.adicCompletionIntegers K).units :=
  Iff.rfl

theorem fractionalIdeal_ker :
    (fractionalIdeal (K := K)).ker = integralSubgroup := by
  ext a
  constructor
  · intro ha v
    have hv :
        valuationVector a =
          (1 : Multiplicative
            (HeightOneSpectrum (𝓞 K) →₀ ℤ)) := by
      apply (FractionalIdealGroup.factorizationEquiv
        (K := K)).injective
      simpa [fractionalIdeal] using ha
    apply (localOrder_eq_zero_iff v (a v)).1
    rw [← valuationVector_apply a v, hv]
    rfl
  · intro ha
    have hv :
        valuationVector a =
          (1 : Multiplicative
            (HeightOneSpectrum (𝓞 K) →₀ ℤ)) := by
      apply Multiplicative.ext
      ext v
      rw [valuationVector_apply]
      exact (localOrder_eq_zero_iff v (a v)).2 (ha v)
    simp [fractionalIdeal, hv]

end FiniteIdeleGroup

namespace IdeleGroup

/-- The fractional ideal attached to an idele. The archimedean components
do not contribute. -/
def fractionalIdeal :
    IdeleGroup K →* FractionalIdealGroup K :=
  (FiniteIdeleGroup.fractionalIdeal (K := K)).comp
    (MonoidHom.snd _ _)

/-- Ideles integral at every finite place; this is the subgroup
`I_K^{S∞}`. -/
def integralAtFinitePlaces : Subgroup (IdeleGroup K) :=
  Subgroup.comap (MonoidHom.snd _ _)
    (FiniteIdeleGroup.integralSubgroup (K := K))

/-- The canonical surjection from ideles to the ordinary ideal class
group. -/
def idealClass :
    IdeleGroup K →* ClassGroup (𝓞 K) :=
  (ClassGroup.mk K).comp (fractionalIdeal (K := K))

end IdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Extension_GaloisDescent
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.RelativeIdeleGroup.finiteComponent_coe _root_.RelativeIdeleGroup.infiniteComponent_coe _root_.RelativeIdeleGroup.scalarConjugation_baseAdele_apply _root_.intermediateAdeleInclusion_tmul _root_.relativeAdeleFiniteComponent_tmul _root_.relativeAdeleInfiniteComponent_tmul _root_.topFieldToOneStep_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Galois descent for idele classes

For a finite Galois extension `L/K`, the Galois action on relative ideles
preserves principal ideles and hence descends to the relative idele class
group. Noether's form of Hilbert 90 then shows that every fixed
class has a fixed representative. Together with fixed-idele descent, this identifies
the fixed subgroup with the embedded copy of `C_K`.
-/

open scoped NumberField
open NumberField

noncomputable section


variable
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

namespace RelativeIdeleGroup

omit [NumberField L] [FiniteDimensional K L] in
/-- The diagonal copy of `Lˣ` in the relative ideles is injective. -/
theorem principalIdele_injective :
    Function.Injective (principalIdele K L) := by
  exact Units.map_injective
    (Algebra.TensorProduct.includeRight_injective
      (B := L)
      (NumberField.AdeleRing.algebraMap_injective
        (R := 𝓞 K) (K := K)))

omit [NumberField L] [FiniteDimensional K L] in
/-- Galois conjugation preserves the principal-relative-idele
congruence, so it acts on the quotient class group. -/
instance principalQuotientAction :
    MulAction.QuotientAction (L ≃ₐ[K] L)
      (principalSubgroup K L) where
  inv_mul_mem σ {a a'} h := by
    rcases h with ⟨x, hx⟩
    refine
      ⟨Units.map σ.toRingEquiv.toMonoidHom x, ?_⟩
    rw [← smul_principalIdele K L σ x, hx]
    simp [smul_def]

omit [NumberField L] [FiniteDimensional K L] in
@[simp]
theorem smul_class_mk
    (σ : L ≃ₐ[K] L) (a : RelativeIdeleGroup K L) :
    σ •
        (QuotientGroup.mk'
          (principalSubgroup K L) a) =
      QuotientGroup.mk'
        (principalSubgroup K L) (σ • a) :=
  rfl

/-- The quotient Galois action on relative idele classes, viewed as an
action by group automorphisms. -/
@[reducible]
noncomputable def relativeIdeleClassMulDistribMulAction :
    MulDistribMulAction (L ≃ₐ[K] L) (ClassGroup K L) := by
  letI := relativeIdeleMulDistribMulAction K L
  exact Function.Surjective.mulDistribMulAction
    (QuotientGroup.mk' (principalSubgroup K L))
    (QuotientGroup.mk'_surjective (principalSubgroup K L))
    (fun _ _ ↦ rfl)

/-- The subgroup of relative idele classes fixed by every Galois
automorphism. -/
def galoisFixedClassSubgroup :
    Subgroup (ClassGroup K L) := by
  letI := relativeIdeleClassMulDistribMulAction K L
  exact FixedPoints.subgroup (L ≃ₐ[K] L) (ClassGroup K L)

omit [NumberField L] [FiniteDimensional K L] in
/-- Every class coming from `C_K` is Galois fixed. -/
theorem classInclusion_range_le_galoisFixed :
    (classInclusion K L).range ≤
      galoisFixedClassSubgroup K L := by
  rintro _ ⟨c, rfl⟩
  obtain ⟨a, rfl⟩ :=
    QuotientGroup.mk_surjective c
  intro σ
  change
    σ •
        QuotientGroup.mk'
          (principalSubgroup K L)
          (inclusion K L a) =
      QuotientGroup.mk'
        (principalSubgroup K L)
        (inclusion K L a)
  rw [smul_class_mk, smul_inclusion]

omit [NumberField L] in
/-- A Galois-fixed relative idele class has a Galois-fixed idele
representative. This is the Noether–Hilbert-90 step in idele-class descent. -/
theorem exists_fixed_representative_of_fixed_class
    [IsGalois K L]
    (a : RelativeIdeleGroup K L)
    (ha :
      ∀ σ : L ≃ₐ[K] L,
        σ •
            QuotientGroup.mk'
              (principalSubgroup K L) a =
          QuotientGroup.mk'
            (principalSubgroup K L) a) :
    ∃ a' : RelativeIdeleGroup K L,
      QuotientGroup.mk'
          (principalSubgroup K L) a' =
        QuotientGroup.mk'
          (principalSubgroup K L) a ∧
      ∀ σ : L ≃ₐ[K] L, σ • a' = a' := by
  classical
  let := relativeIdeleMulDistribMulAction K L
  have hex :
      ∀ σ : L ≃ₐ[K] L,
        ∃ x : Lˣ,
          principalIdele K L x =
            (σ • a) / a := by
    intro σ
    have hmem :
        (σ • a) / a ∈ principalSubgroup K L := by
      exact (QuotientGroup.eq_iff_div_mem).1 (ha σ)
    exact hmem
  let f : (L ≃ₐ[K] L) → Lˣ :=
    fun σ ↦ Classical.choose (hex σ)
  have hf_spec :
      ∀ σ : L ≃ₐ[K] L,
        principalIdele K L (f σ) =
          (σ • a) / a :=
    fun σ ↦ Classical.choose_spec (hex σ)
  have hf_cocycle :
      groupCohomology.IsMulCocycle₁ f := by
    intro σ τ
    apply principalIdele_injective K L
    have hsmul :
        principalIdele K L (σ • f τ) =
          σ • principalIdele K L (f τ) := by
      calc
        principalIdele K L (σ • f τ) =
            principalIdele K L
              (Units.map
                σ.toRingEquiv.toMonoidHom (f τ)) := by
          congr 1
        _ = σ • principalIdele K L (f τ) :=
          (smul_principalIdele K L σ (f τ)).symm
    rw [map_mul, hsmul,
      hf_spec (σ * τ), hf_spec τ, hf_spec σ,
      smul_div', ← mul_smul]
    exact (div_mul_div_cancel _ _ _).symm
  obtain ⟨β, hβ⟩ :=
    groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units
      f hf_cocycle
  let a' : RelativeIdeleGroup K L :=
    a / principalIdele K L β
  have hratio :
      ∀ σ : L ≃ₐ[K] L,
        (σ • principalIdele K L β) /
            principalIdele K L β =
          (σ • a) / a := by
    intro σ
    have hβ' :
        Units.map σ.toRingEquiv.toMonoidHom β / β =
          f σ := by
      calc
        Units.map σ.toRingEquiv.toMonoidHom β / β =
            σ • β / β := by
          congr 2
        _ = f σ := hβ σ
    rw [smul_principalIdele,
      ← map_div, hβ', hf_spec σ]
  have ha'fixed :
      ∀ σ : L ≃ₐ[K] L, σ • a' = a' := by
    intro σ
    change
      σ • (a / principalIdele K L β) =
        a / principalIdele K L β
    rw [smul_div']
    calc
      (σ • a) / (σ • principalIdele K L β) =
          ((σ • a) / a) *
            (a / (σ • principalIdele K L β)) := by
        exact (div_mul_div_cancel _ _ _).symm
      _ = ((σ • principalIdele K L β) /
            principalIdele K L β) *
          (a / (σ • principalIdele K L β)) := by
        rw [← hratio σ]
      _ = a / principalIdele K L β := by
        exact div_mul_div_cancel' _ _ _
  refine ⟨a', ?_, ha'fixed⟩
  apply (QuotientGroup.eq_iff_div_mem).2
  refine ⟨β⁻¹, ?_⟩
  change
    (principalIdele K L β)⁻¹ =
      (a / principalIdele K L β) / a
  simpa only [div_mul_eq_div_div] using
    (div_mul_cancel_right a
      (principalIdele K L β)).symm

omit [NumberField L] in
/-- Every Galois-fixed relative idele class comes from `C_K`. -/
theorem galoisFixed_le_classInclusion_range
    [IsGalois K L] :
    galoisFixedClassSubgroup K L ≤
      (classInclusion K L).range := by
  intro c hc
  obtain ⟨a, rfl⟩ :=
    QuotientGroup.mk_surjective c
  have ha :
      ∀ σ : L ≃ₐ[K] L,
        σ •
            QuotientGroup.mk'
              (principalSubgroup K L) a =
          QuotientGroup.mk'
            (principalSubgroup K L) a :=
    hc
  obtain ⟨a', ha'class, ha'fixed⟩ :=
    exists_fixed_representative_of_fixed_class
      K L a ha
  have ha'mem :
      a' ∈ galoisFixedSubgroup K L :=
    ha'fixed
  rw [← inclusion_range_eq_galoisFixedSubgroup
    K L] at ha'mem
  obtain ⟨b, hb⟩ := ha'mem
  refine
    ⟨QuotientGroup.mk'
      (IdeleGroup.principalSubgroup K) b, ?_⟩
  rw [classInclusion_mk, hb]
  exact ha'class

omit [NumberField L] in
/-- Galois descent for idele classes,
`C_L^{Gal(L/K)} = C_K`. -/
theorem classInclusion_range_eq_galoisFixedClassSubgroup
    [IsGalois K L] :
    (classInclusion K L).range =
      galoisFixedClassSubgroup K L :=
  le_antisymm
    (classInclusion_range_le_galoisFixed K L)
    (galoisFixed_le_classInclusion_range K L)

end RelativeIdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_Induced
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ramificationQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.representedQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.residueQuotientFinite _root_.ClassFormation.DegreeData.FiniteResidueAbstractExtension.instFiniteQuotientSubtypeMemSubgroupFieldBaseExtensionSubgroupField _root_.ClassFormation.DegreeData.FiniteTower.baseQuotientFinite _root_.ClassFormation.DegreeData.FiniteTower.topQuotientFinite _root_.ClassFormation.DegreeData.FiniteTower.totalQuotientFinite _root_.ClassFormation.FiniteAbstractField.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteAbstractFieldExtension.instFiniteQuotientSubtypeMemSubgroupFieldBaseExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

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

section CyclicCoordinates

variable [CommGroup G] [Fintype G]

/-- In a cyclic group, `σ^[G:H]` generates `H`. -/
theorem zpowers_pow_index_eq (H : Subgroup G) (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ) :
    Subgroup.zpowers (σ ^ H.index) = H := by
  have hn0 : H.index ≠ 0 := by
    rw [H.index_eq_card]
    exact Nat.card_pos.ne'
  have horder : orderOf σ = Nat.card G :=
    orderOf_eq_card_of_forall_mem_zpowers hgen
  have hindex_dvd_order : H.index ∣ orderOf σ := by
    rw [horder]
    exact H.index_dvd_card
  have hpowOrder :
      orderOf (σ ^ H.index) = Nat.card H := by
    calc
      orderOf (σ ^ H.index) =
          orderOf σ / H.index :=
        orderOf_pow_of_dvd hn0 hindex_dvd_order
      _ = Nat.card G / H.index := by rw [horder]
      _ = Nat.card H := by
        rw [← H.index_mul_card]
        exact Nat.mul_div_cancel_left
          (Nat.card H) (Nat.pos_of_ne_zero hn0)
  apply Subgroup.eq_of_le_of_card_ge
  · exact Subgroup.zpowers_le.mpr
      (cyclic_pow_index_mem H σ)
  · rw [Nat.card_zpowers, hpowOrder]

/-- The canonical element `σ^[G:H]` generates `H`. -/
theorem subgroupGenerator_generates (H : Subgroup G) (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ) :
    ∀ h : H, h ∈ Subgroup.zpowers (subgroupGenerator H σ) := by
  intro h
  have hh : h.1 ∈
      Subgroup.zpowers (σ ^ H.index) := by
    rw [zpowers_pow_index_eq H σ hgen]
    exact h.2
  obtain ⟨k, hk⟩ :=
    Subgroup.mem_zpowers_iff.mp hh
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  apply Subtype.ext
  exact hk

end CyclicCoordinates

section InducedHerbrandH0

variable [CommGroup G] [Fintype G] [CommGroup B]
variable (H : Subgroup G) [MulDistribMulAction H B]

attribute [local instance] CyclicCohomology.instFintypeSubtypeMemSubgroup_solutions
/-- Norm compatibility under evaluation:
`ev₁(N_G f) = N_H(∏_{G/H} f)`. -/
theorem inducedEvaluation_tateNorm (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ)
    (f : InducedModule (B := B) H) :
    inducedEvaluation H
        (tateNorm G (InducedModule (B := B) H) f) =
      tateNorm H B
        (inducedCoordinateProduct H σ hgen f) := by
  classical
  let e := cyclicCosetEquiv H σ hgen
  let ev : InducedModule (B := B) H →* B :=
    inducedEvaluation H
  calc
    inducedEvaluation H
          (tateNorm G (InducedModule (B := B) H) f) =
        ∏ g : G, f.1 g := by
      calc
        inducedEvaluation H
              (tateNorm G
                (InducedModule (B := B) H) f) =
            ∏ g : G, ev (g • f) := by
          simp only [tateNorm, ev, map_prod]
        _ = ∏ g : G, f.1 g := by
          apply Finset.prod_congr rfl
          intro g _hg
          change f.1 (1 * g) = f.1 g
          rw [one_mul]
    _ = ∏ p : H × Fin H.index, f.1 (e p) := by
      exact Fintype.prod_equiv e.symm
        (fun g : G ↦ f.1 g)
        (fun p : H × Fin H.index ↦ f.1 (e p))
        (fun g ↦ by
          rw [e.apply_symm_apply])
    _ = ∏ h : H, ∏ i : Fin H.index,
          h • f.1 (σ ^ i.1) := by
      rw [Fintype.prod_prod_type]
      apply Finset.prod_congr rfl
      intro h _hh
      apply Finset.prod_congr rfl
      intro i _hi
      change
        f.1 (h.1 * σ ^ i.1) =
          h • f.1 (σ ^ i.1)
      exact f.2 h (σ ^ i.1)
    _ = ∏ h : H,
          h • (∏ i : Fin H.index,
            f.1 (σ ^ i.1)) := by
      apply Finset.prod_congr rfl
      intro h _hh
      exact
        (map_prod
          (MulDistribMulAction.toMonoidHom B h)
          (fun i : Fin H.index ↦ f.1 (σ ^ i.1))
          Finset.univ).symm
    _ = tateNorm H B
          (inducedCoordinateProduct H σ hgen f) := by
      simp only [tateNorm,
        inducedCoordinateProduct_apply]

end InducedHerbrandH0

section InducedHerbrandHMinusOne

variable [CommGroup G] [Fintype G] [CommGroup B]
variable (H : Subgroup G) [MulDistribMulAction H B]

attribute [local instance] CyclicCohomology.instNeZeroNatIndex_solutions
/-- In canonical coordinates, right translation by `σ` is the cyclic shift
whose wrap-around is acted on by `σ^[G:H]`. -/
theorem inducedCoordinates_smul_generator (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ)
    (f : InducedModule (B := B) H)
    (i : Fin H.index) :
    inducedCoordinates H σ hgen (σ • f) i =
      twistedFinRotate (subgroupGenerator H σ)
        (inducedCoordinates H σ hgen f) i := by
  unfold twistedFinRotate
  change
    f.1 (σ ^ i.1 * σ) =
      if finRotate H.index i = 0 then
        subgroupGenerator H σ •
          f.1 (σ ^ (0 : Fin H.index).1)
      else
        f.1 (σ ^ (finRotate H.index i).1)
  rw [pow_mul_eq_pow_finRotate]
  split_ifs with hi
  · have hcov :=
      f.2 (subgroupGenerator H σ) 1
    change
      f.1 (σ ^ H.index * 1) =
        subgroupGenerator H σ • f.1 1 at hcov
    simpa using hcov
  · rfl

/-- The transversal product sends a `σ`-coboundary to the corresponding
`σ^[G:H]`-coboundary. -/
theorem inducedCoordinateProduct_sigmaMinusOne
    (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ)
    (f : InducedModule (B := B) H) :
    inducedCoordinateProduct H σ hgen
        (sigmaMinusOne G
          (InducedModule (B := B) H) σ f) =
      sigmaMinusOne H B
        (subgroupGenerator H σ) (f.1 1) := by
  let v : Fin H.index → B :=
    inducedCoordinates H σ hgen f
  rw [show
      sigmaMinusOne G
          (InducedModule (B := B) H) σ f =
        σ • f * f⁻¹ by rfl,
    map_mul, map_inv]
  change
    (∏ i : Fin H.index,
        inducedCoordinates H σ hgen (σ • f) i) *
        (∏ i : Fin H.index, v i)⁻¹ =
      sigmaMinusOne H B
        (subgroupGenerator H σ) (f.1 1)
  calc
    (∏ i : Fin H.index,
          inducedCoordinates H σ hgen (σ • f) i) *
          (∏ i : Fin H.index, v i)⁻¹ =
        (∏ i : Fin H.index,
          twistedFinRotate
            (subgroupGenerator H σ) v i) *
          (∏ i : Fin H.index, v i)⁻¹ := by
      congr 2
      funext i
      exact inducedCoordinates_smul_generator
        H σ hgen f i
    _ = subgroupGenerator H σ • v 0 *
          (v 0)⁻¹ :=
      prod_twistedFinRotate_div
        (subgroupGenerator H σ) v
    _ = sigmaMinusOne H B
          (subgroupGenerator H σ) (f.1 1) := by
      have hv0 : v 0 = f.1 1 := by
        simpa only [Fin.val_zero, pow_zero] using
          (inducedCoordinates_apply H σ hgen f (0 : Fin H.index))
      simpa only [sigmaMinusOne] using
        congrArg (fun b : B => subgroupGenerator H σ • b * b⁻¹) hv0

end InducedHerbrandHMinusOne

section FiniteCyclicGroup

variable [Group G] [Fintype G] [CommGroup B]
variable (H : Subgroup G) [MulDistribMulAction H B]

/-- The canonical generator of a subgroup, exposed without requiring a
global `CommGroup G` instance.  Commutativity is derived from the supplied
cyclic generator. -/
noncomputable def subgroupGeneratorOfGenerator (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ) : H := by
  letI : IsCyclic G := ⟨⟨σ, hgen⟩⟩
  letI : CommGroup G := IsCyclic.commGroup
  exact subgroupGenerator H σ

omit [Fintype G] in
@[simp]
theorem subgroupGeneratorOfGenerator_coe (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ) :
    (subgroupGeneratorOfGenerator H σ hgen : G) =
      σ ^ H.index :=
  rfl

/-- The derived element `σ^[G:H]` generates `H`. -/
theorem subgroupGeneratorOfGenerator_generates (σ : G)
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers σ) :
    ∀ h : H,
      h ∈ Subgroup.zpowers
        (subgroupGeneratorOfGenerator H σ hgen) := by
  let : IsCyclic G := ⟨⟨σ, hgen⟩⟩
  let : CommGroup G := IsCyclic.commGroup
  have hτ :
      subgroupGeneratorOfGenerator H σ hgen =
        subgroupGenerator H σ :=
    Subtype.ext (by rfl)
  rw [hτ]
  exact subgroupGenerator_generates H σ hgen

end FiniteCyclicGroup

end CyclicCohomology
end
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_HerbrandLowDegree_Product
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

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

section TateProducts

variable {G : Type uG} [Group G] [Fintype G]
variable {ι : Type uι} (A : ι → Type uA)
variable [∀ i, CommGroup (A i)]
variable [∀ i, MulDistribMulAction G (A i)]

local instance instMulDistribMulActionForall_solutions :
    MulDistribMulAction G (∀ i, A i) :=
  piMulDistribMulAction G A

/-- Fixed points of a product are products of fixed points. -/
def fixedPiEquiv :
    fixedSubgroup G (∀ i, A i) ≃*
      ∀ i, fixedSubgroup G (A i) where
  toFun x i := ⟨x.1 i, fun g ↦ congrFun (x.2 g) i⟩
  invFun x := ⟨fun i ↦ (x i).1, fun g ↦ by
    funext i
    exact (x i).2 g⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

omit [Fintype G] in
@[simp]
theorem fixedPiEquiv_apply_coe
    (x : fixedSubgroup G (∀ i, A i))
    (i : ι) :
    ((fixedPiEquiv (G := G) A x i : A i)) =
      x.1 i :=
  rfl

end TateProducts

end CyclicCohomology
end
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_Product
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Herbrand quotients of finite products

This file extracts the cardinality consequence of the product
decompositions of low-degree Tate cohomology, giving the corresponding
product formula for Herbrand quotients.
-/

open scoped BigOperators

noncomputable section

namespace CyclicCohomology

open CyclicCohomology.ProfiniteCohomology.Herbrand

universe uG uι uA

variable {G : Type uG} [Group G] [Fintype G]
variable {ι : Type uι} [Fintype ι]
variable (A : ι → Type uA)
variable [∀ i, CommGroup (A i)]
variable [∀ i, MulDistribMulAction G (A i)]

local instance instMulDistribMulActionForall_solutions_1 :
    MulDistribMulAction G (∀ i, A i) :=
  piMulDistribMulAction G A

end CyclicCohomology
end
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_Permutation_Module
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroup_tateNorm_coe _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Herbrand quotients of permutation lattices

This file supplies the abstract cohomology calculation for permutation
lattices.  It proves the value of the Herbrand quotient on the trivial
integer lattice, transports that calculation through Shapiro's lemma to
transitive permutation lattices, and multiplies over a finite family of
orbits.  It also records invariance under passage to a finite-index stable
subgroup.
-/

open scoped BigOperators

noncomputable section

namespace CyclicCohomology

open CyclicCohomology.ProfiniteCohomology.Herbrand

universe uG uA uι

section TrivialInteger

variable {G : Type uG} [Group G] [Fintype G]

/-- For the trivial integer module, the norm is multiplication by the
order of the group. -/
theorem trivialInt_tateNorm_toAdd
    (a : Multiplicative ℤ) :
    letI := trivialIntMulDistribMulAction G
    Multiplicative.toAdd
        (tateNorm G (Multiplicative ℤ) a) =
      (Fintype.card G : ℤ) * Multiplicative.toAdd a := by
  let := trivialIntMulDistribMulAction G
  have hsmul (g : G) : g • a = a := rfl
  simp [tateNorm, hsmul]

end TrivialInteger

end CyclicCohomology
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_Herbrand
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.LubinTate.compatibleGroupFamiliesGroup _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.FiniteIdeleGroup.mem_integralSubgroup_iff _root_.FiniteIdeleGroup.valuationVectorAdd_apply _root_.FiniteIdeleGroup.valuationVector_apply _root_.FiniteIdeleGroup.valuationVector_valuationVectorSection _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.RelativeIdeleGroup.finiteComponent_coe _root_.RelativeIdeleGroup.infiniteComponent_coe _root_.intermediateAdeleInclusion_tmul _root_.relativeAdeleFiniteComponent_tmul _root_.relativeAdeleInfiniteComponent_tmul _root_.topFieldToOneStep_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Herbrand cohomology of the relative idele class group

This file realizes the low-degree exact sequence on the actual relative
idele group

`1 → Lˣ → I_L → C_L → 1`.

The Galois actions are the concrete conjugation actions from the
tensor-product model of relative adeles.  The class norm is descended from
the determinant norm on relative ideles, and its relation with the Tate
norm is proved from the Galois product formula.
-/

open scoped BigOperators NumberField
open NumberField

noncomputable section


open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

namespace RelativeIdeleGroup
namespace Cohomology

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The natural Galois action on relative ideles, upgraded from the
existing multiplicative action to an action by group automorphisms. -/
@[reducible]
noncomputable def relativeIdeleMulDistribMulAction :
    MulDistribMulAction (L ≃ₐ[K] L)
      (RelativeIdeleGroup K L) where
  __ := RelativeIdeleGroup.relativeIdeleMulAction K L
  smul_one σ :=
    map_one (RelativeIdeleGroup.conjugationIdele K L σ)
  smul_mul σ a b :=
    map_mul
      (RelativeIdeleGroup.conjugationIdele K L σ) a b

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
theorem principalRelativeIdele_smul_mem
    (σ : L ≃ₐ[K] L)
    (a : RelativeIdeleGroup K L)
    (ha :
      a ∈ RelativeIdeleGroup.principalSubgroup K L) :
    σ • a ∈
      RelativeIdeleGroup.principalSubgroup K L := by
  rcases ha with ⟨x, rfl⟩
  refine
    ⟨Units.map σ.toRingEquiv.toMonoidHom x, ?_⟩
  exact
    (RelativeIdeleGroup.smul_principalIdele
      K L σ x).symm

/-- The actual quotient Galois action on the relative idele class group,
upgraded to an action by group automorphisms. -/
@[reducible]
noncomputable def ideleClassMulDistribMulAction :
    MulDistribMulAction (L ≃ₐ[K] L)
      (RelativeIdeleGroup.ClassGroup K L) := by
  letI := relativeIdeleMulDistribMulAction K L
  exact
    stableQuotientMulDistribMulAction
      (RelativeIdeleGroup.principalSubgroup K L)
      (principalRelativeIdele_smul_mem K L)

/-- The restricted Galois action on the actual subgroup of principal
relative ideles. -/
@[reducible]
noncomputable def principalIdeleMulDistribMulAction :
    MulDistribMulAction (L ≃ₐ[K] L)
      (RelativeIdeleGroup.principalSubgroup K L) := by
  letI := relativeIdeleMulDistribMulAction K L
  exact
    stableSubgroupMulDistribMulAction
      (RelativeIdeleGroup.principalSubgroup K L)
      (principalRelativeIdele_smul_mem K L)

/-- The norm on relative ideles, descended through principal ideles to
the actual idele class groups. -/
noncomputable def ideleClassNorm :
    RelativeIdeleGroup.ClassGroup K L →*
      IdeleClassGroup K :=
  QuotientGroup.map
    (RelativeIdeleGroup.principalSubgroup K L)
    (IdeleGroup.principalSubgroup K)
    (RelativeIdeleGroup.norm K L)
    (by
      rintro _ ⟨x, rfl⟩
      refine
        ⟨Units.map (Algebra.norm K) x, ?_⟩
      exact
        (RelativeIdeleGroup.norm_principalIdele
          K L x).symm)

omit [NumberField L] [IsGalois K L] in
@[simp]
theorem ideleClassNorm_mk
    (a : RelativeIdeleGroup K L) :
    ideleClassNorm K L
        (QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K L) a) =
      QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K)
        (RelativeIdeleGroup.norm K L a) :=
  rfl

section Actions

local instance instMulDistribMulActionAlgEquiv_r3ed079_1 :
    MulDistribMulAction (L ≃ₐ[K] L)
      (RelativeIdeleGroup K L) :=
  relativeIdeleMulDistribMulAction K L
local instance instMulDistribMulActionAlgEquivClassGroup :
    MulDistribMulAction (L ≃ₐ[K] L)
      (RelativeIdeleGroup.ClassGroup K L) :=
  ideleClassMulDistribMulAction K L

local instance instMulDistribMulActionAlgEquivSubtypeMemSubgroupPrincipalSubgroup_r3ed079_1 :
    MulDistribMulAction (L ≃ₐ[K] L)
      (RelativeIdeleGroup.principalSubgroup K L) :=
  principalIdeleMulDistribMulAction K L
omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem relativeIdele_smul_def
    (σ : L ≃ₐ[K] L)
    (a : RelativeIdeleGroup K L) :
    σ • a =
      RelativeIdeleGroup.conjugationIdele K L σ a :=
  rfl

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem ideleClass_smul_mk
    (σ : L ≃ₐ[K] L)
    (a : RelativeIdeleGroup K L) :
    σ • QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K L) a =
      QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K L)
        (σ • a) :=
  rfl

end Actions

end Cohomology
end RelativeIdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_PrincipalUnits
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
/-!
# Principal units

Defines the filtration `U^n = 1 + 𝓂^n`, proves its basic order properties, and
constructs the quotient of valuation-ring units by the first filtration step.
-/

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- Principal-unit groups decrease as the filtration index increases. -/
theorem principalUnits_antitone (K : Type u) [Field K] [ValuativeRel K]
    {m n : Nat} (h : m ≤ n) :
    principalUnits K n ≤ principalUnits K m := by
  intro u hu
  exact Ideal.pow_le_pow_right h hu

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_ResidueUnits
attribute [-instance] _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
/-!
# Residue units

Constructs the quotient of valuation-ring units by first principal units and
identifies it, multiplicatively and additively, with the residue-field units.
-/

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- The unit group of the finite residue field is finite. -/
noncomputable instance residueUnitsFinite
    (K : Type u) [Field K] [ValuativeRel K] [Finite 𝓀[K]] :
    Finite (ResidueUnits K) := by
  exact Finite.of_equiv 𝓀[K]ˣ (residueUnitsConcreteEquiv K).symm.toEquiv

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_Units
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.LubinTate.compatibleGroupFamiliesGroup _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalFieldTheory

/-!
# Principal-unit filtrations

This file provides a theorem API for antitone principal-unit filtrations used by
ramification and norm arguments.
-/

universe u v

open scoped BigOperators

namespace DiscreteValuationField

namespace AntitoneSubgroupFiltration

variable {G : Type u} [Group G] (U : AntitoneSubgroupFiltration G)

/-- The subgroup appearing in `(U.principalUnitSubgroupClassInQuotient m n).Normal` is normal. -/
instance principalUnitSubgroupClassInQuotient_normal
    (m n : ℕ) [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] :
    (U.principalUnitSubgroupClassInQuotient m n).Normal := by
  dsimp [principalUnitSubgroupClassInQuotient]
  infer_instance

/-- Eliminate a principal-unit subquotient through its canonical map. -/
protected theorem principalUnitSubquotient.inductionOn
    (m n : ℕ) [(U.principalUnitSubgroup n).Normal]
    {motive : U.principalUnitSubquotient m n → Prop}
    (q : U.principalUnitSubquotient m n)
    (h : ∀ x : U.principalUnitSubgroup m,
      motive (U.principalUnitSubquotientMk m n x)) :
    motive q := by
  change motive
    (show U.principalUnitSubgroup m ⧸
      (U.principalUnitSubgroup n).subgroupOf
        (U.principalUnitSubgroup m) from q)
  refine QuotientGroup.induction_on q ?_
  intro x
  exact h x

/-- The principal-unit graded piece `U^n/U^{n+1}`. -/
def principalUnitGradedPiece (n : ℕ) : Type u :=
  U.principalUnitSubquotient n (n + 1)

/--
Equips the target with its canonical `Group` structure, namely `Group (U.principalUnitGradedPiece
n)`.
-/
instance principalUnitGradedPieceGroup
    (n : ℕ) [(U.principalUnitSubgroup (n + 1)).Normal] :
    Group (U.principalUnitGradedPiece n) := by
  change Group (U.principalUnitSubquotient n (n + 1))
  infer_instance

/-- The canonical class map into the adjacent graded piece. -/
def principalUnitGradedPieceMk
    (n : ℕ) [(U.principalUnitSubgroup (n + 1)).Normal] :
    U.principalUnitSubgroup n →* U.principalUnitGradedPiece n := by
  change U.principalUnitSubgroup n →*
    U.principalUnitSubquotient n (n + 1)
  exact U.principalUnitSubquotientMk n (n + 1)

/-- Explicit identification of a graded piece with its named adjacent
subquotient. -/
def principalUnitGradedPieceEquivSubquotient
    (n : ℕ) [(U.principalUnitSubgroup (n + 1)).Normal] :
    U.principalUnitGradedPiece n ≃*
      U.principalUnitSubquotient n (n + 1) := by
  change U.principalUnitSubquotient n (n + 1) ≃*
    U.principalUnitSubquotient n (n + 1)
  exact MulEquiv.refl _

/-- Cardinality bridge between the adjacent named subquotient and the graded
piece wrapper. -/
theorem card_principalUnitSubquotient_succ_eq_gradedPiece
    (n : ℕ) [(U.principalUnitSubgroup (n + 1)).Normal]
    [Finite (U.principalUnitSubquotient n (n + 1))] :
    Nat.card (U.principalUnitSubquotient n (n + 1)) =
      Nat.card (U.principalUnitGradedPiece n) :=
  Nat.card_congr (U.principalUnitGradedPieceEquivSubquotient n).symm.toEquiv

/-- Representative criterion for the identity in `U^m/U^n`. -/
theorem principalUnitSubquotient_mk_eq_one_iff
    {m n : ℕ} [(U.principalUnitSubgroup n).Normal]
    (x : U.principalUnitSubgroup m) :
    U.principalUnitSubquotientMk m n x = 1 ↔
      (x : G) ∈ U.principalUnitSubgroup n := by
  change (QuotientGroup.mk x :
      U.principalUnitSubgroup m ⧸
        (U.principalUnitSubgroup n).subgroupOf
          (U.principalUnitSubgroup m)) =
    1 ↔ x ∈ (U.principalUnitSubgroup n).subgroupOf
      (U.principalUnitSubgroup m)
  exact QuotientGroup.eq_one_iff
    (N := (U.principalUnitSubgroup n).subgroupOf
      (U.principalUnitSubgroup m)) x

/-- The restricted map `U^l/U^n → U^l/U^m` is surjective. -/
theorem principalUnitClassMapOfLe_surjective {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] :
    Function.Surjective (U.principalUnitClassMapOfLe hlm hmn) := by
  intro q
  rcases q with ⟨q, hq⟩
  rcases (U.mem_principalUnitSubgroupClassInQuotient_iff l m q).1 hq with
    ⟨x, hx, hxq⟩
  refine ⟨⟨QuotientGroup.mk' (U.principalUnitSubgroup n) x,
    U.principalUnitSubgroupClassInQuotient_mk_mem hx⟩, ?_⟩
  apply Subtype.ext
  rw [U.principalUnitClassMapOfLe_apply, U.quotient_principalUnitSubgroup_mapOfLe_apply_mk']
  exact hxq

/-- First isomorphism theorem inside principal-unit classes:
`(U^l/U^n)/ker(U^l/U^n → U^l/U^m) ≃ U^l/U^m`, for `l ≤ m ≤ n`.
The kernel is identified with `U^m/U^n` by
`principalUnitClassMapOfLe_ker_eq`. -/
noncomputable def principalUnitClassQuotientKerEquivClassOfLe {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] :
    U.principalUnitSubgroupClassInQuotient l n ⧸
        (U.principalUnitClassMapOfLe hlm hmn).ker ≃*
      U.principalUnitSubgroupClassInQuotient l m :=
  QuotientGroup.quotientKerEquivOfSurjective
    (U.principalUnitClassMapOfLe hlm hmn)
    (U.principalUnitClassMapOfLe_surjective hlm hmn)

/--
Establishes the identity `U.principalUnitClassQuotientKerEquivClassOfLe hlm hmn (QuotientGroup.mk'
(U.principalUnitClassMapOfLe hlm hmn).ker q) = U.principalUnitClassMapOfLe hlm hmn q`.
-/
@[simp] theorem principalUnitClassQuotientKerEquivClassOfLe_mk'
    {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal]
    (q : U.principalUnitSubgroupClassInQuotient l n) :
    U.principalUnitClassQuotientKerEquivClassOfLe hlm hmn
        (QuotientGroup.mk' (U.principalUnitClassMapOfLe hlm hmn).ker q) =
      U.principalUnitClassMapOfLe hlm hmn q := by
  exact QuotientGroup.kerLift_mk (U.principalUnitClassMapOfLe hlm hmn) q

/-- The third-isomorphism equivalence for principal-unit filtration quotients:
`(G / U^n) / (U^m / U^n) ≃ G / U^m` when `m ≤ n`. -/
noncomputable def quotientModuloPrincipalUnitClassEquivQuotientOfLe
    {m n : ℕ} (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] :
    (G ⧸ U.principalUnitSubgroup n) ⧸
        U.principalUnitSubgroupClassInQuotient m n ≃*
      G ⧸ U.principalUnitSubgroup m :=
  QuotientGroup.quotientQuotientEquivQuotient
    (U.principalUnitSubgroup n) (U.principalUnitSubgroup m)
    (U.principalUnitSubgroup_antitone hmn)

/--
Establishes the identity `U.quotientModuloPrincipalUnitClassEquivQuotientOfLe hmn
(QuotientGroup.mk' (U.principalUnitSubgroupClassInQuotient m n) q) =
U.quotient_principalUnitSubgroup_mapOfLe hmn q`.
-/
@[simp] theorem quotientModuloPrincipalUnitClassEquivQuotientOfLe_mk
    {m n : ℕ} (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal]
    (q : G ⧸ U.principalUnitSubgroup n) :
    U.quotientModuloPrincipalUnitClassEquivQuotientOfLe hmn
        (QuotientGroup.mk'
          (U.principalUnitSubgroupClassInQuotient m n) q) =
      U.quotient_principalUnitSubgroup_mapOfLe hmn q := by
  change
    QuotientGroup.quotientQuotientEquivQuotientAux
        (U.principalUnitSubgroup n) (U.principalUnitSubgroup m)
        (U.principalUnitSubgroup_antitone hmn) q =
      U.quotient_principalUnitSubgroup_mapOfLe hmn q
  exact
    QuotientGroup.quotientQuotientEquivQuotientAux_mk
      (N := U.principalUnitSubgroup n)
      (M := U.principalUnitSubgroup m)
      (h := U.principalUnitSubgroup_antitone hmn) q

/--
Establishes the identity `U.quotientModuloPrincipalUnitClassEquivQuotientOfLe hmn
(QuotientGroup.mk' (U.principalUnitSubgroupClassInQuotient m n) (QuotientGroup.mk'
(U.principalUnitSubgroup n) x)) = QuotientGroup.mk' (U.principalUnitSubgroup m) x`.
-/
@[simp] theorem quotientModuloPrincipalUnitClassEquivQuotientOfLe_mk_mk
    {m n : ℕ} (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] (x : G) :
    U.quotientModuloPrincipalUnitClassEquivQuotientOfLe hmn
        (QuotientGroup.mk'
          (U.principalUnitSubgroupClassInQuotient m n)
          (QuotientGroup.mk' (U.principalUnitSubgroup n) x)) =
      QuotientGroup.mk' (U.principalUnitSubgroup m) x := by
  rw [U.quotientModuloPrincipalUnitClassEquivQuotientOfLe_mk hmn,
    U.quotient_principalUnitSubgroup_mapOfLe_apply_mk' hmn x]

/--
Establishes the identity `(U.quotientModuloPrincipalUnitClassEquivQuotientOfLe hmn).symm
(QuotientGroup.mk' (U.principalUnitSubgroup m) x) = QuotientGroup.mk'
(U.principalUnitSubgroupClassInQuotient m n) (QuotientGroup.mk' (U.principalUnitSubgroup n) x)`.
-/
@[simp] theorem quotientModuloPrincipalUnitClassEquivQuotientOfLe_symm_mk
    {m n : ℕ} (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] (x : G) :
    (U.quotientModuloPrincipalUnitClassEquivQuotientOfLe hmn).symm
        (QuotientGroup.mk' (U.principalUnitSubgroup m) x) =
      QuotientGroup.mk' (U.principalUnitSubgroupClassInQuotient m n)
        (QuotientGroup.mk' (U.principalUnitSubgroup n) x) := by
  apply (U.quotientModuloPrincipalUnitClassEquivQuotientOfLe hmn).injective
  calc
    U.quotientModuloPrincipalUnitClassEquivQuotientOfLe hmn
        ((U.quotientModuloPrincipalUnitClassEquivQuotientOfLe hmn).symm
          (QuotientGroup.mk' (U.principalUnitSubgroup m) x)) =
      QuotientGroup.mk' (U.principalUnitSubgroup m) x := by
        exact (U.quotientModuloPrincipalUnitClassEquivQuotientOfLe hmn).apply_symm_apply _
    _ =
      U.quotientModuloPrincipalUnitClassEquivQuotientOfLe hmn
        (QuotientGroup.mk' (U.principalUnitSubgroupClassInQuotient m n)
          (QuotientGroup.mk' (U.principalUnitSubgroup n) x)) := by
        rw [U.quotientModuloPrincipalUnitClassEquivQuotientOfLe_mk_mk hmn x]

end AntitoneSubgroupFiltration

end DiscreteValuationField

end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_NormFiltration
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.LubinTate.compatibleGroupFamiliesGroup _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.ofWithZeroValuation_val _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalFieldTheory

/-!
# Norm compatibility with unit filtrations

A compatibility hypothesis for a norm and two unit filtrations immediately
produces homomorphisms on every filtration level.
-/

noncomputable section

universe u v

namespace DiscreteValuationField
namespace ValuedNorm

variable {G : Type u} {H : Type v} [Group G] [Group H]
variable {vG : MultiplicativeIntegerValuation G}
variable {vH : MultiplicativeIntegerValuation H}
variable (N : ValuedNorm vG vH)
variable (UG : AntitoneSubgroupFiltration G) (UH : AntitoneSubgroupFiltration H)
variable (targetLevel : ℕ → ℕ)

/-- A compatibility hypothesis for the norm and two filtrations. -/
abbrev MapsFiltrationLevels : Prop :=
  ∀ n {x : H}, x ∈ UH.principalUnitSubgroup n →
    N.toHom x ∈ UG.principalUnitSubgroup (targetLevel n)

/-- The norm map restricted to a filtration level. -/
def mapLevelOfMapsFiltrationLevels
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ) :
    UH.principalUnitSubgroup n →* UG.principalUnitSubgroup (targetLevel n) where
  toFun x := ⟨N.toHom x.1, hN n x.2⟩
  map_one' := by
    apply Subtype.ext
    exact N.toHom.map_one
  map_mul' x y := by
    apply Subtype.ext
    exact N.toHom.map_mul x.1 y.1

/--
The defining evaluation formula for `mapLevelOfMapsFiltrationLevels` is
`(mapLevelOfMapsFiltrationLevels N UG UH targetLevel hN n x : G) = N.toHom x.1`.
-/
@[simp] theorem mapLevelOfMapsFiltrationLevels_apply
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    (x : UH.principalUnitSubgroup n) :
    (mapLevelOfMapsFiltrationLevels N UG UH targetLevel hN n x : G) =
      N.toHom x.1 :=
  rfl

/-- A compatible norm descends to the quotient by a filtration level. -/
def quotientMapOfMapsFiltrationLevels
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal] :
    H ⧸ UH.principalUnitSubgroup n →*
      G ⧸ UG.principalUnitSubgroup (targetLevel n) :=
  QuotientGroup.map (UH.principalUnitSubgroup n)
    (UG.principalUnitSubgroup (targetLevel n)) N.toHom (by
      intro x hx
      exact hN n hx)

/--
The defining evaluation formula for `quotientMapOfMapsFiltrationLevels` is
`quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n (QuotientGroup.mk x) =
QuotientGroup.mk (N.toHom x)`.
-/
@[simp] theorem quotientMapOfMapsFiltrationLevels_apply_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal] (x : H) :
    quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n
        (QuotientGroup.mk x) =
      QuotientGroup.mk (N.toHom x) :=
  rfl

/--
Establishes the identity `quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n
(QuotientGroup.mk' (UH.principalUnitSubgroup n) x) = QuotientGroup.mk' (UG.principalUnitSubgroup
(targetLevel n)) (N.toHom x)`.
-/
@[simp] theorem quotientMapOfMapsFiltrationLevels_apply_mk'
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal] (x : H) :
    quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n
        (QuotientGroup.mk' (UH.principalUnitSubgroup n) x) =
      QuotientGroup.mk' (UG.principalUnitSubgroup (targetLevel n))
        (N.toHom x) :=
  rfl

/-- The preimage of the target filtration subgroup under the valued norm. -/
def filtrationPreimageSubgroup (n : ℕ) : Subgroup H :=
  (UG.principalUnitSubgroup (targetLevel n)).comap N.toHom

/--
Characterizes `x ∈ N.filtrationPreimageSubgroup UG targetLevel n` by the equivalent condition
`N.toHom x ∈ UG.principalUnitSubgroup (targetLevel n)`.
-/
@[simp] theorem mem_filtrationPreimageSubgroup_iff (n : ℕ) (x : H) :
    x ∈ N.filtrationPreimageSubgroup UG targetLevel n ↔
      N.toHom x ∈ UG.principalUnitSubgroup (targetLevel n) :=
  Iff.rfl

/-- The subgroup appearing in `(N.filtrationPreimageSubgroup UG targetLevel n).Normal` is normal. -/
instance filtrationPreimageSubgroup_normal
    (n : ℕ) [(UG.principalUnitSubgroup (targetLevel n)).Normal] :
    (N.filtrationPreimageSubgroup UG targetLevel n).Normal := by
  dsimp [filtrationPreimageSubgroup]
  infer_instance

/-- The class of the norm-preimage of the target filtration subgroup inside
the source quotient `H ⧸ U_H^n`. -/
def filtrationPreimageClassInQuotient (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal] :
    Subgroup (H ⧸ UH.principalUnitSubgroup n) :=
  Subgroup.map (QuotientGroup.mk' (UH.principalUnitSubgroup n))
    (N.filtrationPreimageSubgroup UG targetLevel n)

/--
The subgroup appearing in `(N.filtrationPreimageClassInQuotient UG UH targetLevel n).Normal` is
normal.
-/
instance filtrationPreimageClassInQuotient_normal
    (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal] :
    (N.filtrationPreimageClassInQuotient UG UH targetLevel n).Normal := by
  dsimp [filtrationPreimageClassInQuotient]
  infer_instance

/-- The kernel of the quotient norm map is the class of the preimage of the
target filtration subgroup in the source quotient. -/
theorem quotientMapOfMapsFiltrationLevels_ker_eq_filtrationPreimageClass
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal] :
    (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).ker =
      N.filtrationPreimageClassInQuotient UG UH targetLevel n := by
  exact QuotientGroup.ker_map (UH.principalUnitSubgroup n)
    (UG.principalUnitSubgroup (targetLevel n)) N.toHom (fun _ hx => hN n hx)

/-- First-isomorphism form of the filtration quotient norm map, with codomain
the actual range when no surjectivity hypothesis is available. -/
noncomputable def quotientModuloFiltrationPreimageClassEquivRange
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal] :
    (H ⧸ UH.principalUnitSubgroup n) ⧸
        N.filtrationPreimageClassInQuotient UG UH targetLevel n ≃*
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).range :=
  (QuotientGroup.quotientMulEquivOfEq
      (N.quotientMapOfMapsFiltrationLevels_ker_eq_filtrationPreimageClass
        UG UH targetLevel hN n).symm).trans
    (QuotientGroup.quotientKerEquivRange
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n))

/--
Establishes the identity `N.quotientModuloFiltrationPreimageClassEquivRange UG UH targetLevel hN n
(QuotientGroup.mk' (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q) =
(quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).rangeRestrict q`.
-/
@[simp] theorem quotientModuloFiltrationPreimageClassEquivRange_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal]
    (q : H ⧸ UH.principalUnitSubgroup n) :
    N.quotientModuloFiltrationPreimageClassEquivRange
        UG UH targetLevel hN n
        (QuotientGroup.mk'
          (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q) =
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).rangeRestrict q :=
  rfl

/--
Establishes the identity `N.quotientModuloFiltrationPreimageClassEquivRange UG UH targetLevel hN n
(QuotientGroup.mk' (N.filtrationPreimageClassInQuotient UG UH targetLevel n) (QuotientGroup.mk'
(UH.principalUnitSubgroup n) x)) = (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN
n).rangeRestrict (QuotientGroup.mk' (UH.principalUnitSubgroup n) x)`.
-/
@[simp] theorem quotientModuloFiltrationPreimageClassEquivRange_mk_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal] (x : H) :
    N.quotientModuloFiltrationPreimageClassEquivRange
        UG UH targetLevel hN n
        (QuotientGroup.mk'
          (N.filtrationPreimageClassInQuotient UG UH targetLevel n)
          (QuotientGroup.mk' (UH.principalUnitSubgroup n) x)) =
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).rangeRestrict
        (QuotientGroup.mk' (UH.principalUnitSubgroup n) x) :=
  rfl

/--
Establishes the identity `((N.quotientModuloFiltrationPreimageClassEquivRange UG UH targetLevel hN
n (QuotientGroup.mk' (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q) :
(quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).range) : G ⧸ UG.principalUnitSubgroup
(targetLevel n)) = quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n q`.
-/
@[simp] theorem coe_quotientModuloFiltrationPreimageClassEquivRange_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal]
    (q : H ⧸ UH.principalUnitSubgroup n) :
    ((N.quotientModuloFiltrationPreimageClassEquivRange
        UG UH targetLevel hN n
        (QuotientGroup.mk'
          (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q) :
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).range) :
        G ⧸ UG.principalUnitSubgroup (targetLevel n)) =
      quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n q := by
  rw [N.quotientModuloFiltrationPreimageClassEquivRange_mk
    UG UH targetLevel hN n q]
  rfl

/--
Establishes the identity `((N.quotientModuloFiltrationPreimageClassEquivRange UG UH targetLevel hN
n (QuotientGroup.mk' (N.filtrationPreimageClassInQuotient UG UH targetLevel n) (QuotientGroup.mk'
(UH.principalUnitSubgroup n) x)) : (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN
n).range) : G ⧸ UG.principalUnitSubgroup (targetLevel n)) = QuotientGroup.mk'
(UG.principalUnitSubgroup (targetLevel n)) (N.toHom x)`.
-/
@[simp] theorem coe_quotientModuloFiltrationPreimageClassEquivRange_mk_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal] (x : H) :
    ((N.quotientModuloFiltrationPreimageClassEquivRange
        UG UH targetLevel hN n
        (QuotientGroup.mk'
          (N.filtrationPreimageClassInQuotient UG UH targetLevel n)
          (QuotientGroup.mk' (UH.principalUnitSubgroup n) x)) :
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).range) :
        G ⧸ UG.principalUnitSubgroup (targetLevel n)) =
      QuotientGroup.mk' (UG.principalUnitSubgroup (targetLevel n))
        (N.toHom x) := by
  rw [N.coe_quotientModuloFiltrationPreimageClassEquivRange_mk
    UG UH targetLevel hN n
    (QuotientGroup.mk' (UH.principalUnitSubgroup n) x),
    N.quotientMapOfMapsFiltrationLevels_apply_mk' UG UH targetLevel hN n x]

/--
Establishes the identity `(N.quotientModuloFiltrationPreimageClassEquivRange UG UH targetLevel hN
n).symm ((quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).rangeRestrict q) =
QuotientGroup.mk' (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q`.
-/
@[simp] theorem quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal]
    (q : H ⧸ UH.principalUnitSubgroup n) :
    (N.quotientModuloFiltrationPreimageClassEquivRange
        UG UH targetLevel hN n).symm
        ((quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).rangeRestrict q) =
      QuotientGroup.mk'
        (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q := by
  apply (N.quotientModuloFiltrationPreimageClassEquivRange
    UG UH targetLevel hN n).injective
  calc
    N.quotientModuloFiltrationPreimageClassEquivRange
        UG UH targetLevel hN n
        ((N.quotientModuloFiltrationPreimageClassEquivRange
          UG UH targetLevel hN n).symm
          ((quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).rangeRestrict q)) =
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).rangeRestrict q := by
        exact
          (N.quotientModuloFiltrationPreimageClassEquivRange
            UG UH targetLevel hN n).apply_symm_apply _
    _ =
      N.quotientModuloFiltrationPreimageClassEquivRange
        UG UH targetLevel hN n
        (QuotientGroup.mk'
          (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q) := by
        rw [N.quotientModuloFiltrationPreimageClassEquivRange_mk
          UG UH targetLevel hN n q]

/--
Establishes the identity `(N.quotientModuloFiltrationPreimageClassEquivRange UG UH targetLevel hN
n).symm ((quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).rangeRestrict
(QuotientGroup.mk' (UH.principalUnitSubgroup n) x)) = QuotientGroup.mk'
(N.filtrationPreimageClassInQuotient UG UH targetLevel n) (QuotientGroup.mk'
(UH.principalUnitSubgroup n) x)`.
-/
@[simp] theorem quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal] (x : H) :
    (N.quotientModuloFiltrationPreimageClassEquivRange
        UG UH targetLevel hN n).symm
        ((quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).rangeRestrict
          (QuotientGroup.mk' (UH.principalUnitSubgroup n) x)) =
      QuotientGroup.mk'
        (N.filtrationPreimageClassInQuotient UG UH targetLevel n)
        (QuotientGroup.mk' (UH.principalUnitSubgroup n) x) := by
  rw [N.quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict
    UG UH targetLevel hN n]

/-- A filtration-compatible norm induces maps on principal-unit subquotients:
`U_H^m/U_H^n → U_G^(targetLevel m)/U_G^(targetLevel n)`. -/
def principalUnitSubquotientMapOfMapsFiltrationLevels
    (hN : MapsFiltrationLevels N UG UH targetLevel) {m n : ℕ}
    (_hmn : m ≤ n) (_htarget : targetLevel m ≤ targetLevel n)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal] :
    UH.principalUnitSubquotient m n →*
      UG.principalUnitSubquotient (targetLevel m) (targetLevel n) :=
  UH.principalUnitSubquotientLift m n
    ((UG.principalUnitSubquotientMk (targetLevel m) (targetLevel n)).comp
      (mapLevelOfMapsFiltrationLevels N UG UH targetLevel hN m))
    (by
      intro x hx
      change UG.principalUnitSubquotientMk (targetLevel m) (targetLevel n)
          (mapLevelOfMapsFiltrationLevels N UG UH targetLevel hN m x) = 1
      rw [UG.principalUnitSubquotient_mk_eq_one_iff]
      exact hN n hx)

/--
The defining evaluation formula for `principalUnitSubquotientMapOfMapsFiltrationLevels` is
`N.principalUnitSubquotientMapOfMapsFiltrationLevels UG UH targetLevel hN hmn htarget
(UH.principalUnitSubquotientMk m n x) = UG.principalUnitSubquotientMk (targetLevel m) (targetLevel
n) (mapLevelOfMapsFiltrationLevels N UG UH targetLevel hN m x)`.
-/
@[simp] theorem principalUnitSubquotientMapOfMapsFiltrationLevels_apply_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) {m n : ℕ}
    (hmn : m ≤ n) (htarget : targetLevel m ≤ targetLevel n)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal]
    (x : UH.principalUnitSubgroup m) :
    N.principalUnitSubquotientMapOfMapsFiltrationLevels
        UG UH targetLevel hN hmn htarget
        (UH.principalUnitSubquotientMk m n x) =
      UG.principalUnitSubquotientMk (targetLevel m) (targetLevel n)
        (mapLevelOfMapsFiltrationLevels N UG UH targetLevel hN m x) :=
  rfl

/-- The subquotient norm map agrees with the ambient quotient norm map under
the canonical embeddings of subquotients as classes in ambient quotients. -/
@[simp] theorem coe_principalUnitSubquotientEquivClassInQuotient_map
    (hN : MapsFiltrationLevels N UG UH targetLevel) {m n : ℕ}
    (hmn : m ≤ n) (htarget : targetLevel m ≤ targetLevel n)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal]
    (z : UH.principalUnitSubquotient m n) :
    ((UG.principalUnitSubquotientEquivClassInQuotientOfLe htarget
        (N.principalUnitSubquotientMapOfMapsFiltrationLevels
          UG UH targetLevel hN hmn htarget z) :
      UG.principalUnitSubgroupClassInQuotient (targetLevel m)
        (targetLevel n)) :
      G ⧸ UG.principalUnitSubgroup (targetLevel n)) =
      quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n
        ((UH.principalUnitSubquotientEquivClassInQuotientOfLe hmn z :
          UH.principalUnitSubgroupClassInQuotient m n) :
          H ⧸ UH.principalUnitSubgroup n) := by
  refine
    AntitoneSubgroupFiltration.principalUnitSubquotient.inductionOn
      UH m n
        (motive := fun z' ↦
          ((UG.principalUnitSubquotientEquivClassInQuotientOfLe htarget
              (N.principalUnitSubquotientMapOfMapsFiltrationLevels
                UG UH targetLevel hN hmn htarget z') :
            UG.principalUnitSubgroupClassInQuotient (targetLevel m)
              (targetLevel n)) :
            G ⧸ UG.principalUnitSubgroup (targetLevel n)) =
          quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n
            ((UH.principalUnitSubquotientEquivClassInQuotientOfLe hmn z' :
              UH.principalUnitSubgroupClassInQuotient m n) :
              H ⧸ UH.principalUnitSubgroup n)) z ?_
  intro x
  simp

/-- The graded-piece form of
`principalUnitSubquotientMapOfMapsFiltrationLevels`. -/
def principalUnitGradedPieceMapOfMapsFiltrationLevels
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    (htarget : targetLevel n ≤ targetLevel (n + 1))
    [(UH.principalUnitSubgroup (n + 1)).Normal]
    [(UG.principalUnitSubgroup (targetLevel (n + 1))).Normal] :
    UH.principalUnitGradedPiece n →*
      UG.principalUnitSubquotient (targetLevel n) (targetLevel (n + 1)) :=
  (N.principalUnitSubquotientMapOfMapsFiltrationLevels
    UG UH targetLevel hN (Nat.le_succ n) htarget).comp
      (UH.principalUnitGradedPieceEquivSubquotient n).toMonoidHom

/--
The defining evaluation formula for `principalUnitGradedPieceMapOfMapsFiltrationLevels` is
`N.principalUnitGradedPieceMapOfMapsFiltrationLevels UG UH targetLevel hN n htarget
(UH.principalUnitGradedPieceMk n x) = UG.principalUnitSubquotientMk (targetLevel n) (targetLevel
(n + 1)) (mapLevelOfMapsFiltrationLevels N UG UH targetLevel hN n x)`.
-/
@[simp] theorem principalUnitGradedPieceMapOfMapsFiltrationLevels_apply_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    (htarget : targetLevel n ≤ targetLevel (n + 1))
    [(UH.principalUnitSubgroup (n + 1)).Normal]
    [(UG.principalUnitSubgroup (targetLevel (n + 1))).Normal]
    (x : UH.principalUnitSubgroup n) :
    N.principalUnitGradedPieceMapOfMapsFiltrationLevels
        UG UH targetLevel hN n htarget
        (UH.principalUnitGradedPieceMk n x) =
      UG.principalUnitSubquotientMk (targetLevel n) (targetLevel (n + 1))
        (mapLevelOfMapsFiltrationLevels N UG UH targetLevel hN n x) :=
  rfl

end ValuedNorm
end DiscreteValuationField

end

end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_IdealQuotients
attribute [-instance] _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.CyclicCohomology.mem_chosenBaseUniformizerPowSubmodule_iff _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-! ### Residue and maximal-ideal successive quotients -/

lemma withZeroMultiplicativeInt_le_of_lt_one
    (δ : WithZero (Multiplicative Int)) (hδ : δ < 1) :
    δ ≤ ((Multiplicative.ofAdd (-1 : Int) : Multiplicative Int) :
      WithZero (Multiplicative Int)) := by
  cases δ using WithZero.recZeroCoe with
  | zero => exact bot_le
  | coe d =>
      rw [WithZero.coe_le_coe]
      rw [← Multiplicative.toAdd_le]
      change Multiplicative.toAdd d ≤ (-1 : Int)
      have hdlt : Multiplicative.toAdd d < (0 : Int) := by
        have h' : d < (1 : Multiplicative Int) := by
          simpa using hδ
        change Multiplicative.toAdd d < Multiplicative.toAdd (1 : Multiplicative Int)
        exact Multiplicative.toAdd_lt.mpr h'
      omega

lemma withZeroMultiplicativeInt_maximal_lt_one_eq_ofAdd_neg_one
    {a : WithZero (Multiplicative Int)} (ha : a < 1)
    (hmax : ∀ δ : WithZero (Multiplicative Int), δ < 1 → δ ≤ a) :
    a = ((Multiplicative.ofAdd (-1 : Int) : Multiplicative Int) :
      WithZero (Multiplicative Int)) := by
  apply le_antisymm
  · exact withZeroMultiplicativeInt_le_of_lt_one a ha
  · apply hmax
    rw [← WithZero.coe_one, WithZero.coe_lt_coe]
    change (-1 : Int) < 0
    omega

theorem valueGroupWithZeroIsoInt_eq_of_maximal_lt_one
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    {a : ValuativeRel.ValueGroupWithZero K} (ha : a < 1)
    (hmax : ∀ δ : ValuativeRel.ValueGroupWithZero K, δ < 1 → δ ≤ a) :
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K a =
      ((Multiplicative.ofAdd (-1 : Int) : Multiplicative Int) :
        WithZero (Multiplicative Int)) := by
  let φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  apply withZeroMultiplicativeInt_maximal_lt_one_eq_ofAdd_neg_one
  · simpa using φ.strictMono ha
  · intro δ hδ
    let ε : ValuativeRel.ValueGroupWithZero K := φ.symm δ
    have hε : ε < 1 := by
      have h := φ.symm.strictMono hδ
      simpa using h
    have hle : ε ≤ a := hmax ε hε
    have hle' := φ.strictMono.monotone hle
    dsimp [ε, φ] at hle'
    simpa using hle'

/-- any prime element of the valuation ring has
multiplicative value `ofAdd (-1)` under the local-field normalization.

The proof is the DVR argument used in this construction: `𝓂 = (ϖ)`, so every
valuation value below `1` is bounded by the value of `ϖ`; in the normalized
value group this maximal element below `1` is `ofAdd (-1)`. -/
theorem valueGroupWithZeroIsoInt_of_integerRing_irreducible
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ) :
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
        (ValuativeRel.valuation K ((ϖ : 𝒪[K]) : K)) =
      ((Multiplicative.ofAdd (-1 : Int) : Multiplicative Int) :
        WithZero (Multiplicative Int)) := by
  apply valueGroupWithZeroIsoInt_eq_of_maximal_lt_one K
  · simpa using (Valuation.integer.v_irreducible_lt_one
      (v := ValuativeRel.valuation K) hϖ)
  · intro δ hδ
    obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (K := K) δ
    by_cases hx0 : x = 0
    · have hδ0 : δ = 0 := by
        simpa [hx0] using hx.symm
      rw [hδ0]
      exact bot_le
    · let y : 𝒪[K] := ⟨x, by
        change ValuativeRel.valuation K x ≤ 1
        rw [hx]
        exact le_of_lt hδ⟩
      have hylt : ValuativeRel.valuation K (y : K) < 1 := by
        change ValuativeRel.valuation K x < 1
        simpa [hx]
      have hynot : ¬ IsUnit y := by
        rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one
          (v := ValuativeRel.valuation K)]
        exact hylt
      have hym : y ∈ (𝓂[K] : Ideal 𝒪[K]) := by
        rw [IsLocalRing.mem_maximalIdeal]
        simpa [nonunits] using hynot
      have hyspan : y ∈
          (Ideal.span ({ϖ} : Set 𝒪[K]) : Ideal 𝒪[K]) := by
        simpa [hϖ.maximalIdeal_eq] using hym
      have hset := Valuation.integer.coe_span_singleton_eq_setOfPred_le_v_coe
        (v := ValuativeRel.valuation K) ϖ
      have hyle : ValuativeRel.valuation K (y : K) ≤
          ValuativeRel.valuation K ((ϖ : 𝒪[K]) : K) := by
        have hyspanSet : y ∈
            ((Ideal.span ({ϖ} : Set 𝒪[K]) : Ideal 𝒪[K]) : Set 𝒪[K]) := hyspan
        rw [hset] at hyspanSet
        exact hyspanSet
      simpa [y, hx] using hyle

/-- A field unit whose value is represented by a valuation-ring prime element
has normalized additive value `-1`. -/
theorem v_integerRingIrreducibleFieldUnit
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (u : Kˣ) (hu : (u : K) = ((ϖ : 𝒪[K]) : K)) :
    LocalFieldTheory.IsNonarchimedeanLocalField.v K (Additive.ofMul u) = -1 := by
  dsimp [LocalFieldTheory.IsNonarchimedeanLocalField.v]
  have hne :
      IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
          (ValuativeRel.valuation K ((u : Kˣ) : K)) ≠ 0 := by
    rw [hu]
    simp [hϖ.ne_zero]
  have hunzero :
      WithZero.unzero
        (x := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
          (ValuativeRel.valuation K ((u : Kˣ) : K))) hne =
        (Multiplicative.ofAdd (-1 : Int) : Multiplicative Int) := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero]
    rw [hu]
    simpa using valueGroupWithZeroIsoInt_of_integerRing_irreducible K ϖ hϖ
  rw [hunzero]
  simp

/-- The inverse of a field unit represented by a valuation-ring prime element
has normalized additive value `1`. -/
theorem v_integerRingIrreducibleFieldUnit_inv
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (u : Kˣ) (hu : (u : K) = ((ϖ : 𝒪[K]) : K)) :
    LocalFieldTheory.IsNonarchimedeanLocalField.v K (Additive.ofMul u⁻¹) = 1 := by
  rw [LocalFieldTheory.IsNonarchimedeanLocalField.v_inv]
  rw [v_integerRingIrreducibleFieldUnit K ϖ hϖ u hu]
  norm_num

/-- The chosen valuation-ring prime element has normalized additive value `-1`
as a field unit.  We use the inverse convention for a positive
uniformizer in the exact sequence. -/
theorem v_integerRingUniformizerFieldUnit
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    LocalFieldTheory.IsNonarchimedeanLocalField.v K
      (Additive.ofMul (integerRingUniformizerFieldUnit K)) = -1 := by
  exact v_integerRingIrreducibleFieldUnit K
    (chosenIntegerRingUniformizer K) (chosenIntegerRingUniformizer_irreducible K)
    (integerRingUniformizerFieldUnit K) rfl

/-- The inverse of the chosen valuation-ring prime element has normalized
additive value `1`.  This is the source object needed before using powers of a
uniformizer in the local class-field calculation. -/
theorem v_inverseIntegerRingUniformizerFieldUnit
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    LocalFieldTheory.IsNonarchimedeanLocalField.v K
      (Additive.ofMul (inverseIntegerRingUniformizerFieldUnit K)) = 1 := by
  rw [inverseIntegerRingUniformizerFieldUnit]
  exact v_integerRingIrreducibleFieldUnit_inv K
    (chosenIntegerRingUniformizer K) (chosenIntegerRingUniformizer_irreducible K)
    (integerRingUniformizerFieldUnit K) rfl

/-- Denominator clearing in the valuation ring:
every element of `K` becomes integral after multiplying by a sufficiently high
power of the chosen prime element of `𝒪[K]`.

This local-DVR denominator-clearing theorem supports normal-basis lattice bounds; the
proof uses the fraction representation over `𝒪[K]` and the DVR factorization of
the denominator into a unit times a power of the prime element. -/
theorem exists_chosenIntegerRingUniformizer_pow_mul_mem_integerRing
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : K) :
    ∃ n : Nat,
      (((chosenIntegerRingUniformizer K : 𝒪[K]) : K) ^ n) * x ∈ 𝒪[K] := by
  obtain ⟨a, b, hb, hfrac⟩ := IsFractionRing.div_surjective (A := 𝒪[K]) x
  have hb_ne : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨n, u, hb_factor⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb_ne
      (chosenIntegerRingUniformizer_irreducible K)
  refine ⟨n, ?_⟩
  rw [← hfrac, hb_factor]
  have hϖ_ne : (((chosenIntegerRingUniformizer K : 𝒪[K]) : K)) ≠ 0 := by
    intro h
    exact (chosenIntegerRingUniformizer_irreducible K).ne_zero
      ((IsFractionRing.injective 𝒪[K] K) h)
  have hϖ_pow_ne :
      (((chosenIntegerRingUniformizer K : 𝒪[K]) : K) ^ n) ≠ 0 :=
    pow_ne_zero n hϖ_ne
  have hu_ne : (((u : 𝒪[K]) : K)) ≠ 0 := by
    intro h
    exact u.ne_zero ((IsFractionRing.injective 𝒪[K] K) h)
  have hclear :
      (((chosenIntegerRingUniformizer K : 𝒪[K]) : K) ^ n) *
          ((a : K) /
            (((u : 𝒪[K]) * chosenIntegerRingUniformizer K ^ n : 𝒪[K]) : K)) =
        ((a * ↑u⁻¹ : 𝒪[K]) : K) := by
    calc
      (((chosenIntegerRingUniformizer K : 𝒪[K]) : K) ^ n) *
          ((a : K) /
            (((u : 𝒪[K]) * chosenIntegerRingUniformizer K ^ n : 𝒪[K]) : K))
          =
          (((chosenIntegerRingUniformizer K : 𝒪[K]) : K) ^ n) *
            ((a : K) / (((u : 𝒪[K]) : K) *
              (((chosenIntegerRingUniformizer K : 𝒪[K]) : K) ^ n))) := by
            simp
      _ = (a : K) * (((u : 𝒪[K]) : K))⁻¹ := by
            field_simp [hu_ne, hϖ_pow_ne]
      _ = ((a * ↑u⁻¹ : 𝒪[K]) : K) := by
            have hu_inv :
                (((↑u⁻¹ : 𝒪[K]) : K)) = (((u : 𝒪[K]) : K))⁻¹ := by
              exact map_units_inv (algebraMap 𝒪[K] K) u
            rw [← hu_inv]
            simp
  change (((chosenIntegerRingUniformizer K : 𝒪[K]) : K) ^ n) *
      ((a : K) /
        (((u : 𝒪[K]) * chosenIntegerRingUniformizer K ^ n : 𝒪[K]) : K)) ∈ 𝒪[K]
  rw [hclear]
  exact (a * ↑u⁻¹ : 𝒪[K]).2

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_ClassGroup_Core
attribute [-instance] _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The ordinary ideal class group as an idele quotient

This file proves that quotienting the idele group by the
ideles integral at every finite place and by the principal ideles gives the
ordinary ideal class group.
-/

open scoped NumberField RestrictedProduct WithZero
open NumberField IsDedekindDomain

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace IdeleGroup

/-- The exponent of a prime in a principal fractional ideal is the additive
form of the corresponding normalized finite-place valuation. -/
theorem count_toPrincipalIdeal (x : Kˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v
        ((toPrincipalIdeal (𝓞 K) K x : FractionalIdealGroup K) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      -WithZero.log (v.valuation K (x : K)) := by
  obtain ⟨⟨n, d, hd⟩, hnd⟩ :=
    IsLocalization.surj (nonZeroDivisors (𝓞 K)) (x : K)
  let d' : nonZeroDivisors (𝓞 K) := ⟨d, hd⟩
  have hx :
      (x : K) = IsLocalization.mk' K n d' :=
    IsLocalization.eq_mk'_iff_mul_eq.mpr hnd
  have hn : n ≠ 0 := by
    intro hn
    have : (x : K) = 0 := by
      rw [hx, hn, IsFractionRing.mk'_eq_div, map_zero, zero_div]
    exact x.ne_zero this
  have hspan :
      (toPrincipalIdeal (𝓞 K) K x :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
        FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
            ((algebraMap (𝓞 K) K) d)⁻¹ *
          (Ideal.span {n} :
            FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    rw [coe_toPrincipalIdeal, hx,
      FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton,
      IsFractionRing.mk'_eq_div, div_eq_mul_inv, mul_comm]
  rw [FractionalIdeal.count_well_defined K v
      (Units.ne_zero (toPrincipalIdeal (𝓞 K) K x)) hspan,
    hx, v.valuation_of_mk']
  rw [v.intValuation_if_neg hn,
    v.intValuation_if_neg (nonZeroDivisors.coe_ne_zero d')]
  simp [d', sub_eq_add_neg, add_comm]

end IdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Topology
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.FiniteIdeleGroup.mem_integralSubgroup_iff _root_.FiniteIdeleGroup.valuationVectorAdd_apply _root_.FiniteIdeleGroup.valuationVector_apply _root_.FiniteIdeleGroup.valuationVector_valuationVectorSection _root_.IdeleGroup.finiteComponent_principalIdele _root_.IdeleGroup.infiniteComponent_principalIdele _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.RelativeIdeleGroup.Cohomology.ideleClassNorm_mk _root_.RelativeIdeleGroup.classInclusion_mk _root_.RelativeIdeleGroup.classNorm_mk _root_.RelativeIdeleGroup.inclusion_principalIdele _root_.RelativeIdeleGroup.norm_inclusion _root_.RelativeIdeleGroup.norm_principalIdele _root_.RelativeIdeleGroup.smul_inclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The idele topology

The idele group `I_K` carries the restricted-product topology. This file records
the topological-group structure and the continuity of every local
component map.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section


variable (K : Type*) [Field K] [NumberField K]

namespace IdeleGroup

variable {K}

/-- Evaluation at an archimedean place is a continuous homomorphism. -/
def infiniteComponentContinuous (v : InfinitePlace K) :
    IdeleGroup K →ₜ* v.Completionˣ where
  __ := infiniteComponent v
  continuous_toFun :=
    (continuous_apply v).comp
      (ContinuousMulEquiv.piUnits.continuous.comp continuous_fst)

/-- Evaluation at a finite place is a continuous homomorphism. -/
def finiteComponentContinuous (v : HeightOneSpectrum (𝓞 K)) :
    IdeleGroup K →ₜ* (v.adicCompletion K)ˣ where
  __ := finiteComponent v
  continuous_toFun :=
    (RestrictedProduct.continuous_eval v).comp continuous_snd

@[simp]
theorem infiniteComponentContinuous_apply
    (a : IdeleGroup K) (v : InfinitePlace K) :
    infiniteComponentContinuous v a =
      ContinuousMulEquiv.piUnits a.1 v :=
  rfl

@[simp]
theorem finiteComponentContinuous_apply
    (a : IdeleGroup K) (v : HeightOneSpectrum (𝓞 K)) :
    finiteComponentContinuous v a = a.2 v :=
  rfl

end IdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_LocallyCompact
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Local compactness of the idele group

The topology on the finite ideles is the restricted-product topology from
`AlgebraicNumberTheory.Idele.Topology`.  We prove local compactness by showing
that every finite completion is proper, that its integral unit group is
compact, and then applying the restricted-product theorem.
-/

open scoped NumberField RestrictedProduct Valued
open NumberField IsDedekindDomain

noncomputable section


variable (K : Type*) [Field K] [NumberField K]

/-- The integral unit group in a finite completion is compact. -/
theorem isCompact_finiteLocalUnits
    (v : HeightOneSpectrum (𝓞 K)) :
    IsCompact
      ((v.adicCompletionIntegers K).units :
        Set (v.adicCompletion K)ˣ) := by
  apply Submonoid.units_isCompact
  change IsCompact
    ((Valued.integer (v.adicCompletion K)) :
      Set (v.adicCompletion K))
  exact isCompact_iff_compactSpace.mpr
    (Valued.integer.properSpace_iff_compactSpace_integer.mp inferInstance)
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_SPlaces
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IdeleGroup.finiteComponent_principalIdele _root_.IdeleGroup.infiniteComponent_principalIdele _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.RelativeIdeleGroup.Cohomology.ideleClassNorm_mk _root_.RelativeIdeleGroup.classInclusion_mk _root_.RelativeIdeleGroup.classNorm_mk _root_.RelativeIdeleGroup.inclusion_principalIdele _root_.RelativeIdeleGroup.norm_inclusion _root_.RelativeIdeleGroup.norm_principalIdele _root_.RelativeIdeleGroup.smul_inclusion
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

namespace FiniteIdeleGroup

/-- The finite ideles that are integral units away from `S`. -/
def supportedAt (S : Set (HeightOneSpectrum (𝓞 K))) :
    Subgroup (FiniteIdeleGroup K) where
  carrier := {a | ∀ v, v ∉ S →
    a v ∈ (v.adicCompletionIntegers K).units}
  one_mem' _ _ := Submonoid.one_mem _
  mul_mem' ha hb v hv := Submonoid.mul_mem _
    (ha v hv) (hb v hv)
  inv_mem' ha v hv := Subgroup.inv_mem _
    (ha v hv)

@[simp]
theorem mem_supportedAt_iff
    (S : Set (HeightOneSpectrum (𝓞 K)))
    (a : FiniteIdeleGroup K) :
    a ∈ supportedAt (K := K) S ↔
      ∀ v, v ∉ S →
        a v ∈ (v.adicCompletionIntegers K).units :=
  Iff.rfl

theorem supportedAt_mono {S T : Set (HeightOneSpectrum (𝓞 K))}
    (hST : S ⊆ T) :
    supportedAt (K := K) S ≤ supportedAt (K := K) T := by
  intro a ha v hv
  exact ha v (fun h => hv (hST h))

theorem mem_supportedAt_nonLocalUnits
    (a : FiniteIdeleGroup K) :
    a ∈ supportedAt (K := K)
      {v | a v ∉ (v.adicCompletionIntegers K).units} := by
  intro v hv
  simpa using hv

/-- Every finite idele is supported at some finite set of finite places. -/
theorem exists_finset_supportedAt (a : FiniteIdeleGroup K) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      a ∈ supportedAt (K := K) (S : Set _) := by
  let T : Set (HeightOneSpectrum (𝓞 K)) :=
    {v | a v ∉ (v.adicCompletionIntegers K).units}
  have hT : T.Finite := Filter.eventually_cofinite.mp a.2
  exact ⟨hT.toFinset, by
    rw [Set.Finite.coe_toFinset]
    exact mem_supportedAt_nonLocalUnits a⟩

/-- For a finite set `S`, the `S`-finite-ideles form an open subgroup. -/
theorem isOpen_supportedAt (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IsOpen
      ((supportedAt (K := K) (S : Set _) :
        Subgroup (FiniteIdeleGroup K)) : Set (FiniteIdeleGroup K)) := by
  change IsOpen {a : FiniteIdeleGroup K | ∀ v, v ∉ (S : Set _) →
    a v ∈ (v.adicCompletionIntegers K).units}
  exact RestrictedProduct.isOpen_forall_imp_mem
    (fun v => isOpen_finiteLocalUnits K v)

end FiniteIdeleGroup

namespace IdeleGroup

/-- The group `I_K^S`, with all infinite places included and finite
components integral away from `S`. -/
def supportedAt (S : Set (HeightOneSpectrum (𝓞 K))) :
    Subgroup (IdeleGroup K) :=
  Subgroup.comap (MonoidHom.snd _ _)
    (FiniteIdeleGroup.supportedAt S)

@[simp]
theorem mem_supportedAt_iff
    (S : Set (HeightOneSpectrum (𝓞 K)))
    (a : IdeleGroup K) :
    a ∈ supportedAt (K := K) S ↔
      ∀ v, v ∉ S →
        a.2 v ∈ (v.adicCompletionIntegers K).units :=
  Iff.rfl

end IdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_GaloisCohomology
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace CyclicCohomology

/-!
# Cyclic Tate low-degree boundary

For a finite cyclic group generated by `g`, mathlib computes odd group
cohomology using `Rep.FiniteCyclicGroup.subCompNormHom A g`.  The canonical
boundary comparison identifies that short-complex homology with
`tateCohomology A (-1)`.

This file applies that comparison to unit representations.  The resulting
objects are mathlib's Tate cohomology objects directly; no parallel
low-degree model is introduced.
-/

noncomputable section

open CategoryTheory

/-- Low-degree Tate periodicity in degree one:
for a finite cyclic group, `H¹(G,A)` is canonically isomorphic to mathlib's
degree-minus-one Tate cohomology. -/
noncomputable def cyclic_H1_iso_HminusOne {k G : Type} [CommRing k] [Group G]
    [Fintype G] (A : Rep k G) (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    groupCohomology A 1 ≅ tateCohomology A (-1) := by
  letI : IsCyclic G := isCyclic_of_forall_mem_zpowers g hg
  letI : CommGroup G := IsCyclic.commGroup (α := G)
  exact Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg 1 (by decide) ≪≫
    (TateCohomology.isoFiniteCyclicNegOne A g hg).symm

/-- The cyclic low-degree comparison for the unit representation. -/
noncomputable def unitsH1IsoTateHminusOne (K L : Type) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] (g : Gal(L / K))
    (hg : ∀ x : Gal(L / K), x ∈ Subgroup.zpowers g) :
    groupCohomology.H1 (Rep.ofAlgebraAutOnUnits K L) ≅
      tateCohomology (Rep.ofAlgebraAutOnUnits K L) (-1) :=
  cyclic_H1_iso_HminusOne (Rep.ofAlgebraAutOnUnits K L) g hg

/-- Hilbert 90 transported through the cyclic `H¹ ≅ H^{-1}` comparison.
This is low-degree cyclic Tate cohomology for the coefficient group `Lˣ`: the vanishing of
`H¹(G,Lˣ)` gives the vanishing of `H^{-1}(G,Lˣ)`. -/
theorem hilbert90_unitsTateHminusOne_isZero (K L : Type) [Field K]
    [Field L] [Algebra K L] [FiniteDimensional K L] (g : Gal(L / K))
    (hg : ∀ x : Gal(L / K), x ∈ Subgroup.zpowers g) :
    CategoryTheory.Limits.IsZero
      (tateCohomology (Rep.ofAlgebraAutOnUnits K L) (-1)) := by
  have hzero :
      CategoryTheory.Limits.IsZero
        (groupCohomology.H1 (Rep.ofAlgebraAutOnUnits K L)) := by
    let _ := groupCohomology.H1ofAutOnUnitsUnique K L
    exact ModuleCat.isZero_of_subsingleton _
  exact hzero.of_iso
    (unitsH1IsoTateHminusOne K L g hg).symm

end
end CyclicCohomology
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_HerbrandLowDegree_BinaryProduct
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Low-degree Tate cohomology of binary products

This specializes the dependent-product calculation to two possibly
different coefficient groups.  It is used to join the unrestricted and
integral parts of a supported idele group.
-/

noncomputable section

namespace CyclicCohomology

open CyclicCohomology.ProfiniteCohomology.Herbrand

universe uG uA

variable {G : Type uG} [Group G] [Fintype G]
variable (A B : Type uA)
variable [CommGroup A] [CommGroup B]
variable [MulDistribMulAction G A] [MulDistribMulAction G B]

omit [Fintype G] in
/-- The binary reindexing is equivariant for the componentwise
actions. -/
theorem prodEquivBinaryCoefficientFamily_smul
    (g : G) (x : A × B) :
    letI : ∀ i, MulDistribMulAction G
        (BinaryCoefficientFamily A B i) :=
      binaryCoefficientFamilyAction A B
    letI : MulDistribMulAction G
        (∀ i, BinaryCoefficientFamily A B i) :=
      piMulDistribMulAction G
        (BinaryCoefficientFamily A B)
    prodEquivBinaryCoefficientFamily A B (g • x) =
      g • prodEquivBinaryCoefficientFamily A B x := by
  funext i
  cases i <;> rfl

end CyclicCohomology
end
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_NormalBasisLattice
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

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

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

omit [FiniteDimensional K L] [IsGalois K L]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- An additive `𝒪_K`-submodule containing a neighborhood of `0` is open. -/
theorem submodule_isOpen_of_mem_nhds_zero
    [TopologicalSpace L] [IsTopologicalAddGroup L]
    {E : Submodule 𝒪[K] L} (hE : (E : Set L) ∈ nhds (0 : L)) :
    IsOpen (E : Set L) := by
  simpa using AddSubgroup.isOpen_of_mem_nhds E.toAddSubgroup hE

omit [FiniteDimensional K L] [IsGalois K L]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- An open additive `𝒪_K`-submodule is closed. -/
theorem submodule_isClosed_of_isOpen
    [TopologicalSpace L] [IsTopologicalAddGroup L]
    {E : Submodule 𝒪[K] L} (hE : IsOpen (E : Set L)) :
    IsClosed (E : Set L) := by
  simpa using AddSubgroup.isClosed_of_isOpen E.toAddSubgroup hE

omit [FiniteDimensional K L] [IsGalois K L]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- A neighborhood submodule is closed in a topological additive group. -/
theorem submodule_isClosed_of_mem_nhds_zero
    [TopologicalSpace L] [IsTopologicalAddGroup L]
    {E : Submodule 𝒪[K] L} (hE : (E : Set L) ∈ nhds (0 : L)) :
    IsClosed (E : Set L) :=
  submodule_isClosed_of_isOpen (K := K) (L := L)
    (submodule_isOpen_of_mem_nhds_zero (K := K) (L := L) hE)

end
end CyclicCohomology

universe u
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_Basic
attribute [-instance] _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
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

/-- The valuation subring of a discrete valuation field is an integral domain. -/
instance valuationSubring.isDomain (F : DVF.{u, v} K) :
    IsDomain F.valuationSubring :=
  ValuationSubring.instIsDomainSubtypeMem F.valuation.valuationSubring

/-- The valuation subring of a DVF is a DVR. -/
theorem valuationSubring_isDiscreteValuationRing (F : DVF.{u, v} K) :
    IsDiscreteValuationRing F.valuationSubring :=
  Valuation.valuationSubring_isDiscreteValuationRing F.valuation

/-- A DVF has a uniformizer in its valuation subring. -/
theorem exists_uniformizer (F : DVF.{u, v} K) :
    Exists (fun pi : F.valuationSubring => F.valuation.IsUniformizer (pi : K)) := by
  change Exists
    (fun pi : F.valuation.valuationSubring => F.valuation.IsUniformizer (pi : K))
  exact Valuation.exists_isUniformizer_of_isCyclic_of_nontrivial F.valuation

/-- A uniformizer lies in the maximal ideal. -/
theorem uniformizer_mem_maximalIdeal (F : DVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K)) :
    pi ∈ F.maximalIdeal := by
  change pi ∈ IsLocalRing.maximalIdeal F.valuation.valuationSubring
  exact (Valuation.mem_maximalIdeal_iff (v := F.valuation)).2 hpi.val_lt_one

/-! ### Successive quotients of powers of the maximal ideal -/

end DVF
end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_Henselian
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
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

namespace HenselianDVF

variable {K : Type u} [Field K]

/-- Introduces the abbreviation `maximalIdeal`. -/
abbrev maximalIdeal (F : HenselianDVF.{u, v} K) : Ideal F.valuationSubring :=
  F.toDVF.maximalIdeal

end HenselianDVF

end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_Complete
attribute [-instance] _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply
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

/-- Introduces the abbreviation `maximalIdeal`. -/
abbrev maximalIdeal (F : CompleteDVF.{u, v} K) : Ideal F.valuationSubring :=
  F.toHenselianDVF.maximalIdeal

/-- The valuation subring in the complete model is a discrete valuation ring. -/
theorem valuationSubring_isDiscreteValuationRing (F : CompleteDVF.{u, v} K) :
    IsDiscreteValuationRing F.valuationSubring :=
  F.toDVF.valuationSubring_isDiscreteValuationRing

/-- The complete DVR model is complete for its maximal-ideal-adic topology. -/
theorem isAdicComplete (F : CompleteDVF.{u, v} K) :
    IsAdicComplete F.maximalIdeal F.valuationSubring := by
  change IsAdicComplete
    (IsLocalRing.maximalIdeal F.valuation.valuationSubring)
    F.valuation.valuationSubring
  exact Valuation.isAdicComplete F.valuation

/-- A complete discrete valuation field admits a uniformizer. -/
theorem exists_uniformizer (F : CompleteDVF.{u, v} K) :
    Exists (fun pi : F.valuationSubring => F.valuation.IsUniformizer (pi : K)) :=
  F.toDVF.exists_uniformizer

/-- Every chosen uniformizer lies in the maximal ideal. -/
theorem uniformizer_mem_maximalIdeal (F : CompleteDVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K)) :
    pi ∈ F.maximalIdeal :=
  F.toDVF.uniformizer_mem_maximalIdeal hpi

/-- The maximal ideal of a complete DVF valuation ring is nonzero. -/
theorem maximalIdeal_ne_bot (F : CompleteDVF.{u, v} K) :
    F.maximalIdeal ≠ ⊥ := by
  rcases F.exists_uniformizer with ⟨pi, hpi⟩
  intro hbot
  have hmem : pi ∈ (⊥ : Ideal F.valuationSubring) := by
    rw [← hbot]
    exact F.uniformizer_mem_maximalIdeal hpi
  have hzero_sub : pi = 0 := by
    simpa using hmem
  apply hpi.ne_zero
  exact Subtype.ext_iff.mp hzero_sub

end CompleteDVF
end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_ValuationExtension
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ValuationTheory

/-!
# Valuation extensions

Mathlib's uniqueness criterion for valuations is expressed through
`Valuation.IsEquiv`: two valuations on the same field are equivalent exactly
when they have the same valuation subring.  The results here use the ambient
valued-extension property directly; no marker object is introduced.
-/

noncomputable section

universe u v w x y

namespace DiscreteValuationField
namespace ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]

section Comparison

variable (target : CompleteDVF.{w, x} L)

/-- Equality of valuation subrings implies valuation equivalence. -/
theorem valuation_isEquiv_of_valuationSubring_eq
    {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma')
    (hsub : target.valuation.valuationSubring = v'.valuationSubring) :
    target.valuation.IsEquiv v' :=
  (_root_.Valuation.isEquiv_iff_valuationSubring target.valuation v').2 hsub

end Comparison
end ValuedExtension
end DiscreteValuationField
end
end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_IntegralClosure
attribute [-instance] _root_.HilbertRamification.Dedekind.basePrime_isPrime _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply
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

/-- The valuation ring of a complete DVF is a fraction ring inside the field. -/
theorem base_valuationSubring_isFractionRing (base : CompleteDVF.{u, v} K) :
    IsFractionRing base.toDVF.valuationSubring K :=
  (Valuation.valuationSubring.integers (v := base.valuation)).isFractionRing

/-- The valuation ring of a complete DVF is integrally closed. -/
theorem base_valuationSubring_isIntegrallyClosed
    (base : CompleteDVF.{u, v} K) :
    IsIntegrallyClosed base.toDVF.valuationSubring := by
  exact inferInstanceAs (IsIntegrallyClosed base.valuation.valuationSubring)

/-- The valuation ring of a complete DVF is Noetherian. -/
theorem base_valuationSubring_isNoetherianRing
    (base : CompleteDVF.{u, v} K) :
    IsNoetherianRing base.toDVF.valuationSubring := by
  have : IsDiscreteValuationRing base.toDVF.valuationSubring :=
    base.valuationSubring_isDiscreteValuationRing
  infer_instance

/-- The actual integral closure of the base valuation ring in the extension
field. -/
abbrev integralClosureIntegers (base : CompleteDVF.{u, v} K)
    (_target : CompleteDVF.{w, x} L) : Type _ :=
  integralClosure base.toDVF.valuationSubring L

omit [FiniteDimensional K L] [base.valuation.HasExtension target.valuation] in
/-- The actual integral closure is integral over the base valuation ring. -/
theorem integralClosure_isIntegral :
    Algebra.IsIntegral base.toDVF.valuationSubring (integralClosureIntegers base target) := by
  exact inferInstanceAs
    (Algebra.IsIntegral base.toDVF.valuationSubring
      (integralClosure base.toDVF.valuationSubring L))

omit [base.valuation.HasExtension target.valuation] in
/-- The algebra map from the base valuation ring into the actual integral
closure is injective. -/
theorem integralClosure_algebraMap_injective :
    Function.Injective
      (algebraMap base.toDVF.valuationSubring (integralClosureIntegers base target)) := by
  intro x y hxy
  apply Subtype.ext
  apply FaithfulSMul.algebraMap_injective K L
  exact congrArg (fun z : (integralClosureIntegers base target) => (z : L)) hxy

omit [base.valuation.HasExtension target.valuation] in
/-- The actual integral closure is faithful over the base valuation ring. -/
theorem integralClosure_faithfulSMul :
    FaithfulSMul base.toDVF.valuationSubring (integralClosureIntegers base target) :=
  (faithfulSMul_iff_algebraMap_injective
    base.toDVF.valuationSubring (integralClosureIntegers base target)).mpr
    (integralClosure_algebraMap_injective base target)

omit [base.valuation.HasExtension target.valuation] in
/-- In a finite separable field extension, the actual integral closure is
module-finite over the base valuation ring. -/
theorem moduleFinite_integralClosureIntegers
    [Algebra.IsSeparable K L] :
    Module.Finite base.toDVF.valuationSubring (integralClosureIntegers base target) := by
  let : IsFractionRing base.toDVF.valuationSubring K :=
    base_valuationSubring_isFractionRing (K := K) base
  let : IsIntegrallyClosed base.toDVF.valuationSubring :=
    base_valuationSubring_isIntegrallyClosed (K := K) base
  let : IsNoetherianRing base.toDVF.valuationSubring :=
    base_valuationSubring_isNoetherianRing (K := K) base
  exact
    (show Module.Finite base.toDVF.valuationSubring
        (integralClosure base.toDVF.valuationSubring L) from
      IsIntegralClosure.finite base.toDVF.valuationSubring K L
        (integralClosure base.toDVF.valuationSubring L))

omit [base.valuation.HasExtension target.valuation] in
/-- In a finite separable field extension, the actual integral closure is
quasi-finite over the base valuation ring. -/
theorem integralClosure_quasiFinite
    [Algebra.IsSeparable K L] :
    Algebra.QuasiFinite base.toDVF.valuationSubring (integralClosureIntegers base target) := by
  let : Module.Finite base.toDVF.valuationSubring (integralClosureIntegers base target) :=
    (moduleFinite_integralClosureIntegers base target)
  infer_instance

omit [base.valuation.HasExtension target.valuation] in
/-- The residue fiber of the finite actual integral closure over the base
maximal ideal is Artinian. -/
theorem integralClosure_base_maximal_fiber_isArtinianRing
    [Algebra.IsSeparable K L] :
    IsArtinianRing (base.maximalIdeal.Fiber (integralClosureIntegers base target)) := by
  let : Algebra.QuasiFinite base.toDVF.valuationSubring (integralClosureIntegers base target) :=
    (integralClosure_quasiFinite base target)
  infer_instance

omit [FiniteDimensional K L] [base.valuation.HasExtension target.valuation] in
/-- For the actual integral closure, the kernel of the residue-fiber
includeRight map is the ideal generated by the base maximal ideal. -/
theorem integralClosure_base_maximal_fiber_includeRight_ker_eq_maximalIdeal_map
     :
    RingHom.ker
        ((Algebra.TensorProduct.includeRight :
          (integralClosureIntegers base target) →ₐ[base.toDVF.valuationSubring]
            base.maximalIdeal.Fiber (integralClosureIntegers base target)) :
          (integralClosureIntegers base target) →+*
            base.maximalIdeal.Fiber (integralClosureIntegers base target)) =
      base.maximalIdeal.map
        (algebraMap base.toDVF.valuationSubring (integralClosureIntegers base target)) := by
  simpa using
    (maximalIdeal_fiber_includeRight_ker_eq_maximalIdeal_map
      (R := base.toDVF.valuationSubring) (S := (integralClosureIntegers base target)))

omit [FiniteDimensional K L] [base.valuation.HasExtension target.valuation] in
/-- Idempotents in the actual integral closure in the extension field are
trivial.

This keeps the Henselian frontier focused on lifting idempotents out of the
finite residue fiber: once an idempotent has lifted to the actual integral
closure, domainhood inside the field forces it to be `0` or `1`. -/
theorem integralClosure_idempotent_eq_zero_or_one
    (e : (integralClosureIntegers base target))
    (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  let : IsDomain (integralClosureIntegers base target) := by
    exact inferInstanceAs
      (IsDomain (integralClosure base.toDVF.valuationSubring L))
  exact IsIdempotentElem.iff_eq_zero_or_one.mp he

omit [base.valuation.HasExtension target.valuation] in
/-- If every idempotent of the residue fiber over the base maximal ideal lifts
to an idempotent of the actual integral closure, then that fiber has at most
one prime.

This packages the topological Artinian-fiber/idempotent argument in the form
needed by the Henselian finite-extension proof. -/
theorem integralClosure_base_maximal_fiber_subsingleton_of_idempotents_lift
    [Algebra.IsSeparable K L]
    (hlift :
      ∀ e : base.maximalIdeal.Fiber (integralClosureIntegers base target),
        IsIdempotentElem e →
          ∃ b : (integralClosureIntegers base target),
            IsIdempotentElem b ∧
              Algebra.TensorProduct.includeRight b = e) :
    Subsingleton
      (PrimeSpectrum (base.maximalIdeal.Fiber (integralClosureIntegers base target))) := by
  let : IsArtinianRing
      (base.maximalIdeal.Fiber (integralClosureIntegers base target)) :=
    (integralClosure_base_maximal_fiber_isArtinianRing base target)
  refine primeSpectrum_subsingleton_of_isArtinianRing_of_idempotents_trivial ?_
  intro e he
  rcases hlift e he with ⟨b, hbidem, hbmap⟩
  rcases (integralClosure_idempotent_eq_zero_or_one base target) b hbidem with rfl | rfl
  · left
    rw [← hbmap]
    simp
  · right
    rw [← hbmap]
    exact (Algebra.TensorProduct.includeRight :
      (integralClosureIntegers base target) →ₐ[base.toDVF.valuationSubring]
        base.maximalIdeal.Fiber (integralClosureIntegers base target)).map_one

omit [FiniteDimensional K L] [base.valuation.HasExtension target.valuation] in
/-- Henselian-kernel form of idempotent lifting for the residue fiber of the
actual integral closure.

The remaining Henselian finite-extension work can now focus on proving that
the `includeRight` map to the finite residue fiber is surjective and has
Henselian kernel; the idempotent lifting itself is supplied by Hensel's lemma
for `X^2 - X`. -/
theorem
integralClosure_base_maximal_fiber_idempotents_lift_of_includeRight_surjective_henselianRing_ker
    (hsurj :
      Function.Surjective
        (Algebra.TensorProduct.includeRight :
          (integralClosureIntegers base target) →ₐ[base.toDVF.valuationSubring]
            base.maximalIdeal.Fiber (integralClosureIntegers base target)))
    [HenselianRing (integralClosureIntegers base target)
      (RingHom.ker
        ((Algebra.TensorProduct.includeRight :
          (integralClosureIntegers base target) →ₐ[base.toDVF.valuationSubring]
            base.maximalIdeal.Fiber (integralClosureIntegers base target)) :
          (integralClosureIntegers base target) →+*
            base.maximalIdeal.Fiber (integralClosureIntegers base target)))] :
    ∀ e : base.maximalIdeal.Fiber (integralClosureIntegers base target),
      IsIdempotentElem e →
        ∃ b : (integralClosureIntegers base target),
          IsIdempotentElem b ∧
            Algebra.TensorProduct.includeRight b = e := by
  intro e he
  let φ : (integralClosureIntegers base target) →+*
      base.maximalIdeal.Fiber (integralClosureIntegers base target) :=
    (Algebra.TensorProduct.includeRight :
      (integralClosureIntegers base target) →ₐ[base.toDVF.valuationSubring]
        base.maximalIdeal.Fiber (integralClosureIntegers base target))
  have hsurjφ : Function.Surjective φ := by
    simpa [φ] using hsurj
  rcases exists_idempotent_lift_of_surjective_henselianRing_ker
      φ hsurjφ e he with
    ⟨b, hbidem, hbmap⟩
  exact ⟨b, hbidem, by simpa [φ] using hbmap⟩

omit [FiniteDimensional K L] [base.valuation.HasExtension target.valuation] in
/-- Henselian-kernel idempotent lifting for the residue fiber of the actual
integral closure.

The `includeRight` map is automatically surjective because the base valuation
ring is local. -/
theorem integralClosure_base_maximal_fiber_idempotents_lift_of_includeRight_henselianRing_ker
    [HenselianRing (integralClosureIntegers base target)
      (RingHom.ker
        ((Algebra.TensorProduct.includeRight :
          (integralClosureIntegers base target) →ₐ[base.toDVF.valuationSubring]
            base.maximalIdeal.Fiber (integralClosureIntegers base target)) :
          (integralClosureIntegers base target) →+*
            base.maximalIdeal.Fiber (integralClosureIntegers base target)))] :
    ∀ e : base.maximalIdeal.Fiber (integralClosureIntegers base target),
      IsIdempotentElem e →
        ∃ b : (integralClosureIntegers base target),
          IsIdempotentElem b ∧
            Algebra.TensorProduct.includeRight b = e := by
  refine (
integralClosure_base_maximal_fiber_idempotents_lift_of_includeRight_surjective_henselianRing_ker
    base target) ?_
  simpa using
    (maximalIdeal_fiber_includeRight_surjective
      (R := base.toDVF.valuationSubring) (S := (integralClosureIntegers base target)))

omit [base.valuation.HasExtension target.valuation] in
/-- If the `includeRight` map to the residue fiber has Henselian kernel, then
the fiber has at most one prime. -/
theorem integralClosure_base_maximal_fiber_subsingleton_of_includeRight_henselianRing_ker
    [Algebra.IsSeparable K L]
    [HenselianRing (integralClosureIntegers base target)
      (RingHom.ker
        ((Algebra.TensorProduct.includeRight :
          (integralClosureIntegers base target) →ₐ[base.toDVF.valuationSubring]
            base.maximalIdeal.Fiber (integralClosureIntegers base target)) :
          (integralClosureIntegers base target) →+*
            base.maximalIdeal.Fiber (integralClosureIntegers base target)))] :
    Subsingleton
      (PrimeSpectrum (base.maximalIdeal.Fiber (integralClosureIntegers base target))) := by
  refine
    (integralClosure_base_maximal_fiber_subsingleton_of_idempotents_lift base target) ?_
  exact
    (integralClosure_base_maximal_fiber_idempotents_lift_of_includeRight_henselianRing_ker
      base target)

omit [base.valuation.HasExtension target.valuation] in
/-- If the ideal generated by the base maximal ideal is Henselian in the actual
integral closure, then the residue fiber has at most one prime. -/
theorem integralClosure_base_maximal_fiber_subsingleton_of_henselianRing_maximalIdeal_map
    [Algebra.IsSeparable K L]
    [HenselianRing (integralClosureIntegers base target)
      (base.maximalIdeal.map
        (algebraMap base.toDVF.valuationSubring (integralClosureIntegers base target)))] :
    Subsingleton
      (PrimeSpectrum (base.maximalIdeal.Fiber (integralClosureIntegers base target))) := by
  let : HenselianRing (integralClosureIntegers base target)
      (RingHom.ker
        ((Algebra.TensorProduct.includeRight :
          (integralClosureIntegers base target) →ₐ[base.toDVF.valuationSubring]
            base.maximalIdeal.Fiber (integralClosureIntegers base target)) :
          (integralClosureIntegers base target) →+*
            base.maximalIdeal.Fiber (integralClosureIntegers base target))) := by
    rw [(integralClosure_base_maximal_fiber_includeRight_ker_eq_maximalIdeal_map base target)]
    infer_instance
  exact
    (integralClosure_base_maximal_fiber_subsingleton_of_includeRight_henselianRing_ker base target)



omit [base.valuation.HasExtension target.valuation] in
/-- In a finite separable extension of complete DVFs, the natural ideal generated
by the base maximal ideal is Henselian in the actual integral closure.

This packages the finite-module completeness theorem together with the
comparison between I-adic and I.map-adic completeness. -/
theorem integralClosure_base_maximal_map_henselianRing
    [Algebra.IsSeparable K L] :
    HenselianRing (integralClosureIntegers base target)
      (base.maximalIdeal.map
        (algebraMap base.toDVF.valuationSubring (integralClosureIntegers base target))) := by
  let : IsNoetherianRing base.toDVF.valuationSubring :=
    base_valuationSubring_isNoetherianRing (K := K) base
  let : Module.Finite base.toDVF.valuationSubring (integralClosureIntegers base target) :=
    (moduleFinite_integralClosureIntegers base target)
  have : IsAdicComplete base.maximalIdeal base.toDVF.valuationSubring :=
    base.isAdicComplete
  have hcomplete : IsAdicComplete base.maximalIdeal (integralClosureIntegers base target) :=
    ValuationTheory.DiscreteValuationField.isAdicComplete_of_moduleFinite
      (I := base.maximalIdeal)
  have hmapComplete :
      IsAdicComplete
        (base.maximalIdeal.map
          (algebraMap base.toDVF.valuationSubring (integralClosureIntegers base target)))
        (integralClosureIntegers base target) :=
    (isAdicComplete_map_algebraMap_iff
      (I := base.maximalIdeal) (S := (integralClosureIntegers base target))).mpr hcomplete
  have := hmapComplete
  infer_instance

omit [base.valuation.HasExtension target.valuation] in
/-- The actual integral closure has at least one prime above the base maximal
ideal. -/
theorem integralClosure_primesOver_base_maximal_nonempty
     :
    Nonempty (Ideal.primesOver base.maximalIdeal (integralClosureIntegers base target)) := by
  let : Algebra.IsIntegral base.toDVF.valuationSubring (integralClosureIntegers base target) :=
    (integralClosure_isIntegral base target)
  let : FaithfulSMul base.toDVF.valuationSubring (integralClosureIntegers base target) :=
    (integralClosure_faithfulSMul base target)
  rcases Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (S := (integralClosureIntegers base target)) base.maximalIdeal with
    ⟨P, hPmax, hPover⟩
  exact ⟨⟨P, hPmax.isPrime, hPover⟩⟩

omit [FiniteDimensional K L] [base.valuation.HasExtension target.valuation] in
/-- If the residue fiber over the base maximal ideal has at most one prime,
then so does the actual set of primes above the base maximal ideal. -/
theorem integralClosure_primesOver_base_maximal_subsingleton_of_fiber_subsingleton
    [Subsingleton
      (PrimeSpectrum (base.maximalIdeal.Fiber (integralClosureIntegers base target)))] :
    Subsingleton
      (Ideal.primesOver base.maximalIdeal (integralClosureIntegers base target)) := by
  constructor
  intro P Q
  let e := PrimeSpectrum.primesOverOrderIsoFiber
    base.toDVF.valuationSubring (integralClosureIntegers base target) base.maximalIdeal
  exact e.injective (Subsingleton.elim (e P) (e Q))

omit [base.valuation.HasExtension target.valuation] in
/-- If the residue fiber over the base maximal ideal has at most one prime,
then the primes of the actual integral closure over the base maximal ideal form
a singleton. -/
theorem integralClosure_primesOver_base_maximal_eq_singleton_of_fiber_subsingleton
    [Subsingleton
      (PrimeSpectrum (base.maximalIdeal.Fiber (integralClosureIntegers base target)))] :
    ∃ P : Ideal (integralClosureIntegers base target),
      Ideal.primesOver base.maximalIdeal (integralClosureIntegers base target) = {P} := by
  let : Subsingleton
      (Ideal.primesOver base.maximalIdeal (integralClosureIntegers base target)) :=
    (integralClosure_primesOver_base_maximal_subsingleton_of_fiber_subsingleton base target)
  rcases (integralClosure_primesOver_base_maximal_nonempty base target) with ⟨P⟩
  refine ⟨P, Set.eq_singleton_iff_unique_mem.mpr ⟨P.2, ?_⟩⟩
  intro Q hQ
  exact congrArg Subtype.val
    (Subsingleton.elim
      (⟨Q, hQ⟩ :
        Ideal.primesOver base.maximalIdeal (integralClosureIntegers base target)) P)

omit [base.valuation.HasExtension target.valuation] in
/-- The actual integral closure is a fraction ring for the finite field
extension. -/
theorem integralClosure_isFractionRing :
    IsFractionRing (integralClosureIntegers base target) L := by
  let : IsFractionRing base.toDVF.valuationSubring K :=
    base_valuationSubring_isFractionRing (K := K) base
  exact
    (show IsFractionRing (integralClosure base.toDVF.valuationSubring L) L from
      integralClosure.isFractionRing_of_finite_extension K L)

omit [base.valuation.HasExtension target.valuation] in
/-- If the actual integral closure is a valuation ring, then it satisfies the
valuative dichotomy inside the extension field.

This is the local/DVR-oriented bridge for the Henselian frontier: after proving
that the finite integral closure is local, one can obtain a valuation-ring
instance and feed this theorem into the finite-separable uniqueness API. -/
theorem integralClosure_mem_or_inv_of_integralClosure_valuationRing
    [ValuationRing (integralClosureIntegers base target)] :
    ∀ z : L,
      z ∈ (integralClosure base.toDVF.valuationSubring L).toSubring ∨
        z⁻¹ ∈ (integralClosure base.toDVF.valuationSubring L).toSubring := by
  let : IsFractionRing (integralClosureIntegers base target) L :=
    (integralClosure_isFractionRing base target)
  intro z
  rcases ValuationRing.isInteger_or_isInteger
      (R := (integralClosureIntegers base target)) (K := L) z with hz | hz
  · left
    rcases hz with ⟨y, hy⟩
    rw [← hy]
    exact y.2
  · right
    rcases hz with ⟨y, hy⟩
    rw [← hy]
    exact y.2

omit [base.valuation.HasExtension target.valuation] in
/-- If the base valuation ring is used as a fraction ring for `K` and the field
extension is separable, the integral closure is Dedekind. -/
theorem integralClosure_isDedekindDomain
    [IsFractionRing base.toDVF.valuationSubring K] [Algebra.IsSeparable K L] :
    IsDedekindDomain (integralClosureIntegers base target) := by
  exact
    (show IsDedekindDomain (integralClosure base.toDVF.valuationSubring L) from
      integralClosure.isDedekindDomain base.toDVF.valuationSubring K L)

omit [FiniteDimensional K L] [base.valuation.HasExtension target.valuation] in
/-- If the primes of the actual integral closure over the base maximal ideal
form a singleton, then the actual integral closure is local.

For integral extensions, every maximal ideal upstairs lies over a maximal ideal
downstairs.  Since the base valuation ring is local, all maximal ideals upstairs
therefore lie over `base.maximalIdeal`; the singleton hypothesis makes the
maximal spectrum upstairs a singleton. -/
theorem integralClosure_isLocalRing_of_primesOver_base_maximal_eq_singleton
    (P : Ideal (integralClosureIntegers base target))
    (hP :
      Ideal.primesOver base.maximalIdeal (integralClosureIntegers base target) = {P}) :
    IsLocalRing (integralClosureIntegers base target) := by
  let : Algebra.IsIntegral base.toDVF.valuationSubring (integralClosureIntegers base target) :=
    (integralClosure_isIntegral base target)
  have hPmem : P ∈ Ideal.primesOver base.maximalIdeal (integralClosureIntegers base target) := by
    rw [hP]
    exact Set.mem_singleton P
  let : Nonempty (MaximalSpectrum (integralClosureIntegers base target)) :=
    ⟨⟨P, Ideal.isMaximal_of_mem_primesOver hPmem⟩⟩
  have hsub :
      Subsingleton (MaximalSpectrum (integralClosureIntegers base target)) := by
    constructor
    intro M N
    apply MaximalSpectrum.ext
    have hMcomap :
        (M.asIdeal.comap
            (algebraMap base.toDVF.valuationSubring (integralClosureIntegers base target))) =
          base.maximalIdeal :=
      IsLocalRing.eq_maximalIdeal
        (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal'
          (R := base.toDVF.valuationSubring)
          (S := (integralClosureIntegers base target))
          (algebraMap base.toDVF.valuationSubring (integralClosureIntegers base target))
          (fun x => Algebra.IsIntegral.isIntegral x) M.asIdeal)
    have hNcomap :
        (N.asIdeal.comap
            (algebraMap base.toDVF.valuationSubring (integralClosureIntegers base target))) =
          base.maximalIdeal :=
      IsLocalRing.eq_maximalIdeal
        (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal'
          (R := base.toDVF.valuationSubring)
          (S := (integralClosureIntegers base target))
          (algebraMap base.toDVF.valuationSubring (integralClosureIntegers base target))
          (fun x => Algebra.IsIntegral.isIntegral x) N.asIdeal)
    have hMmem :
        M.asIdeal ∈ Ideal.primesOver base.maximalIdeal
          (integralClosureIntegers base target) :=
      ⟨M.isMaximal.isPrime, ⟨hMcomap.symm⟩⟩
    have hNmem :
        N.asIdeal ∈ Ideal.primesOver base.maximalIdeal
          (integralClosureIntegers base target) :=
      ⟨N.isMaximal.isPrime, ⟨hNcomap.symm⟩⟩
    have hMeq : M.asIdeal = P := by
      simpa [hP] using hMmem
    have hNeq : N.asIdeal = P := by
      simpa [hP] using hNmem
    exact hMeq.trans hNeq.symm
  exact IsLocalRing.of_singleton_maximalSpectrum

omit [base.valuation.HasExtension target.valuation] in
/-- If the residue fiber over the base maximal ideal has at most one prime,
then the actual integral closure is local. -/
theorem integralClosure_isLocalRing_of_base_maximal_fiber_subsingleton
    [Subsingleton
      (PrimeSpectrum (base.maximalIdeal.Fiber (integralClosureIntegers base target)))] :
    IsLocalRing (integralClosureIntegers base target) := by
  rcases
      (integralClosure_primesOver_base_maximal_eq_singleton_of_fiber_subsingleton
        base target) with
    ⟨P, hP⟩
  exact (integralClosure_isLocalRing_of_primesOver_base_maximal_eq_singleton base target) P hP

omit [base.valuation.HasExtension target.valuation] in
/-- A local actual integral closure in a finite separable extension of a complete
DVF is a valuation ring.

The Henselian frontier can therefore aim only at localness of the finite
integral closure.  Dedekind theory and mathlib's local Noetherian-domain TFAE
then turn that local integral closure into a valuation ring, giving the
valuative dichotomy needed by the finite-extension uniqueness bridge. -/
theorem integralClosure_valuationRing_of_isLocalRing
    [Algebra.IsSeparable K L]
    [IsLocalRing (integralClosureIntegers base target)] :
    ValuationRing (integralClosureIntegers base target) := by
  let : IsFractionRing base.toDVF.valuationSubring K :=
    base_valuationSubring_isFractionRing (K := K) base
  let : IsIntegrallyClosed base.toDVF.valuationSubring :=
    base_valuationSubring_isIntegrallyClosed (K := K) base
  let : IsNoetherianRing base.toDVF.valuationSubring :=
    base_valuationSubring_isNoetherianRing (K := K) base
  let : IsDomain (integralClosureIntegers base target) := by
    exact inferInstanceAs
      (IsDomain (integralClosure base.toDVF.valuationSubring L))
  let : IsDedekindDomain (integralClosureIntegers base target) :=
    (integralClosure_isDedekindDomain base target)
  exact
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain
      (integralClosureIntegers base target)).out (3-1) (2-1)).mp
      (show IsDedekindDomain (integralClosureIntegers base target) from inferInstance)

omit [base.valuation.HasExtension target.valuation] in
/-- If the actual integral closure is local, then it satisfies the valuative
dichotomy inside the extension field. -/
theorem integralClosure_mem_or_inv_of_isLocalRing
    [Algebra.IsSeparable K L]
    [IsLocalRing (integralClosureIntegers base target)] :
    ∀ z : L,
      z ∈ (integralClosure base.toDVF.valuationSubring L).toSubring ∨
        z⁻¹ ∈ (integralClosure base.toDVF.valuationSubring L).toSubring := by
  let : ValuationRing (integralClosureIntegers base target) :=
    (integralClosure_valuationRing_of_isLocalRing base target)
  exact (integralClosure_mem_or_inv_of_integralClosure_valuationRing base target)

end ValuedExtension

end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_FiniteExtension_Degree
attribute [-instance] _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

omit [FiniteDimensional K L] in
/-- The center of an extension valuation ring on the constructed actual
integral-closure valuation subring contracts to the base maximal ideal.

This is the nontrivial half of locating the center: the center is represented
as `ValuationSubring.idealOfLE`, and its contraction along the canonical map
from the base valuation ring is computed using the `HasExtension` valuation
inequality.  A later Henselian local-integral-closure theorem can combine this
with uniqueness of primes above the base maximal ideal to identify the center
with the maximal ideal of the constructed integral closure. -/
theorem idealOfLE_comap_integralClosureValuationSubringIntegerMap_eq_maximalIdeal
    {ΓL : Type x} [LinearOrderedCommGroupWithZero ΓL]
    (base : CompleteDVF.{u, v} K) (vL : _root_.Valuation L ΓL)
    [base.valuation.HasExtension vL]
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring) :
    let B :=
      integralClosureValuationSubringOfMemOrInv
        (L := L) base.valuation hval
    let hvL_le : B ≤ vL.valuationSubring :=
      integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
        (L := L) base.valuation vL hval
    (ValuationSubring.idealOfLE B vL.valuationSubring hvL_le).comap
        (integralClosureValuationSubringIntegerMapOfMemOrInv
          (K := K) (L := L) base hval) =
      base.maximalIdeal := by
  let B :=
    integralClosureValuationSubringOfMemOrInv
      (L := L) base.valuation hval
  let hvL_le : B ≤ vL.valuationSubring :=
    integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
      (L := L) base.valuation vL hval
  let i : base.valuationSubring →+* B :=
    integralClosureValuationSubringIntegerMapOfMemOrInv
      (K := K) (L := L) base hval
  apply Ideal.ext
  intro a
  rw [Ideal.mem_comap]
  change B.inclusion vL.valuationSubring hvL_le (i a) ∈
      IsLocalRing.maximalIdeal vL.valuationSubring ↔
    a ∈ IsLocalRing.maximalIdeal base.valuation.valuationSubring
  rw [Valuation.mem_maximalIdeal_iff (v := vL)]
  rw [Valuation.mem_maximalIdeal_iff (v := base.valuation)]
  change vL
      ((B.inclusion vL.valuationSubring hvL_le (i a) :
        vL.valuationSubring) : L) < 1 ↔
    base.valuation (a : K) < 1
  have hcoe :
      ((B.inclusion vL.valuationSubring hvL_le (i a) :
        vL.valuationSubring) : L) =
        algebraMap K L (a : K) := by
    rfl
  rw [hcoe]
  exact Valuation.HasExtension.val_map_lt_one_iff base.valuation vL (a : K)

end ValuedExtension
end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_FiniteExtension_Uniqueness
attribute [-instance] _root_.HilbertRamification.Dedekind.basePrime_isPrime _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply
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

/-- A complete-DVF uniqueness predicate for extensions of the base valuation. -/
def HasUniqueValuationExtension (base : CompleteDVF.{u, v} K)
    (target : CompleteDVF.{w, x} L) : Prop :=
  ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'],
      target.valuation.IsEquiv v'

omit [FiniteDimensional K L] in
/-- Center-prime form of the Henselian uniqueness frontier.

If the actual integral closure of the base valuation ring is a valuation ring,
and the center of every extension valuation ring on that integral-closure
valuation ring is the maximal ideal, then the extension valuation is unique.

This is the exact prime-theoretic step that remains after proving the
Henselian valuative dichotomy: the hypotheses are the center equalities
the Henselian finite-extension theorem must supply, not local-map or
certificate-style substitutes. -/
theorem hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_forall_center_eq_maximalIdeal

    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring)
    (htargetCenter :
      ValuationSubring.idealOfLE
        (ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
          (L := L) base.valuation hval)
        target.valuation.valuationSubring
        (ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
          (L := L) base.valuation target.valuation hval) =
        IsLocalRing.maximalIdeal
          (ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
            (L := L) base.valuation hval))
    (hcenter :
      ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
        (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'],
          ValuationSubring.idealOfLE
            (ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
              (L := L) base.valuation hval)
            v'.valuationSubring
            (ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
              (L := L) base.valuation v' hval) =
            IsLocalRing.maximalIdeal
              (ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
                (L := L) base.valuation hval)) :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  let B :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
      (L := L) base.valuation hval
  have htarget_le : B ≤ target.valuation.valuationSubring :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
      (L := L) base.valuation target.valuation hval
  have htarget_eq : target.valuation.valuationSubring = B :=
    ValuationTheory.DiscreteValuationField.Valuation.valuationSubring_eq_of_le_of_idealOfLE_eq_maximalIdeal
      B target.valuation.valuationSubring htarget_le
      (by simpa [B, htarget_le] using htargetCenter)
  intro Gamma' _ v' hExt
  let : base.valuation.HasExtension v' := hExt
  have hv_le : B ≤ v'.valuationSubring :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
      (L := L) base.valuation v' hval
  have hv_eq : v'.valuationSubring = B :=
    ValuationTheory.DiscreteValuationField.Valuation.valuationSubring_eq_of_le_of_idealOfLE_eq_maximalIdeal
      B v'.valuationSubring hv_le
      (by simpa [B, hv_le] using (@hcenter Gamma' inferInstance v' hExt))
  have hSubring : target.valuation.valuationSubring = v'.valuationSubring :=
    htarget_eq.trans hv_eq.symm
  exact valuation_isEquiv_of_valuationSubring_eq target v' hSubring

omit [FiniteDimensional K L] in
/-- Prime-uniqueness form of the Henselian uniqueness frontier.

After the actual integral closure has been turned into a valuation subring, it
is enough to prove that every prime of that valuation subring whose contraction
to the base valuation ring is the base maximal ideal is itself the maximal
ideal.  The center of each extension valuation ring has exactly that
contraction, so this theorem converts the Henselian local prime-uniqueness
statement into uniqueness of valuation extensions. -/
theorem hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_unique_primes_over_base_maximal

    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring)
    (hunique :
      let B :=
        ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
          (L := L) base.valuation hval
      let i : base.valuationSubring →+* B :=
        integralClosureValuationSubringIntegerMapOfMemOrInv
          (K := K) (L := L) base hval
      ∀ P : Ideal B, P.IsPrime → P.comap i = base.maximalIdeal →
        P = IsLocalRing.maximalIdeal B) :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  let B :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
      (L := L) base.valuation hval
  let i : base.valuationSubring →+* B :=
    integralClosureValuationSubringIntegerMapOfMemOrInv
      (K := K) (L := L) base hval
  refine
    (hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_forall_center_eq_maximalIdeal
      (K := K) (L := L) (base := base) (target := target)  hval ?_ ?_ :
        HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target))
  · let htarget_le : B ≤ target.valuation.valuationSubring :=
      ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
        (L := L) base.valuation target.valuation hval
    exact hunique
      (ValuationSubring.idealOfLE B target.valuation.valuationSubring htarget_le)
      (by infer_instance)
      (by
        simpa [B, htarget_le, i] using
          idealOfLE_comap_integralClosureValuationSubringIntegerMap_eq_maximalIdeal
            (K := K) (L := L) base target.valuation hval)
  · intro Gamma' _ v' hExt
    let : base.valuation.HasExtension v' := hExt
    let hv_le : B ≤ v'.valuationSubring :=
      ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
        (L := L) base.valuation v' hval
    exact hunique
      (ValuationSubring.idealOfLE B v'.valuationSubring hv_le)
      (by infer_instance)
      (by
        simpa [B, hv_le, i] using
          idealOfLE_comap_integralClosureValuationSubringIntegerMap_eq_maximalIdeal
            (K := K) (L := L) base v' hval)

/-- In a finite separable extension of complete DVFs, the actual integral
closure of the base valuation ring is itself a valuation ring. -/
theorem integralClosure_mem_or_inv_of_finite_separable
    (target : CompleteDVF.{w, x} L)
    [base.valuation.HasExtension target.valuation]
    [Algebra.IsSeparable K L] :
    ∀ z : L,
      z ∈ (integralClosure base.valuationSubring L).toSubring ∨
        z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring := by
  let : HenselianRing (integralClosureIntegers base target)
      (base.maximalIdeal.map
        (algebraMap base.valuationSubring (integralClosureIntegers base target))) :=
    (integralClosure_base_maximal_map_henselianRing base target)
  let : Subsingleton
      (PrimeSpectrum (base.maximalIdeal.Fiber (integralClosureIntegers base target))) :=
    (integralClosure_base_maximal_fiber_subsingleton_of_henselianRing_maximalIdeal_map base target)
  let : IsLocalRing (integralClosureIntegers base target) :=
    (integralClosure_isLocalRing_of_base_maximal_fiber_subsingleton base target)
  exact (integralClosure_mem_or_inv_of_isLocalRing base target)

omit [FiniteDimensional K L] [base.valuation.HasExtension target.valuation] in
/-- Under unique extension, any valuation subring whose canonical valuation
extends the base valuation is the chosen target valuation ring. -/
theorem target_valuationSubring_eq_of_hasUniqueValuationExtension
    (huniq : HasUniqueValuationExtension.{u, v, w, x, w}
      (base := base) (target := target))
    (B : ValuationSubring L) [base.valuation.HasExtension B.valuation] :
    target.valuation.valuationSubring = B := by
  have hEquiv : target.valuation.IsEquiv B.valuation :=
    huniq B.valuation
  have hSubring :
      target.valuation.valuationSubring = B.valuation.valuationSubring :=
    (_root_.Valuation.isEquiv_iff_valuationSubring
      target.valuation B.valuation).1 hEquiv
  simpa [ValuationSubring.valuationSubring_valuation] using hSubring

end ValuedExtension
end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_ValuedAdicComplete
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

universe u v

namespace ValuationTheory

/-!
# Adic completeness of complete rank-one discrete valued fields

This file supplies the common source used in the valuation-topology and adic-completeness arguments: on a
rank-one discrete valued field with archimedean ambient value group, the
native topology of the valuation ring is its maximal-ideal adic topology.
Consequently a complete valued field has an adically complete valuation ring.
-/

noncomputable section

namespace Valuations

open _root_.ValuationTheory.DiscreteValuationField

/-- A complete rank-one discrete valued field, equipped with its distinguished
valuation, gives a `CompleteDVF` by construction. -/
noncomputable def completeDVFOfCompleteValuedField
    {K : Type u} [Field K] {Gamma : Type v}
    [LinearOrderedCommGroupWithZero Gamma] [MulArchimedean Gamma]
    [Valued K Gamma]
    [(Valued.v : Valuation K Gamma).IsRankOneDiscrete]
    [CompleteSpace K] :
    CompleteDVF.{u, v} K where
  ValueGroup := Gamma
  valuation := Valued.v
  instCompleteDiscrete :=
    { isRankOneDiscrete := inferInstance
      isAdicComplete := rankOneDiscreteValuationSubring_isAdicComplete }

end Valuations
end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_FiniteExtensionCompleteDVF
attribute [-instance] _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Complete-DVF packages for local fields and their finite extensions

The canonical complete discrete valuation on a nonarchimedean local field,
and an integral-closure valuation chosen on each finite separable extension.
-/

noncomputable section

namespace LocalFieldTheory

open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension
open scoped ValuativeRel

universe u v y

/-! ## The canonical complete discrete valuation -/

/-- The canonical valuation of a nonarchimedean local field, packaged as a
complete discrete valuation field. -/
noncomputable def localCompleteDVF
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    CompleteDVF.{u, u} K := by
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  let v : Valuation K (ValuativeRel.ValueGroupWithZero K) := Valued.v
  let e :=
    (OrderMonoidIso.unitsCongr
      (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)).trans
      OrderMonoidIso.unitsWithZero
  letI : IsCyclic (ValuativeRel.ValueGroupWithZero K)ˣ :=
    e.toMulEquiv.isCyclic.mpr inferInstance
  letI : v.IsNontrivial :=
    (ValuativeRel.isNontrivial_iff_isNontrivial v).mp inferInstance
  letI : IsCyclic (MonoidWithZeroHom.valueGroup v.toMonoidWithZeroHom) :=
    Subgroup.isCyclic_of_le
      (show MonoidWithZeroHom.valueGroup v.toMonoidWithZeroHom ≤ ⊤ from le_top)
  letI : v.IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' v
  exact ValuationTheory.Valuations.completeDVFOfCompleteValuedField

/-- The canonical complete-DVF packages preserve an existing extension of
the underlying valuative relations. -/
theorem localCompleteDVFValuation_hasExtension
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)] :
    (localCompleteDVF K).valuation.HasExtension
      (localCompleteDVF L).valuation := by
  apply Valuation.HasExtension.ofComapInteger
  ext x
  change
    ValuativeRel.valuation L (algebraMap K L x) ≤ 1 ↔
      ValuativeRel.valuation K x ≤ 1
  exact
    Valuation.HasExtension.val_map_le_one_iff
      (ValuativeRel.valuation K) (ValuativeRel.valuation L) x

/-! ## Chosen ramification data for an arbitrary finite local extension -/

end LocalFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_SeparableNormValuation
attribute [-instance] _root_.HilbertRamification.Dedekind.basePrime_isPrime _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option synthInstance.maxHeartbeats 400000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory

open LocalFieldTheory

/-!
# Finite local reciprocity: normalized valuation of field norms

This file supplies the local-field calculation used when the abstract
class-formation framework is specialized to separable-closure units.  All
ramification and residue degrees below are the actual invariants of the
valuation-ring extension; no packaged norm-valuation hypothesis is assumed.
-/

noncomputable section

universe u v w

open scoped BigOperators ValuativeRel
open IsNonarchimedeanLocalField

section SeparableIdealNorm

variable (R : Type u) (S : Type v)
  [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
  [IsIntegrallyClosed R] [IsIntegrallyClosed S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]

attribute [local instance] FractionRing.liftAlgebra

omit [IsIntegrallyClosed R] in
/-- Finiteness of the integral normal closure follows from separability of
the original fraction-field extension. -/
theorem ringNormalClosure_moduleFinite_of_isSeparable
    [IsNoetherianRing S]
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)] :
    Module.Finite S (Ring.NormalClosure R S) := by
  let K := FractionRing R
  let L := FractionRing S
  let A := AlgebraicClosure L
  let E := IntermediateField.normalClosure K L A
  let : Algebra L E := normalClosure.algebra K L A
  let T := Ring.NormalClosure R S
  let : Algebra S E := ((algebraMap L E).comp (algebraMap S L)).toAlgebra
  let : IsScalarTower S L E := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  let : Algebra T E := by
    change Algebra (integralClosure S E) E
    infer_instance
  let : IsScalarTower S T E :=
    IsScalarTower.subalgebra' S E E (integralClosure S E)
  let : IsIntegralClosure T S E := integralClosure.isIntegralClosure S E
  let : FiniteDimensional L E :=
    intermediateNormalClosure_finiteDimensional_top K L A
  let : Algebra.IsSeparable K E :=
    intermediateNormalClosure_isSeparable_of_isSeparable K L A
  let : Algebra.IsSeparable L E :=
    Algebra.isSeparable_tower_top_of_isSeparable K L E
  change Module.Finite S (integralClosure S E)
  exact IsIntegralClosure.finite S L E (integralClosure S E)

end SeparableIdealNorm

section SeparableIdealNormRelNorm

variable (R : Type u) (S : Type v)
  [CommRing R] [IsDedekindDomain R]
  [CommRing S] [IsDedekindDomain S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]

attribute [local instance] FractionRing.liftAlgebra

/-- Relative ideal norm of a maximal ideal in a finite separable extension.
This is the separable replacement for mathlib's perfect-base theorem and is
proved by the same normal-closure descent. -/
theorem relNorm_eq_pow_inertiaDeg_of_isSeparable
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
    (P : Ideal S) (p : Ideal R) [P.LiesOver p]
    [P.IsMaximal] [p.IsMaximal] :
    Ideal.relNorm R P = p ^ P.inertiaDeg R := by
  let T := Ring.NormalClosure R S
  let : Module.Finite S T :=
    ringNormalClosure_moduleFinite_of_isSeparable R S
  let : Module.Finite R T := Module.Finite.trans S T
  let : IsDedekindDomain T :=
    ringNormalClosure_isDedekindDomain_of_isSeparable R S
  let : IsScalarTower R (FractionRing S) (FractionRing T) :=
    IsScalarTower.to₁₃₄ R S (FractionRing S) (FractionRing T)
  let : IsScalarTower (FractionRing R) (FractionRing S) (FractionRing T) :=
    IsScalarTower.of_algebraMap_eq' (by
      apply IsFractionRing.ringHom_ext (A := R)
      intro x
      rw [← IsScalarTower.algebraMap_apply R (FractionRing R) (FractionRing T)]
      change algebraMap R (FractionRing T) x =
        algebraMap (FractionRing S) (FractionRing T)
          (algebraMap (FractionRing R) (FractionRing S)
            (algebraMap R (FractionRing R) x))
      rw [← IsScalarTower.algebraMap_apply R (FractionRing R) (FractionRing S),
        ← IsScalarTower.algebraMap_apply R (FractionRing S) (FractionRing T)])
  let : IsGalois (FractionRing R) (FractionRing T) :=
    ringNormalClosure_isGalois_of_isSeparable R S
  let : IsGalois (FractionRing S) (FractionRing T) :=
    IsGalois.tower_top_of_isGalois
      (FractionRing R) (FractionRing S) (FractionRing T)
  obtain ⟨Q, hQm, hQP⟩ : ∃ Q : Ideal T, Q.IsMaximal ∧ Q.LiesOver P :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral P
  let : Q.IsMaximal := hQm
  let : Q.LiesOver P := hQP
  let : Q.LiesOver p := Ideal.LiesOver.trans Q P p
  have h := Ideal.relNorm_eq_pow_of_isPrime_isGalois Q p
  rwa [← Ideal.relNorm_relNorm R S,
    Ideal.relNorm_eq_pow_of_isPrime_isGalois Q P, map_pow,
    Ideal.inertiaDeg_tower (R := R) P Q, pow_mul, pow_left_inj] at h
  exact Nat.ne_zero_iff_zero_lt.mpr (Ideal.inertiaDeg_pos Q S)

end SeparableIdealNormRelNorm

attribute [local instance] FractionRing.liftAlgebra

/-- In a finite separable local-field extension, the relative ideal norm of
the upstairs maximal ideal is the residue-degree power of the base maximal
ideal. -/
theorem relNorm_maximalIdeal_eq_pow_residue_finrank
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]] :
    Ideal.relNorm 𝒪[K] (𝓂[L] : Ideal 𝒪[L]) =
      (𝓂[K] : Ideal 𝒪[K]) ^ Module.finrank 𝓀[K] 𝓀[L] := by
  let : Algebra.IsSeparable (FractionRing 𝒪[K]) (FractionRing 𝒪[L]) :=
    fractionRing_integerRing_isSeparable K L
  have h := relNorm_eq_pow_inertiaDeg_of_isSeparable
    𝒪[K] 𝒪[L] (𝓂[L] : Ideal 𝒪[L]) (𝓂[K] : Ideal 𝒪[K])
  rw [Ideal.inertiaDeg_eq_of_isMaximal
    (𝓂[K] : Ideal 𝒪[K]) (𝓂[L] : Ideal 𝒪[L])] at h
  exact h

end
end LocalClassFieldTheory
end


