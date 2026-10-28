-- Prove2me | Definitions.Def_OAIQ068A005
-- name    : OAIQ068A005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T07:39:30.293441+00:00
-- url     : https://prove2.me/theorems/b2646645-6465-4e01-ae15-06841836c7dc
-- title:
--   Definitions bundle OAIQ068A005 of the split of OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 96 declarations of OpenAI's Lean: 30 definitions, 1 inductive type or structure and 65 theorems. The definitions and types are `OAI.PiExponent.Arithmetic.lcmConstant`, `OAI.PiExponent.CoherentExtFiniteness.FiniteCohomologyPresentation`, `OAI.PiExponent.CoherentExtFiniteness.extLinearEquivBiproduct`, `OAI.PiExponent.CurveGlobalMonomialLocal.monomialCoordinates`, `OAI.PiExponent.CurveNormalizationModel.affineChartFunctionFieldMap`, `OAI.PiExponent.CurveNormalizationModel.affineFunctionFieldEquiv`, `OAI.PiExponent.CurveNormalizationModel.functionFieldRestriction`, `OAI.PiExponent.ExceptionalCurveDegree.localIdeal`, `OAI.PiExponent.GeometrySupport.FreeCechResolution.coverVertices`, `OAI.PiExponent.GeometrySupport.FreeCechResolution.freePresheafComplex`, `OAI.PiExponent.GeometrySupport.FreeCechResolution.freeSheafComplex`, `OAI.PiExponent.GeometrySupport.FreeCechResolution.freeTupleComplex`, `OAI.PiExponent.GeometrySupport.FreeCechResolution.tupleAugmented`, `OAI.PiExponent.GeometrySupport.FreeCechResolution.tupleExtraDegeneracy`, `OAI.PiExponent.GeometrySupport.FreeCechResolution.tuplePresheaf`, `OAI.PiExponent.GeometrySupport.FreeCechResolution.tupleSimplex`, `OAI.PiExponent.GeometrySupport.FreeCechSections.boundary`, `OAI.PiExponent.GeometrySupport.FreeCechSections.freeFace`, `OAI.PiExponent.GeometrySupport.FreeCechSections.freeTerm`, `OAI.PiExponent.GeometrySupport.FreeCechSections.termShortComplex`, `OAI.PiExponent.GeometrySupport.ProjectiveTupleCharts.tupleVariables`, `OAI.PiExponent.GradedCech.coverProduct`, `OAI.PiExponent.WeightedLocalLattice.generatedLattice`, `OAI.PiExponent.WeightedLocalSheaf.generatedSectionMap`, `OAI.PiExponent.WeightedLocalSheaf.generatedSheaf`, `OAI.PiExponent.WeightedSectionOrder.coordinateBasis`, `OAI.PiExponentSeshadri.FiniteSupport.pointOpen`, `OAI.PiExponentSeshadri.Geometry.structuralStalkAlgebra`, `OAI.PiExponentSeshadri.Projective.relabeledOverlapEquiv`, `OAI.PiExponentSeshadri.Projective.relabeledSectionIso`, `OAI.PiExponentSeshadri.Projective.schemeIsoGammaEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `PiExponent_Ampleness_AffineFunctionFieldCompatibility`, `PiExponent_Ampleness_ExceptionalCurveDegree`, `PiExponent_Approximation_Arithmetic`, `PiExponent_Approximation_ClosedPushforwardCoherent`, `PiExponent_Approximation_GlobalSectionClearing`, `PiExponent_Approximation_InverseFrameRestriction`, `PiExponent_Approximation_TwistSectionClearing`, `PiExponent_Approximation_WeightedSectionOrder`, `PiExponent_Cohomology_FiniteLineEuler`, `PiExponent_Cohomology_FiniteSupportCohomology`, `PiExponent_Cohomology_FreeCechResolution`, `PiExponent_Cohomology_FreeCechSections`, `PiExponent_Cohomology_GradedCech`, `PiExponent_Geometry_BirationalValuationStalk`, `PiExponent_Geometry_CartierSequence`, `PiExponent_Geometry_CurveChartFunctionField`, `PiExponent_Geometry_CurveFunctionFieldCompatibility`, `PiExponent_Geometry_CurveGlobalMonomialLocal`, `PiExponent_Geometry_CurveLocalOrder`, `PiExponent_Geometry_CurveModelGenericPoint`, `PiExponent_Geometry_CurveModelLocalOrder`, `PiExponent_Geometry_CurvePlaceCenter`, `PiExponent_Geometry_FiniteCurveZeros`, `PiExponent_Geometry_ProjectiveChartRingNaturality`, `PiExponent_Geometry_ProjectiveChartRingNaturalityCore`, `PiExponent_Geometry_ProjectiveCoordinateRingNaturality`, `PiExponent_Geometry_ProjectiveCoordinateSections`, `PiExponent_Geometry_ProjectiveEmbeddingCharts`, `PiExponent_Geometry_ProjectiveTupleCharts`, `PiExponent_Geometry_WeightedLocalSheaf`, `PiExponent_Jets_IntrinsicLength`, `PiExponent_LocalAlgebra_CoherentExtFiniteness`, `PiExponent_LocalAlgebra_LocalPullbackSectionOrder`, `PiExponent_LocalAlgebra_WeightedLocalLattice`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ068A015`, `OAIQ068A016` and `OAIQ068A017`; the statement `OAI_PiExponent_NumericalAmpleness_isAmple_of_lower_ampleness_of_euler_growth`.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 1581d4c

import Mathlib
import Lean.Elab.Tactic.Omega

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_IntrinsicLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W24

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

theorem augmentation_surjective (ε : A →+* K)
    (hε : ∀ k : K, ε (algebraMap K A k) = k) : Function.Surjective ε :=
  fun k => ⟨algebraMap K A k, hε k⟩

variable [IsLocalRing A]

theorem simple_annihilator_eq_augmentation_kernel (ε : A →+* K)
    (hε : ∀ k : K, ε (algebraMap K A k) = k)
    {M : Type*} [AddCommGroup M] [Module A M] [IsSimpleModule A M] :
    Module.annihilator A M = RingHom.ker ε := by
  have hker : (RingHom.ker ε).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective ε (augmentation_surjective ε hε)
  exact (IsLocalRing.eq_maximalIdeal (IsSimpleModule.annihilator_isMaximal (R := A)
    (M := M))).trans (IsLocalRing.eq_maximalIdeal hker).symm

theorem simple_smul_eq_augmentation_smul (ε : A →+* K)
    (hε : ∀ k : K, ε (algebraMap K A k) = k)
    {M : Type*} [AddCommGroup M] [Module A M] [Module K M]
    [IsScalarTower K A M] [IsSimpleModule A M] (a : A) (x : M) :
    a • x = ε a • x := by
  have ha : a - algebraMap K A (ε a) ∈ Module.annihilator A M := by
    rw [simple_annihilator_eq_augmentation_kernel ε hε]
    rw [RingHom.mem_ker, map_sub, hε, sub_self]
  have hx := Module.mem_annihilator.mp ha x
  exact sub_eq_zero.mp (by simpa only [sub_smul, algebraMap_smul] using hx)

theorem simple_over_coefficient_field (ε : A →+* K)
    (hε : ∀ k : K, ε (algebraMap K A k) = k)
    {M : Type*} [AddCommGroup M] [Module A M] [Module K M]
    [IsScalarTower K A M] [IsSimpleModule A M] : IsSimpleModule K M := by
  apply isSimpleModule_iff_toSpanSingleton_surjective.mpr
  refine ⟨IsSimpleModule.nontrivial A M, ?_⟩
  intro x hx y
  obtain ⟨a, ha⟩ := IsSimpleModule.toSpanSingleton_surjective A hx y
  refine ⟨ε a, ?_⟩
  change ε a • x = y
  rw [← simple_smul_eq_augmentation_smul ε hε a x]
  exact ha

end PiExponentJets.W24

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveLocalOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators nonZeroDivisors
open IsLocalRing IsDiscreteValuationRing

namespace PiExponent.CurveLocalOrder

theorem length_quotient_span_eq_addVal
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {a : A} (ha : a ≠ 0) :
    Module.length A (A ⧸ Ideal.span {a}) = IsDiscreteValuationRing.addVal A a := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  rw [IsDiscreteValuationRing.addVal_def' u hϖ]
  rw [Ideal.span_singleton_mul_left_unit u.isUnit,
    ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq]
  exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal A n

theorem principal_colength_ne_top
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {a : A} (ha : a ≠ 0) : Module.length A (A ⧸ Ideal.span {a}) ≠ ⊤ := by
  rw [length_quotient_span_eq_addVal ha]
  exact IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr ha

end PiExponent.CurveLocalOrder

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveFunctionFieldCompatibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationModel
open CategoryTheory AlgebraicGeometry
universe u

def functionFieldRestriction {U X : Scheme.{u}} [IsIntegral U] [IsIntegral X]
    (i : U ⟶ X) [IsOpenImmersion i] : X.functionField ⟶ U.functionField :=
  eqToHom (congrArg (fun x => X.presheaf.stalk x)
    (genericPoint_eq_of_isOpenImmersion i).symm) ≫ i.stalkMap (genericPoint U)

theorem stalkMap_eqToHom {U X : Scheme.{u}} (i : U ⟶ X)
    (x y : U) (h : x = y) :
    i.stalkMap x ≫ eqToHom (congrArg (fun z => U.presheaf.stalk z) h) =
      eqToHom (congrArg (fun z => X.presheaf.stalk (i z)) h) ≫ i.stalkMap y := by
  subst y
  simp

theorem functionFieldRestriction_comp {V U X : Scheme.{u}}
    [IsIntegral V] [IsIntegral U] [IsIntegral X]
    (j : V ⟶ U) (i : U ⟶ X) [IsOpenImmersion j] [IsOpenImmersion i] :
    functionFieldRestriction (j ≫ i) = functionFieldRestriction i ≫ functionFieldRestriction j := by
  symm
  unfold functionFieldRestriction
  rw [Scheme.Hom.stalkMap_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (i.stalkMap (genericPoint U)),
    stalkMap_eqToHom i (genericPoint U) (j (genericPoint V))
      (genericPoint_eq_of_isOpenImmersion j).symm]
  simp

theorem toStalk_eqToHom (A : CommRingCat.{u})
    (x y : PrimeSpectrum A) (h : x = y) :
    StructureSheaf.toStalk A x ≫ eqToHom (congrArg
      (fun z => (Spec A).presheaf.stalk z) h) = StructureSheaf.toStalk A y := by
  subst y
  exact Category.comp_id _


theorem functionFieldRestriction_toStalk {A B : CommRingCat.{u}} [IsDomain A] [IsDomain B]
    (f : A ⟶ B) [IsOpenImmersion (Spec.map f)] :
    StructureSheaf.toStalk A (genericPoint (Spec A)) ≫
      functionFieldRestriction (Spec.map f) =
      f ≫ StructureSheaf.toStalk B (genericPoint (Spec B)) := by
  unfold functionFieldRestriction
  erw [← Category.assoc, toStalk_eqToHom A _ _
    (genericPoint_eq_of_isOpenImmersion (Spec.map f)).symm]
  exact AlgebraicGeometry.stalkMap_toStalk f _

end PiExponent.CurveNormalizationModel

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_AffineFunctionFieldCompatibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationModel
open CategoryTheory AlgebraicGeometry
universe u
variable (A E : Type u) [CommRing A] [IsDomain A] [Field E]
  [Algebra A E] [IsFractionRing A E]

theorem isFractionRing_of_intermediate_domain
    (B : Type u) [CommRing B] [IsDomain B] [Algebra A B]
    [Algebra B E] [IsScalarTower A B E]
    (hB : Function.Injective (algebraMap B E)) : IsFractionRing B E where
  map_units b := isUnit_iff_ne_zero.mpr (by
    intro h
    exact (mem_nonZeroDivisors_iff_ne_zero.mp b.2) (hB (by simpa using h)))
  surj z := by
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors A) z
    have hn : algebraMap A B s ≠ 0 := by
      intro he
      have he' : algebraMap A E s = 0 := by
        rw [IsScalarTower.algebraMap_apply A B E, he, map_zero]
      exact (mem_nonZeroDivisors_iff_ne_zero.mp s.2)
        ((IsFractionRing.injective A E) (by simp at he'))
    refine ⟨⟨algebraMap A B a, ⟨algebraMap A B s, mem_nonZeroDivisors_iff_ne_zero.mpr hn⟩⟩, ?_⟩
    simpa only [← IsScalarTower.algebraMap_apply A B E] using hs
  exists_of_eq {a b} h := ⟨1, by simpa using hB h⟩

def affineFunctionFieldEquiv : (Spec (.of A)).functionField ≃+* E := by
  letI : Algebra A (Spec (.of A)).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of A)
  letI : IsFractionRing A (Spec (.of A)).functionField :=
    functionField_isFractionRing_of_affine (.of A)
  exact (IsLocalization.algEquiv (nonZeroDivisors A) (Spec (.of A)).functionField E).toRingEquiv

@[simp] theorem affineFunctionFieldEquiv_toStalk (a : A) :
    affineFunctionFieldEquiv A E (StructureSheaf.toStalk A
      (genericPoint (Spec (.of A))) a) = algebraMap A E a := by
  let : Algebra A (Spec (.of A)).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of A)
  let : IsFractionRing A (Spec (.of A)).functionField :=
    functionField_isFractionRing_of_affine (.of A)
  exact (IsLocalization.algEquiv (nonZeroDivisors A)
    (Spec (.of A)).functionField E).commutes a

theorem affineFunctionFieldEquiv_naturality
    (B : Type u) [CommRing B] [IsDomain B] [Algebra A B]
    [Algebra B E] [IsFractionRing B E] [IsScalarTower A B E]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A B)))] :
    (affineFunctionFieldEquiv B E).toRingHom.comp
      (functionFieldRestriction (Spec.map (CommRingCat.ofHom (algebraMap A B)))).hom =
      (affineFunctionFieldEquiv A E).toRingHom := by
  let : Algebra A (Spec (.of A)).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of A)
  let : IsFractionRing A (Spec (.of A)).functionField :=
    functionField_isFractionRing_of_affine (.of A)
  apply IsLocalization.ringHom_ext (nonZeroDivisors A)
  apply RingHom.ext
  intro a
  change affineFunctionFieldEquiv B E
    (functionFieldRestriction (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (StructureSheaf.toStalk A (genericPoint (Spec (.of A))) a)) =
    affineFunctionFieldEquiv A E
      (StructureSheaf.toStalk A (genericPoint (Spec (.of A))) a)
  have h := congrArg (fun h => h a)
    (functionFieldRestriction_toStalk (CommRingCat.ofHom (algebraMap A B)))
  change functionFieldRestriction (Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (StructureSheaf.toStalk A (genericPoint (Spec (.of A))) a) =
    StructureSheaf.toStalk B (genericPoint (Spec (.of B))) (algebraMap A B a) at h
  rw [h, affineFunctionFieldEquiv_toStalk, affineFunctionFieldEquiv_toStalk]
  exact (IsScalarTower.algebraMap_apply A B E a).symm

end PiExponent.CurveNormalizationModel

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveEmbeddingCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri

universe u

namespace Geometry
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y : Scheme.{u}} {ι : Type u}

theorem closedImmersion_of_source_charts (f : X ⟶ Y) [UniversallyClosed f]
    (U : ι → X.Opens) (V : ι → Y.Opens)
    (hU : (⨆ i, U i) = ⊤) (g : ∀ i, (U i).toScheme ⟶ (V i).toScheme)
    (hg : ∀ i, IsClosedImmersion (g i))
    (hcomm : ∀ i, (U i).ι ≫ f = g i ≫ (V i).ι)
    (hpre : ∀ i, f ⁻¹ᵁ V i = U i) : IsClosedImmersion f := by
  have hinj : Function.Injective f := by
    intro x y hxy
    have hx : x ∈ ⨆ i, U i := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    have hy : y ∈ U i := by
      rw [← hpre i]
      change f y ∈ V i
      rw [← hxy]
      change x ∈ f ⁻¹ᵁ V i
      rw [hpre]
      exact hi
    have he (z : (U i).toScheme) : (g i z).val = f z.val :=
      (congrArg (fun a : (U i).toScheme ⟶ Y => a z) (hcomm i)).symm
    have hz : g i ⟨x, hi⟩ = g i ⟨y, hy⟩ := by
      apply Subtype.ext
      exact (he ⟨x, hi⟩).trans (hxy.trans (he ⟨y, hy⟩).symm)
    have := (g i).isClosedEmbedding.injective hz
    exact congrArg Subtype.val this
  have hstalk : SurjectiveOnStalks f := by
    apply IsZariskiLocalAtSource.of_openCover (P := @SurjectiveOnStalks)
      (X.openCoverOfIsOpenCover U hU)
    intro i
    change ι at i
    change SurjectiveOnStalks ((U i).ι ≫ f)
    rw [hcomm]
    have := hg i
    infer_instance
  exact ⟨Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap f.continuous hinj f.isClosedMap⟩

end Geometry

namespace Projective

open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
variable {K σ : Type u} [CommRing K] {X : Scheme.{u}}
attribute [local instance] MvPolynomial.gradedAlgebra

lemma toSpec_scalarMap (p : X ⟶ Spec (CommRingCat.of K)) :
    X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)) = p := by
  change X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ p.appTop) = p
  rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
  simp

end Projective

namespace Geometry
open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped AlgebraicGeometry

lemma finiteType_coordinates {K R : Type u} [CommRing K] [CommRing R]
    (k : K →+* R) (hk : k.FiniteType) :
    ∃ n : ℕ, ∃ a : Fin n → R, Function.Surjective (eval₂Hom k a) := by
  let := k.toAlgebra
  have : Algebra.FiniteType K R := hk
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType K R)
  refine ⟨n, fun i => f (X i), ?_⟩
  have heq : eval₂Hom k (fun i => f (X i)) = f.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      exact (eval₂Hom_C _ _ _).trans (f.commutes c).symm
    · intro i
      exact eval₂Hom_X' _ _ _
  rw [heq]
  exact hf

theorem affine_coordinate_generators {K : Type u} [CommRing K] {X : Scheme.{u}}
    [IsAffine X] (p : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType p] :
    ∃ n : ℕ, ∃ a : Fin n → Γ(X, ⊤), Function.Surjective
      (eval₂Hom (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) a) := by
  have hp : p.appTop.hom.FiniteType :=
    HasRingHomProperty.appTop (P := @LocallyOfFiniteType) _ inferInstance
  have he : (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv).surjective
  exact finiteType_coordinates _ (hp.comp he)

end Geometry

end PiExponentSeshadri

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveChartRingNaturalityCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
attribute [local instance] Classical.propDecidable
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] AlgebraicGeometry.StructureSheaf.openAlgebra
variable {R σ : Type*} [CommRing R] (i : σ)

lemma chartIso_pullback_top {X : Scheme} (U : X.Opens) (A : CommRingCat)
    (e : U.toScheme ≅ Spec A) (g : A ⟶ Γ(X,U))
    (he : e.hom.appTop = (Scheme.ΓSpecIso A).hom ≫ g ≫ U.topIso.inv) :
    g ≫ U.topIso.inv ≫ e.inv.appTop = (Scheme.ΓSpecIso A).inv := by
  apply (cancel_epi (Scheme.ΓSpecIso A).hom).mp
  rw [Iso.hom_inv_id]
  calc
    _ = e.hom.appTop ≫ e.inv.appTop := by rw [he]; simp only [Category.assoc]
    _ = 𝟙 _ := by rw [← Scheme.Hom.comp_appTop, e.inv_hom_id, Scheme.Hom.id_appTop]

def relabeledSectionIso {Y Z : Scheme} (f : Y ⟶ Z) [IsOpenImmersion f]
    (V U : Z.Opens) (W : Y.Opens) (hU : f.opensRange = U) (hW : f ⁻¹ᵁ V = W) :
    Γ(Y,W) ≅ Γ(Z,U ⊓ V) := by
  have e := IsOpenImmersion.ΓIso f V
  rw [hU, hW] at e
  exact e

lemma relabeledSectionIso_inv {Y Z : Scheme} (f : Y ⟶ Z) [IsOpenImmersion f]
    (V U : Z.Opens) (W : Y.Opens) (hU : f.opensRange = U) (hW : f ⁻¹ᵁ V = W) :
    (relabeledSectionIso f V U W hU hW).inv = f.appLE (U ⊓ V) W (by
      rw [← hU, ← hW, ← f.image_preimage_eq_opensRange_inf, f.preimage_image_eq]) := by
  subst U
  subst W
  exact IsOpenImmersion.ΓIso_inv f V

end
end PiExponentSeshadri.Projective

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveChartRingNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
attribute [local instance] Classical.propDecidable
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] AlgebraicGeometry.StructureSheaf.openAlgebra
variable {R σ : Type*} [CommRing R] (i : σ)

def relabeledOverlapEquiv {X : Scheme} {A : Type*} [CommRing A]
    (U V V' : X.Opens) (z z' : A)
    (e : Γ(X,U ⊓ V) ≃+* Localization.Away z) (hz : z = z') (hV : V = V') :
    Γ(X,U ⊓ V') ≃+* Localization.Away z' := by
  rw [hz, hV] at e
  exact e

lemma relabeledOverlapEquiv_restrict {X : Scheme} {A : Type*} [CommRing A]
    (U V V' : X.Opens) (z z' : A)
    (e : Γ(X,U ⊓ V) ≃+* Localization.Away z) (hz : z = z') (hV : V = V')
    (a : Γ(X,U)) (p : A)
    (h : e (X.presheaf.map (homOfLE inf_le_left).op a) = algebraMap _ _ p) :
    relabeledOverlapEquiv U V V' z z' e hz hV
      (X.presheaf.map (homOfLE inf_le_left).op a) = algebraMap _ _ p := by
  subst z'
  subst V'
  exact h

end
end PiExponentSeshadri.Projective

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveCoordinateSections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open PiExponentSeshadri.Geometry
attribute [local instance] MvPolynomial.gradedAlgebra

def schemeIsoGammaEquiv {Y : Scheme} {A : CommRingCat} (g : Y ≅ Spec A) :
    Γ(Y,⊤) ≃+* A :=
  (Scheme.Γ.mapIso g.symm.op ≪≫ Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv

@[simp] lemma schemeIsoGammaEquiv_symm_apply {Y : Scheme} {A : CommRingCat}
    (g : Y ≅ Spec A) (a : A) :
    (schemeIsoGammaEquiv g).symm a = ((Scheme.ΓSpecIso A).inv ≫ g.hom.appTop).hom a := rfl

end
end PiExponentSeshadri.Projective

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveCoordinateRingNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri
namespace Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

lemma appLE_restrict_comm {X Y : Scheme} (f : X ⟶ Y)
    {U V : Y.Opens} {U' V' : X.Opens} (h : V ≤ U) (h' : V' ≤ U')
    (eU : U' ≤ f ⁻¹ᵁ U) (eV : V' ≤ f ⁻¹ᵁ V) (x : Γ(Y,U)) :
    X.presheaf.map (homOfLE h').op (f.appLE U U' eU x) =
      f.appLE V V' eV (Y.presheaf.map (homOfLE h).op x) := by
  change (f.appLE U U' eU ≫ X.presheaf.map (homOfLE h').op) x =
    (Y.presheaf.map (homOfLE h).op ≫ f.appLE V V' eV) x
  simp only [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

attribute [local instance] MvPolynomial.gradedAlgebra

end

end Projective
end PiExponentSeshadri

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_Arithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.Arithmetic

noncomputable def lcmConstant : ℝ := Real.log 4 + 4

end PiExponent.Arithmetic

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_WeightedLocalLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators nonZeroDivisors
open PiExponent.CurveLocalOrder

namespace PiExponent.WeightedLocalLattice

def generatedLattice
    (A : Type*) {K ι : Type*} [CommRing A] [Field K] [Algebra A K]
    (y : ι → K) (s : Finset ι) : Submodule A K :=
  Submodule.span A {z | ∃ i ∈ s, z = y i}

end PiExponent.WeightedLocalLattice

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_GlobalSectionClearing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GlobalSectionClearing
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {X Y : Scheme.{u}}

lemma principal_open_image (r : Γ(X,⊤)) (U : X.Opens) :
    U.ι ''ᵁ U.toScheme.basicOpen (U.ι.appTop r) = U ⊓ X.basicOpen r := by
  rw [← Scheme.preimage_basicOpen_top, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι]

end
end PiExponent.GlobalSectionClearing

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ClosedPushforwardCoherent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.ClosedPushforward

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
variable {X Y : Scheme.{0}}

theorem presentation_transport {Z : Scheme.{0}}
    {M N : SheafOfModules Z.ringCatSheaf} (e : M ≅ N)
    (P : M.Presentation) (hP : P.IsFinite) : ∃ Q : N.Presentation, Q.IsFinite := by
  let : IsIso e.hom := e.isIso_hom
  exact ⟨P.ofIsIso e.hom,
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩

end PiExponentSeshadri.ClosedPushforward

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_TwistSectionClearing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.TwistSectionClearing
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry
open PiExponent.GlobalSectionClearing
variable {X : Scheme}

lemma iso_section_restrict_zero_on {P Q : X.Modules} (e : P ≅ Q)
    {V W : X.Opens} (hVW : V ≤ W) (x : Γ(P,W))
    (hx : P.presheaf.map (homOfLE hVW).op x = 0) :
    Q.presheaf.map (homOfLE hVW).op (e.hom.app W x) = 0 := by
  have h := CategoryTheory.congr_fun (e.hom.mapPresheaf.naturality (homOfLE hVW).op) x
  change e.hom.app V (P.presheaf.map (homOfLE hVW).op x) =
    Q.presheaf.map (homOfLE hVW).op (e.hom.app W x) at h
  rw [hx, map_zero] at h
  exact h.symm

lemma hom_section_restriction {P Q : X.Modules} (f : P ⟶ Q)
    {V W : X.Opens} (hVW : V ≤ W) (x : Γ(P,W)) :
    Q.presheaf.map (homOfLE hVW).op (f.app W x) =
      f.app V (P.presheaf.map (homOfLE hVW).op x) := by
  have h := CategoryTheory.congr_fun (f.mapPresheaf.naturality (homOfLE hVW).op) x
  exact h.symm

end
end PiExponent.TwistSectionClearing

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_FreeCechResolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.FreeCechResolution

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology TopologicalSpace

universe u

def tupleSimplex (V : Type u) : SimplicialObject (Type u) where
  obj n := ToType n.unop → V
  map f := ↾fun t => t ∘ f.unop.toOrderHom
  map_id _ := rfl
  map_comp _ _ := rfl

def tupleAugmented (V : Type u) : SimplicialObject.Augmented (Type u) :=
  (tupleSimplex V).augmentOfIsTerminal Types.isTerminalPUnit

def tupleExtraDegeneracy {V : Type u} (p : V) :
    (tupleAugmented V).ExtraDegeneracy where
  s' := ↾fun _ _ => p
  s n := ↾fun t => Fin.cons p t
  s'_comp_ε := rfl
  s₀_comp_δ₁ := by
    ext t
    funext i
    fin_cases i
    rfl
  s_comp_δ₀ n := by
    ext t
    funext i
    rfl
  s_comp_δ n i := by
    ext t
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · change (Fin.cons p t : Fin (n + 3) → V) (i.succ.succAbove j.succ) = t (i.succAbove j)
      simp only [Fin.succ_succAbove_succ]
      rfl
  s_comp_σ n i := by
    ext t
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · change (Fin.cons p t : Fin (n + 2) → V) (i.succ.predAbove j.succ) = t (i.predAbove j)
      simp only [Fin.succ_predAbove_succ]
      rfl

def freeTupleComplex (R : RingCat.{u}) (V : Type u) : ChainComplex (ModuleCat R) ℕ :=
  AlternatingFaceMapComplex.obj (tupleSimplex V ⋙ ModuleCat.free R)

theorem freeTupleComplex_exact (R : RingCat.{u}) (V : Type u) (q : ℕ) :
    (freeTupleComplex R V).ExactAt (q + 1) := by
  classical
  cases isEmpty_or_nonempty V with
  | inl h =>
    let : IsEmpty (Fin (q + 2) → V) := ⟨fun t => isEmptyElim (t 0)⟩
    change ((freeTupleComplex R V).sc (q + 1)).Exact
    apply ShortComplex.exact_of_isZero_X₂
    have hz : Subsingleton (((Fin (q + 2) → V) →₀ R)) := inferInstance
    exact ModuleCat.isZero_of_subsingleton (ModuleCat.of R ((Fin (q + 2) → V) →₀ R))
  | inr h =>
    let p : V := Classical.choice h
    let e := ((tupleExtraDegeneracy p).map (ModuleCat.free R)).homotopyEquiv
    apply (exactAt_iff_of_quasiIsoAt e.hom (q + 1)).2
    exact HomologicalComplex.exactAt_single_obj (ComplexShape.down ℕ) 0 _
      (q + 1) (by omega)

def coverVertices {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X) :
    (Opens X)ᵒᵖ ⥤ Type u where
  obj W := {i : ι // W.unop ≤ U i}
  map f := ↾fun i => ⟨i.val, (leOfHom f.unop).trans i.property⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def tuplePresheaf {C : Type u} [Category.{u} C] (V : Cᵒᵖ ⥤ Type u) :
    SimplicialObject (Cᵒᵖ ⥤ Type u) where
  obj n :=
    { obj W := ToType n.unop → V.obj W
      map f := ↾fun t i => V.map f (t i)
      map_id W := by ext t i; simp
      map_comp f g := by ext t i; simp }
  map f := { app W := ↾fun t => t ∘ f.unop.toOrderHom }
  map_id _ := rfl
  map_comp _ _ := rfl

def freePresheafComplex {C : Type u} [Category.{u} C] (R : Cᵒᵖ ⥤ RingCat.{u})
    (V : Cᵒᵖ ⥤ Type u) : ChainComplex (PresheafOfModules.{u} R) ℕ :=
  AlternatingFaceMapComplex.obj (tuplePresheaf V ⋙ PresheafOfModules.free R)

theorem exact_of_objectwise {C : Type u} [Category.{u} C]
    (R : Cᵒᵖ ⥤ RingCat.{u}) (S : ShortComplex (PresheafOfModules.{u} R))
    (hS : ∀ W, (S.map (PresheafOfModules.evaluation R W)).Exact) : S.Exact := by
  simp only [ShortComplex.exact_iff_isZero_homology] at hS ⊢
  rw [IsZero.iff_id_eq_zero]
  ext1 W
  apply (IsZero.of_iso (hS W)
    (S.mapHomologyIso (PresheafOfModules.evaluation R W)).symm).eq_of_src

theorem evaluation_freePresheafComplex {C : Type u} [Category.{u} C]
    (R : Cᵒᵖ ⥤ RingCat.{u}) (V : Cᵒᵖ ⥤ Type u) (W : Cᵒᵖ) :
    ((PresheafOfModules.evaluation R W).mapHomologicalComplex _).obj
      (freePresheafComplex R V) = freeTupleComplex (R.obj W) (V.obj W) := by
  change ((alternatingFaceMapComplex _ ⋙
    (PresheafOfModules.evaluation R W).mapHomologicalComplex _).obj
      (tuplePresheaf V ⋙ PresheafOfModules.free R)) = _
  rw [map_alternatingFaceMapComplex]
  rfl

theorem freePresheafComplex_exact {C : Type u} [Category.{u} C]
    (R : Cᵒᵖ ⥤ RingCat.{u}) (V : Cᵒᵖ ⥤ Type u) (q : ℕ) :
    (freePresheafComplex R V).ExactAt (q + 1) := by
  change ((freePresheafComplex R V).sc (q + 1)).Exact
  apply exact_of_objectwise R
  intro W
  have h := freeTupleComplex_exact (R.obj W) (V.obj W) q
  rw [← evaluation_freePresheafComplex R V W] at h
  exact h

def freeSheafComplex {X : TopCat.{u}}
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (V : (Opens X)ᵒᵖ ⥤ Type u) : ChainComplex (SheafOfModules.{u} R) ℕ :=
  ((PresheafOfModules.sheafification (𝟙 R.obj)).mapHomologicalComplex _).obj
    (freePresheafComplex R.obj V)

theorem freeSheafComplex_exact {X : TopCat.{u}}
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (V : (Opens X)ᵒᵖ ⥤ Type u) (q : ℕ) :
    (freeSheafComplex R V).ExactAt (q + 1) := by
  change (((freePresheafComplex R.obj V).sc (q + 1)).map
    (PresheafOfModules.sheafification (𝟙 R.obj))).Exact
  exact (freePresheafComplex_exact R.obj V q).map _

end
end PiExponent.GeometrySupport.FreeCechResolution

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_FreeCechSections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.FreeCechSections

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology TopologicalSpace
open FreeCechResolution
open scoped Simplicial BigOperators

universe u
variable {X : TopCat.{u}} {J : Type u} (U : J → Opens X)

variable (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  (M : SheafOfModules.{u} R)

def freeTerm (q : ℕ) : SheafOfModules.{u} R :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).obj
    ((PresheafOfModules.free R.obj).obj ((tuplePresheaf (coverVertices U)).obj (op ⦋q⦌)))

def freeFace (q : ℕ) (k : Fin (q + 2)) : freeTerm U R (q + 1) ⟶ freeTerm U R q :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).map
    ((PresheafOfModules.free R.obj).map ((tuplePresheaf (coverVertices U)).δ k))

def boundary (q : ℕ) : freeTerm U R (q + 1) ⟶ freeTerm U R q :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).map
    ((freePresheafComplex R.obj (coverVertices U)).d (q + 1) q)

theorem boundary_eq_sum (q : ℕ) :
    boundary U R q = ∑ k : Fin (q + 2), (-1 : ℤ) ^ k.val • freeFace U R q k := by
  let : (PresheafOfModules.sheafification (𝟙 R.obj)).Additive :=
    CategoryTheory.Functor.additive_of_preserves_binary_products _
  dsimp only [boundary, freePresheafComplex, freeTerm]
  rw [AlternatingFaceMapComplex.obj_d_eq]
  rw [CategoryTheory.Functor.map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [CategoryTheory.Functor.map_zsmul]
  rfl

theorem boundary_squared (q : ℕ) : boundary U R (q + 1) ≫ boundary U R q = 0 := by
  unfold boundary
  erw [← CategoryTheory.Functor.map_comp, HomologicalComplex.d_comp_d,
    CategoryTheory.Functor.map_zero]
  rfl

def termShortComplex (q : ℕ) : ShortComplex (SheafOfModules.{u} R) :=
  ShortComplex.mk (boundary U R (q + 1)) (boundary U R q) (boundary_squared U R q)

end
end PiExponent.GeometrySupport.FreeCechSections

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveTupleCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.ProjectiveTupleCharts

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Projective PiExponentSeshadri.Geometry

universe u
variable {σ : Type u} [Fintype σ]

def tupleVariables {q : ℕ} (t : Fin (q + 1) → σ) (p : Fin (q + 1)) :
    Finset {j : σ // j ≠ t p} := by
  classical
  exact Finset.univ.filter (fun j => j.val ∈ Set.range t)

@[simp] theorem mem_tupleVariables {q : ℕ} (t : Fin (q + 1) → σ)
    (p : Fin (q + 1)) (j : {j : σ // j ≠ t p}) :
    j ∈ tupleVariables t p ↔ j.val ∈ Set.range t := by
  classical
  simp [tupleVariables]

theorem tupleVariables_support {q : ℕ} (t : Fin (q + 1) → σ) (p : Fin (q + 1)) :
    ({t p} : Set σ) ∪ Subtype.val '' (tupleVariables t p : Set {j : σ // j ≠ t p}) =
      Set.range t := by
  classical
  ext j
  constructor
  · rintro (h | ⟨a, ha, rfl⟩)
    · exact h ▸ Set.mem_range_self p
    · exact (mem_tupleVariables t p a).mp ha
  · intro hj
    by_cases hp : j = t p
    · exact Or.inl hp
    · exact Or.inr ⟨⟨j, hp⟩, (mem_tupleVariables t p _).mpr hj, rfl⟩

theorem tupleVariables_inf {α : Type*} [CompleteLattice α]
    (U : σ → α) {q : ℕ} (t : Fin (q + 1) → σ) (p : Fin (q + 1)) :
    U (t p) ⊓ (tupleVariables t p).inf (fun j => U j.val) = ⨅ i, U (t i) := by
  classical
  apply le_antisymm
  · apply le_iInf
    intro i
    by_cases h : t i = t p
    · rw [h]
      exact inf_le_left
    · exact inf_le_right.trans (Finset.inf_le
        ((mem_tupleVariables t p ⟨t i, h⟩).mpr (Set.mem_range_self i)))
  · apply le_inf (iInf_le _ p)
    apply Finset.le_inf
    intro j hj
    obtain ⟨i, hi⟩ := (mem_tupleVariables t p j).mp hj
    exact hi ▸ iInf_le (fun i => U (t i)) i

attribute [local instance] MvPolynomial.gradedAlgebra

end
end PiExponent.GeometrySupport.ProjectiveTupleCharts

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_InverseFrameRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.InverseFrames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} {M N : X.Modules}

lemma restrictionMap_cycle {C : Type*} [Category C]
    (F : X.Opensᵒᵖ ⥤ C) {U V : X.Opens} (h : V ≤ U) (k : U ≤ V) :
    F.map (homOfLE h).op ≫ F.map (homOfLE k).op = 𝟙 (F.obj (op U)) := by
  rw [← Functor.map_comp]
  rw [show (homOfLE h).op ≫ (homOfLE k).op = 𝟙 (op U) from Subsingleton.elim _ _]
  exact F.map_id _

end
end PiExponent.InverseFrames

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_CoherentExtFiniteness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CoherentExtFiniteness
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open PiExponentSeshadri.Geometry

theorem finite_middle_of_exact {K U V W : Type*} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Module.Finite K U] [Module.Finite K W]
    (f : U →ₗ[K] V) (g : V →ₗ[K] W) (h : Function.Exact f g) :
    Module.Finite K V := by
  have he : Function.Exact f g.rangeRestrict := by
    intro x
    rw [Subtype.ext_iff]
    exact h x
  exact Module.Finite.of_exact he g.surjective_rangeRestrict

universe w v u t k
variable {K : Type k} [Field K] {C : Type u} [Category.{v} C] [Abelian C]
    [Linear K C] [HasExt.{w} C]

def extLinearEquivBiproduct (A : C) {J : Type*} [Fintype J]
    {B : J → C} {c : Bicone B} (hc : c.IsBilimit) (q : ℕ) :
    Ext.{w} A c.pt q ≃ₗ[K] ∀ j, Ext.{w} A (B j) q :=
  { Ext.addEquivBiproduct A hc q with
    map_smul' := by
      intro a x
      funext j
      exact Ext.smul_comp x (Ext.mk₀ (c.π j)) (add_zero q) a }

theorem ext_finite_of_biproduct (A : C) {J : Type*} [Fintype J]
    {B : J → C} {c : Bicone B} (hc : c.IsBilimit) (q : ℕ)
    (hfinite : ∀ j, Module.Finite K (Ext.{w} A (B j) q)) :
    Module.Finite K (Ext.{w} A c.pt q) := by
  let (j : J) : Module.Finite K (Ext.{w} A (B j) q) := hfinite j
  exact Module.Finite.of_surjective (extLinearEquivBiproduct (K := K) A hc q).symm.toLinearMap
    (extLinearEquivBiproduct (K := K) A hc q).symm.surjective

structure FiniteCohomologyPresentation {ι : Type t} (A : C) (F : ι → C) (i : ι) where
  kernel : ι
  middle : C
  left : F kernel ⟶ middle
  right : middle ⟶ F i
  comp_zero : left ≫ right = 0
  shortExact : (ShortComplex.mk left right comp_zero).ShortExact
  finite : ∀ q, Module.Finite K (Ext.{w} A middle q)

end
end PiExponent.CoherentExtFiniteness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_FiniteCurveZeros
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {K : Type} [Field K] {X Y : Scheme}

lemma proper_finite_scheme_isFinite (f : X ⟶ Y) [IsProper f] [Finite X] : IsFinite f := by
  let : LocallyQuasiFinite f := .of_finite_preimage_singleton f (fun _ => Set.toFinite _)
  exact .of_isProper_of_locallyQuasiFinite f

lemma proper_finite_scheme_isAffine (f : X ⟶ Spec (CommRingCat.of K))
    [IsProper f] [Finite X] : IsAffine X := by
  let : IsFinite f := proper_finite_scheme_isFinite f
  exact isAffine_of_isAffineHom f

lemma proper_finite_functions (f : X ⟶ Spec (CommRingCat.of K))
    [IsProper f] [Finite X] :
    let _ : Algebra K Γ(X,⊤) :=
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
    FiniteDimensional K Γ(X,⊤) := by
  let : IsFinite f := proper_finite_scheme_isFinite f
  dsimp only
  exact f.finite_appTop.comp (RingHom.Finite.of_surjective
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (by
      exact (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.surjective))

end

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {K : Type} [Field K] {X : Scheme}

abbrev structuralStalkAlgebra (f : X ⟶ Spec (CommRingCat.of K)) (x : X) :
    Algebra K (X.presheaf.stalk x) :=
  ((X.presheaf.germ ⊤ x trivial).hom.comp
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)).toAlgebra

end

open AlgebraicGeometry CategoryTheory

end PiExponentSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_FiniteSupportCohomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.FiniteSupport

section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
lemma discrete_restriction_surjective {X : TopCat.{0}} [DiscreteTopology X]
    (F : X.Sheaf AddCommGrpCat.{0}) {U V : Opens X} (i : V ⟶ U) :
    Function.Surjective (F.obj.map i.op) := by
  classical
  intro s
  let W : Opens X := ⟨(U : Set X) \ V, isOpen_discrete _⟩
  let D : Bool → Opens X := fun b => if b then V else W
  let e : ∀ b, D b ⟶ U := fun b => homOfLE (by
    cases b
    · exact fun x hx => hx.1
    · exact i.le)
  have hcover : U ≤ ⨆ b, D b := by
    intro x hx
    by_cases hV : x ∈ V
    · exact Opens.mem_iSup.mpr ⟨true,hV⟩
    · exact Opens.mem_iSup.mpr ⟨false,hx,hV⟩
  let t : ∀ b, F.obj.obj (op (D b)) := fun b => match b with
    | true => s
    | false => 0
  have hc : TopCat.Presheaf.IsCompatible F.obj D t := by
    intro b c
    cases b <;> cases c
    · rfl
    · have h : D false ⊓ D true = ⊥ := by
        ext x
        change ((x ∈ U ∧ x ∉ V) ∧ x ∈ V) ↔ False
        tauto
      let : Subsingleton (F.obj.obj (op (D false ⊓ D true))) :=
        AddCommGrpCat.subsingleton_of_isZero (F.isTerminalOfEqEmpty h).isZero
      exact Subsingleton.elim _ _
    · have h : D true ⊓ D false = ⊥ := by
        ext x
        change (x ∈ V ∧ x ∈ U ∧ x ∉ V) ↔ False
        tauto
      let : Subsingleton (F.obj.obj (op (D true ⊓ D false))) :=
        AddCommGrpCat.subsingleton_of_isZero (F.isTerminalOfEqEmpty h).isZero
      exact Subsingleton.elim _ _
    · rfl
  obtain ⟨a,ha,_⟩ := F.existsUnique_gluing' D U e hcover t hc
  exact ⟨a,ha true⟩

variable {X Y : Scheme.{0}}

lemma proper_finite_discrete (p : X ⟶ Spec (CommRingCat.of ℂ))
    [IsProper p] [Finite X] : DiscreteTopology X := by
  let : IsFinite p := Geometry.proper_finite_scheme_isFinite p
  have he : p ⁻¹' ({⟨⊥, Ideal.isPrime_bot⟩} : Set (Spec (CommRingCat.of ℂ))) = Set.univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  have h := p.isDiscrete_preimage_singleton (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
  rw [he] at h
  exact isDiscrete_univ_iff.mp h

lemma pushforward_flasque (f : X ⟶ Y) [DiscreteTopology X] (M : X.Modules) :
    TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf Y.ringCatSheaf).obj
      ((Scheme.Modules.pushforward f).obj M)) where
  epi i := by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    exact discrete_restriction_surjective
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)
      ((Opens.map f.base).map i.unop)

end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry PiExponentSeshadri.Geometry

end PiExponentSeshadri.FiniteSupport

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_FiniteLineEuler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.FiniteSupport

section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} [DiscreteTopology X]

def pointOpen (x : X) : X.Opens := ⟨{x}, isOpen_discrete _⟩

lemma pointOpen_basis : Opens.IsBasis (Set.range (pointOpen (X := X))) := by
  apply Opens.isBasis_iff_nbhd.mpr
  intro U x hx
  exact ⟨pointOpen x, ⟨x,rfl⟩, rfl, fun y hy => by cases hy; exact hx⟩

end

open CategoryTheory AlgebraicGeometry PiExponentSeshadri.Geometry

end PiExponentSeshadri.FiniteSupport

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CartierSequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PiExponentSeshadri.CartierSequence
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

lemma chart_topIso_naturality {Y : Scheme.{0}} (j : Y ⟶ X) (U : X.Opens) :
    U.topIso.hom ≫ j.app U ≫ (j ⁻¹ᵁ U).topIso.inv = (j ∣_ U).appTop := by
  have H := (arrowResLEAppIso j U (j ⁻¹ᵁ U) le_rfl).hom.w
  change U.topIso.hom ≫ j.appLE U (j ⁻¹ᵁ U) le_rfl =
    (j.resLE U (j ⁻¹ᵁ U) le_rfl).appTop ≫ (j ⁻¹ᵁ U).topIso.hom at H
  rw [Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appLE_eq_app] at H
  apply (cancel_mono (j ⁻¹ᵁ U).topIso.hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using H

lemma restriction_principal (_p : X ⟶ Spec (CommRingCat.of ℂ))
    (I : X.IdealSheafData) (U : X.affineOpens) (r : Γ(U.1.toScheme,⊤))
    (hI : I.ideal U = Ideal.span {U.1.topIso.hom r}) :
    (I.subschemeι ∣_ U.1).ker.ideal ⟨⊤,isAffineOpen_top U.1.toScheme⟩ =
      Ideal.span {r} := by
  ext z
  rw [Scheme.Hom.ker_apply,RingHom.mem_ker]
  change (I.subschemeι ∣_ U.1).appTop z = 0 ↔ z ∈ Ideal.span {r}
  have hz : (I.subschemeι ∣_ U.1).appTop z = 0 ↔
      U.1.topIso.hom z ∈ I.ideal U := by
    rw [← chart_topIso_naturality]
    simp only [CommRingCat.comp_apply]
    rw [← I.ker_subschemeι_app U]
    change (I.subschemeι ⁻¹ᵁ U.1).topIso.inv
      (I.subschemeι.app U.1 (U.1.topIso.hom z)) = 0 ↔
      I.subschemeι.app U.1 (U.1.topIso.hom z) = 0
    exact map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
      (I.subschemeι ⁻¹ᵁ U.1).topIso.inv).injective
  rw [hz,hI,Ideal.mem_span_singleton,Ideal.mem_span_singleton]
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨U.1.topIso.inv a,?_⟩
    have h := congrArg U.1.topIso.inv ha
    simpa only [map_mul,U.1.topIso.hom_inv_id_apply] using h
  · rintro ⟨a,ha⟩
    refine ⟨U.1.topIso.hom a,?_⟩
    simpa only [map_mul] using congrArg U.1.topIso.hom ha

end
end PiExponentSeshadri.CartierSequence

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_BirationalValuationStalk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.BirationalValuationStalk
open CategoryTheory AlgebraicGeometry

theorem comp_eq_of_comp_eq {C : Type*} [Category C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (k : X ⟶ Z) (hcomp : g ≫ h = k) :
    (f ≫ g) ≫ h = f ≫ k :=
  (Category.assoc f g h).trans (congrArg (fun t => f ≫ t) hcomp)

universe u
variable {X : Scheme.{u}} [IsIntegral X]
variable {A E : Type u} [CommRing A] [IsLocalRing A]
  [Field E] [Algebra A E] [IsFractionRing A E]
variable (g : Spec (.of A) ⟶ X) (e : X.functionField ≃+* E)
variable (hgeneric : Spec.map (CommRingCat.ofHom (algebraMap A E)) ≫ g =
  Spec.map (CommRingCat.ofHom e.toRingHom) ≫ X.fromSpecStalk (genericPoint X))

include hgeneric


omit [IsFractionRing A E] in
theorem stalkClosedPointTo_field_compatibility :
    (algebraMap A E).comp (Scheme.stalkClosedPointTo g).hom =
      e.toRingHom.comp
        (algebraMap (X.presheaf.stalk (g (IsLocalRing.closedPoint A))) X.functionField) := by
  have h : Scheme.stalkClosedPointTo g ≫ CommRingCat.ofHom (algebraMap A E) =
      X.presheaf.stalkSpecializes (genericPoint_specializes (g (IsLocalRing.closedPoint A))) ≫
        CommRingCat.ofHom e.toRingHom := by
    apply Spec.map_injective
    apply (cancel_mono (X.fromSpecStalk (g (IsLocalRing.closedPoint A)))).mp
    let q := X.fromSpecStalk (g (IsLocalRing.closedPoint A))
    have hleft := comp_eq_of_comp_eq
      (Spec.map (CommRingCat.ofHom (algebraMap A E)))
      (Spec.map (Scheme.stalkClosedPointTo g)) q g
      (Scheme.Spec_stalkClosedPointTo_fromSpecStalk g)
    have hright := comp_eq_of_comp_eq
      (Spec.map (CommRingCat.ofHom e.toRingHom))
      (Spec.map (X.presheaf.stalkSpecializes
        (genericPoint_specializes (g (IsLocalRing.closedPoint A))))) q
      (X.fromSpecStalk (genericPoint X))
      (X.SpecMap_stalkSpecializes_fromSpecStalk
        (genericPoint_specializes (g (IsLocalRing.closedPoint A))))
    have hmapLeft := congrArg (fun k => k ≫ q)
      (Spec.map_comp (Scheme.stalkClosedPointTo g) (CommRingCat.ofHom (algebraMap A E)))
    have hmapRight := congrArg (fun k => k ≫ q)
      (Spec.map_comp (X.presheaf.stalkSpecializes
        (genericPoint_specializes (g (IsLocalRing.closedPoint A))))
        (CommRingCat.ofHom e.toRingHom))
    exact hmapLeft.trans (hleft.trans (hgeneric.trans (hright.symm.trans hmapRight.symm)))
  exact CommRingCat.hom_ext_iff.mp h


theorem stalkClosedPointTo_bijective
    [ValuationRing (X.presheaf.stalk (g (IsLocalRing.closedPoint A)))] :
    Function.Bijective (Scheme.stalkClosedPointTo g).hom := by
  let α := (Scheme.stalkClosedPointTo g).hom
  let β := e.symm.toRingHom.comp (algebraMap A E)
  have hcomp : β.comp α =
      algebraMap (X.presheaf.stalk (g (IsLocalRing.closedPoint A))) X.functionField := by
    apply RingHom.ext
    intro a
    apply e.injective
    have h := RingHom.congr_fun (stalkClosedPointTo_field_compatibility g e hgeneric) a
    change e (e.symm ((algebraMap A E) (α a))) =
      e ((algebraMap (X.presheaf.stalk (g (IsLocalRing.closedPoint A))) X.functionField) a)
    rw [e.apply_symm_apply]
    exact h
  have hβ : Function.Injective β := e.symm.injective.comp (IsFractionRing.injective A E)
  have hbij := bijective_rangeRestrict_comp_of_valuationRing α β hcomp
  refine ⟨fun a b hab => hbij.1 (congrArg β.rangeRestrict hab), ?_⟩
  intro a
  obtain ⟨b, hb⟩ := hbij.2 (β.rangeRestrict a)
  refine ⟨b, hβ ?_⟩
  exact congrArg Subtype.val hb

theorem stalkMap_isIso
    [ValuationRing (X.presheaf.stalk (g (IsLocalRing.closedPoint A)))] :
    IsIso (g.stalkMap (IsLocalRing.closedPoint A)) := by
  have : IsIso (Scheme.stalkClosedPointTo g) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (stalkClosedPointTo_bijective g e hgeneric)
  change IsIso (g.stalkMap _ ≫ (stalkClosedPointIso (.of A)).hom) at this
  exact IsIso.of_isIso_comp_right _ (stalkClosedPointIso (.of A)).hom

end PiExponent.BirationalValuationStalk

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveModelLocalOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Polynomial nonZeroDivisors
namespace PiExponent.CurveModelLocalOrder
universe u
open CurveNormalizationModel
open AlgebraicGeometry CategoryTheory

theorem addVal_ringEquiv
    {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (e : A ≃+* B) (a : A) :
    IsDiscreteValuationRing.addVal B (e a) = IsDiscreteValuationRing.addVal A a := by
  by_cases ha : a = 0
  · simp only [ha, map_zero, IsDiscreteValuationRing.addVal_zero]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_prime A
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ.irreducible
  rw [map_mul, map_pow, IsDiscreteValuationRing.addVal_def' u hπ.irreducible n]
  exact IsDiscreteValuationRing.addVal_def' (Units.map e.toMonoidHom u)
    (hπ.irreducible.map e) n

end PiExponent.CurveModelLocalOrder

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveModelGenericPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationModel
open CategoryTheory AlgebraicGeometry
open scoped Polynomial
universe u

theorem eqToHom_fromSpecStalk (X : Scheme.{u}) {x y : X} (h : x = y) :
    Spec.map (eqToHom (congrArg (fun z => X.presheaf.stalk z) h)) ≫
      X.fromSpecStalk x = X.fromSpecStalk y := by
  subst y
  simp

theorem functionFieldRestriction_fromSpecStalk {U X : Scheme.{u}}
    [IsIntegral U] [IsIntegral X] (i : U ⟶ X) [IsOpenImmersion i] :
    Spec.map (functionFieldRestriction i) ≫ X.fromSpecStalk (genericPoint X) =
      U.fromSpecStalk (genericPoint U) ≫ i := by
  unfold functionFieldRestriction
  rw [Spec.map_comp, Category.assoc,
    eqToHom_fromSpecStalk X (genericPoint_eq_of_isOpenImmersion i).symm]
  exact Scheme.SpecMap_stalkMap_fromSpecStalk i


theorem affineFunctionFieldEquiv_fromSpecStalk
    (A E : Type u) [CommRing A] [IsDomain A] [Field E]
    [Algebra A E] [IsFractionRing A E] :
    Spec.map (CommRingCat.ofHom (affineFunctionFieldEquiv A E).toRingHom) ≫
      (Spec (.of A)).fromSpecStalk (genericPoint (Spec (.of A))) =
      Spec.map (CommRingCat.ofHom (algebraMap A E)) := by
  erw [Spec.fromSpecStalk_eq', ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact affineFunctionFieldEquiv_toStalk A E

theorem affineRestriction_fromSpecStalk
    (A E : Type u) [CommRing A] [IsDomain A] [Field E]
    [Algebra A E] [IsFractionRing A E] {X : Scheme.{u}} [IsIntegral X]
    (i : Spec (.of A) ⟶ X) [IsOpenImmersion i] :
    Spec.map (functionFieldRestriction i ≫
      CommRingCat.ofHom (affineFunctionFieldEquiv A E).toRingHom) ≫
      X.fromSpecStalk (genericPoint X) =
      Spec.map (CommRingCat.ofHom (algebraMap A E)) ≫ i := by
  let e := Spec.map (CommRingCat.ofHom (affineFunctionFieldEquiv A E).toRingHom)
  let r := Spec.map (functionFieldRestriction i)
  let q := X.fromSpecStalk (genericPoint X)
  have hmap := congrArg (fun k => k ≫ q)
    (Spec.map_comp (functionFieldRestriction i)
      (CommRingCat.ofHom (affineFunctionFieldEquiv A E).toRingHom))
  have hrestrict := congrArg (fun k => e ≫ k) (functionFieldRestriction_fromSpecStalk i)
  have haffine := congrArg (fun k => k ≫ i) (affineFunctionFieldEquiv_fromSpecStalk A E)
  have hassoc := Category.assoc e
    ((Spec (.of A)).fromSpecStalk (genericPoint (Spec (.of A)))) i
  exact hmap.trans ((Category.assoc e r q).trans
    (hrestrict.trans (hassoc.symm.trans haffine)))

end PiExponent.CurveNormalizationModel

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveChartFunctionField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationModel
open CategoryTheory AlgebraicGeometry
universe u
variable (A E : Type u) [CommRing A] [IsDomain A] [Field E]
  [Algebra A E] [IsFractionRing A E]

def affineChartFunctionFieldMap {X : Scheme.{u}} [IsIntegral X]
    (i : Spec (.of A) ⟶ X) [IsOpenImmersion i] : X.functionField →+* E :=
  (affineFunctionFieldEquiv A E).toRingHom.comp (functionFieldRestriction i).hom

theorem restriction_congr {U X : Scheme.{u}} [IsIntegral U] [IsIntegral X]
    {i j : U ⟶ X} [IsOpenImmersion i] [IsOpenImmersion j] (h : i = j) :
    functionFieldRestriction i = functionFieldRestriction j := by
  subst j
  rfl

theorem affineChartFunctionFieldMap_eq_of_overlap
    (B G : Type u) [CommRing B] [IsDomain B] [CommRing G] [IsDomain G]
    [Algebra B E] [IsFractionRing B E] [Algebra G E] [IsFractionRing G E]
    [Algebra A G] [Algebra B G] [IsScalarTower A G E] [IsScalarTower B G E]
    {X : Scheme.{u}} [IsIntegral X]
    (iA : Spec (.of A) ⟶ X) (iB : Spec (.of B) ⟶ X)
    [IsOpenImmersion iA] [IsOpenImmersion iB]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A G)))]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B G)))]
    (h : Spec.map (CommRingCat.ofHom (algebraMap A G)) ≫ iA =
      Spec.map (CommRingCat.ofHom (algebraMap B G)) ≫ iB) :
    affineChartFunctionFieldMap A E iA = affineChartFunctionFieldMap B E iB := by
  have hr : functionFieldRestriction iA ≫
      functionFieldRestriction (Spec.map (CommRingCat.ofHom (algebraMap A G))) =
      functionFieldRestriction iB ≫
      functionFieldRestriction (Spec.map (CommRingCat.ofHom (algebraMap B G))) := by
    rw [← functionFieldRestriction_comp, ← functionFieldRestriction_comp]
    exact restriction_congr h
  apply RingHom.ext
  intro z
  have hz := congrArg (fun g => affineFunctionFieldEquiv G E (g z)) hr
  change affineFunctionFieldEquiv G E
    (functionFieldRestriction (Spec.map (CommRingCat.ofHom (algebraMap A G)))
      (functionFieldRestriction iA z)) =
    affineFunctionFieldEquiv G E
    (functionFieldRestriction (Spec.map (CommRingCat.ofHom (algebraMap B G)))
      (functionFieldRestriction iB z)) at hz
  have hA := RingHom.congr_fun (affineFunctionFieldEquiv_naturality A E G)
    (functionFieldRestriction iA z)
  have hB := RingHom.congr_fun (affineFunctionFieldEquiv_naturality B E G)
    (functionFieldRestriction iB z)
  exact hA.symm.trans (hz.trans hB)

end PiExponent.CurveNormalizationModel

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurvePlaceCenter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
universe u
namespace PiExponent.CurvePlaceCenter
open AlgebraicGeometry CategoryTheory
open CurveNormalizationModel

theorem fractionSpec_isDominant
    (A E : Type u) [CommRing A] [IsDomain A] [Field E] [Algebra A E] [IsFractionRing A E] :
    IsDominant (Spec.map (CommRingCat.ofHom (algebraMap A E))) := by
  constructor
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_univ_subset
  rw [← genericPoint_closure (Spec (CommRingCat.of A))]
  apply closure_mono
  rw [Set.singleton_subset_iff]
  refine ⟨(⊥ : PrimeSpectrum E), ?_⟩
  rw [genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  ext a
  change algebraMap A E a = 0 ↔ a = 0
  exact map_eq_zero_iff _ (IsFractionRing.injective A E)

theorem hom_ext_fraction
    (A E : Type u) [CommRing A] [IsDomain A] [Field E] [Algebra A E] [IsFractionRing A E]
    {Y : Scheme.{u}} [Y.IsSeparated] (g h : Spec (CommRingCat.of A) ⟶ Y)
    (heq : Spec.map (CommRingCat.ofHom (algebraMap A E)) ≫ g =
      Spec.map (CommRingCat.ofHom (algebraMap A E)) ≫ h) : g = h := by
  let := fractionSpec_isDominant A E
  exact ext_of_isDominant (Spec.map (CommRingCat.ofHom (algebraMap A E))) heq

end PiExponent.CurvePlaceCenter

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_LocalPullbackSectionOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry

namespace PiExponent.LocalPullbackSectionOrder


theorem topIso_germ_stalkMap {X : Scheme.{0}} (U : X.Opens) (y : U.toScheme) :
    U.topIso.hom ≫ X.presheaf.germ U (U.ι y) y.2 ≫ U.ι.stalkMap y =
      U.toScheme.presheaf.germ ⊤ y trivial := by
  have hmap : U.topIso.hom ≫ U.ι.app U =
      U.toScheme.presheaf.map (homOfLE (show U.ι ⁻¹ᵁ U ≤ ⊤ from le_top)).op := by
    rw [Scheme.Opens.ι_app, Scheme.Opens.topIso_hom]
    erw [← Functor.map_comp]
    rfl
  have hstalk := congrArg (fun k => U.topIso.hom ≫ k) (U.ι.germ_stalkMap U y y.2)
  have hres := congrArg (fun k => k ≫ U.toScheme.presheaf.germ (U.ι ⁻¹ᵁ U) y y.2) hmap
  exact hstalk.trans ((Category.assoc U.topIso.hom (U.ι.app U)
    (U.toScheme.presheaf.germ (U.ι ⁻¹ᵁ U) y y.2)).symm.trans
      (hres.trans (U.toScheme.presheaf.germ_res (homOfLE le_top) y y.2)))

theorem factor_coefficient_image {X : Scheme.{0}} {A : Type} [CommRing A] [IsLocalRing A]
    (U : X.Opens) (g : Spec (CommRingCat.of A) ⟶ U.toScheme)
    (c : Γ(U.toScheme, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom (g.appTop c) =
      (Scheme.stalkClosedPointTo (g ≫ U.ι))
        (X.presheaf.germ U ((g ≫ U.ι) (IsLocalRing.closedPoint A))
          (g (IsLocalRing.closedPoint A)).2 (U.topIso.hom c)) := by
  have h := topIso_germ_stalkMap U (g (IsLocalRing.closedPoint A))
  have hg := Scheme.germ_stalkClosedPointTo g ⊤ trivial
  simp only [Scheme.stalkClosedPointTo_comp]
  change ((g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom) c) =
    ((U.topIso.hom ≫ X.presheaf.germ U _ _ ≫ U.ι.stalkMap _ ≫
      Scheme.stalkClosedPointTo g) c)
  erw [← Category.assoc U.topIso.hom
    (X.presheaf.germ U _ _ ≫ U.ι.stalkMap _) (Scheme.stalkClosedPointTo g), h]
  rw [hg]
  congr 1

end PiExponent.LocalPullbackSectionOrder

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ExceptionalCurveDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ExceptionalCurveDegree
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry
variable {X Y : Scheme.{0}}

def localIdeal {A : Type} [CommRing A] (I : X.IdealSheafData)
    (q : Spec (CommRingCat.of A) ⟶ X) : Ideal A :=
  ((I.comap q).ideal ⟨⊤, isAffineOpen_top _⟩).map
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom

end
end PiExponent.ExceptionalCurveDegree

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_WeightedLocalSheaf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry
open PiExponent.WeightedLocalLattice
open scoped BigOperators
universe u

namespace PiExponent.WeightedLocalSheaf

def generatedSheaf
    {A K : Type u} {ι : Type*} [CommRing A] [Field K] [Algebra A K]
    (y : ι → K) (s : Finset ι) : (Spec (CommRingCat.of A)).Modules :=
  tilde (ModuleCat.of A (generatedLattice A y s))

def generatedSectionMap
    {A K : Type*} {ι : Type*} [CommRing A] [Field K] [Algebra A K]
    (y : ι → K) (s : Finset ι) (a : ι) (ha : a ∈ s) :
    A →ₗ[A] generatedLattice A y s where
  toFun c := ⟨c • y a, Submodule.smul_mem _ c (Submodule.subset_span ⟨a, ha, rfl⟩)⟩
  map_add' c d := by ext; simp [add_smul]
  map_smul' c d := by ext; simp [mul_smul]

theorem generatedSectionMap_bijective_of_span
    {A K : Type*} {ι : Type*} [CommRing A] [IsDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (y : ι → K) (s : Finset ι) (a : ι) (ha : a ∈ s) (hya : y a ≠ 0)
    (hspan : generatedLattice A y s = Submodule.span A {y a}) :
    Function.Bijective (generatedSectionMap (A := A) y s a ha) := by
  constructor
  · intro c d h
    have h' := congrArg (fun z : generatedLattice A y s => (z : K)) h
    change c • y a = d • y a at h'
    simp only [Algebra.smul_def] at h'
    exact IsFractionRing.injective A K (mul_right_cancel₀ hya h')
  · intro z
    have hz := hspan.le z.2
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hz
    exact ⟨c, Subtype.ext hc⟩

end PiExponent.WeightedLocalSheaf

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_WeightedSectionOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry
open PiExponent.WeightedLocalSheaf PiExponent.WeightedLocalLattice
open PiExponent.CurveLocalOrder
open scoped BigOperators

namespace PiExponent.WeightedSectionOrder


variable {A K : Type} {ι : Type*} [CommRing A] [IsDomain A]
  [Field K] [Algebra A K] [IsFractionRing A K]

def coordinateBasis (y : ι → K) (s : Finset ι) (a : ι) (ha : a ∈ s)
    (hya : y a ≠ 0) (hspan : generatedLattice A y s = Submodule.span A {y a}) :
    A ≃ₗ[A] generatedLattice A y s :=
  LinearEquiv.ofBijective (generatedSectionMap y s a ha)
    (generatedSectionMap_bijective_of_span y s a ha hya hspan)

end PiExponent.WeightedSectionOrder

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_GradedCech
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GradedCech
noncomputable section
open scoped BigOperators

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

variable {σR σM : Type*} [SetLike σR R]
  [SetLike σM M] [AddSubgroupClass σM M]
  (𝒜 : ℤ → σR) (𝓜 : ℤ → σM)
  [SetLike.GradedMonoid 𝒜] [SetLike.GradedSMul 𝒜 𝓜]

section Cover
variable {J : Type*} [DecidableEq J] (x : J → R) (hx : ∀ j, x j ∈ 𝒜 1)

def coverProduct (s : Finset J) : R := ∏ j ∈ s, x j

end Cover

end
end PiExponent.GradedCech

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveGlobalMonomialLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.CurveGlobalMonomialLocal
open AlgebraicGeometry CategoryTheory MvPolynomial
open WeightedSectionOrder
open WeightedLocalLattice PiExponentSeshadri.Projective
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

def monomialCoordinates {F E ι σ : Type} [CommRing F] [CommRing E] [Algebra F E]
    (a : σ → ι →₀ ℕ) (x : ι → E) (s : σ) : E :=
  eval₂Hom (algebraMap F E) x (monomial (a s) 1)

@[simp] theorem monomialCoordinates_zero
    {F E ι σ : Type} [CommRing F] [CommRing E] [Algebra F E]
    (a : σ → ι →₀ ℕ) (x : ι → E) (z : σ) (hz : a z = 0) :
    monomialCoordinates (F := F) a x z = 1 := by
  simp [monomialCoordinates, hz]

end PiExponent.CurveGlobalMonomialLocal

end

end OAI
end


