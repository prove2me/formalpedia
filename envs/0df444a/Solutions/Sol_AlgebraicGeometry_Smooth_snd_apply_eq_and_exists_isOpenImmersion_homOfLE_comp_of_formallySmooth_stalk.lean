-- Prove2me | solution 1 for AlgebraicGeometry.Smooth.snd_apply_eq_and_exists_isOpenImmersion_homOfLE_comp_of_formallySmooth_stalk
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/9fd16c3e-3092-5f97-9160-b60363705e29

import Mathlib
import Definitions.Def_NeronModelInfra_OmegaMinimalComponentData
import Theorems.Thm_AlgebraicGeometry_exists_isOpenImmersion_of_formallySmooth_stalk_of_isFractionRing_of_isDiscreteValuationRing
import Theorems.Thm_AlgebraicGeometry_Smooth_algebraMap_stalk_ne_zero_and_isPrime_span_of_apply_eq_closedPoint
import Theorems.Thm_AlgebraicGeometry_Smooth_isDiscreteValuationRing_stalk_of_forall_specializes
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Smooth_snd_apply_eq_and_exists_isOpenImmersion_homOfLE_comp_of_formallySmooth_stalk
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Z X Y : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R)) (f : X ⟶ Spec (CommRingCat.of R))
    (g : Y ⟶ Spec (CommRingCat.of R)) [Smooth z] [Smooth f] [Smooth g] [LocallyOfFiniteType g]
    (η : ↑(pullback z f)) (hη : (pullback.fst z f ≫ z).base η = IsLocalRing.closedPoint R)
    (hmax : ∀ y : ↑(pullback z f), y ⤳ η → (pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint R → y = η)
    (yT : ↑Y) (hyT : g.base yT = IsLocalRing.closedPoint R)
    (U₀ : (pullback z f).Opens) (hηU : η ∈ U₀)
    (v : (U₀ : Scheme.{u}) ⟶ pullback z g) (hv₁ : v ≫ pullback.fst z g = U₀.ι ≫ pullback.fst z f)
    (hgen : yT ⤳ (v ≫ pullback.snd z g).base ⟨η, hηU⟩)
    (hdom : IsDomain ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))
    (hdom' : IsDomain ((pullback z g).presheaf.stalk (v.base ⟨η, hηU⟩)))
    (hfrac : letI : Algebra ((pullback z g).presheaf.stalk (v.base ⟨η, hηU⟩)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)) :=
        ((algebraMap ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))).comp (v.stalkMap ⟨η, hηU⟩).hom).toAlgebra
      IsFractionRing ((pullback z g).presheaf.stalk (v.base ⟨η, hηU⟩)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)))
    (hfs : letI : Algebra ((pullback z g).presheaf.stalk (v.base ⟨η, hηU⟩)) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) := (v.stalkMap ⟨η, hηU⟩).hom.toAlgebra
      Algebra.FormallySmooth ((pullback z g).presheaf.stalk (v.base ⟨η, hηU⟩)) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)) :
    (v ≫ pullback.snd z g).base ⟨η, hηU⟩ = yT ∧
      ∃ (U₁ : (pullback z f).Opens) (_ : η ∈ U₁) (h₁ : U₁ ≤ U₀),
        IsOpenImmersion ((pullback z f).homOfLE h₁ ≫ v) := by
  classical

  set x : ↥(U₀ : Scheme.{u}) := ⟨η, hηU⟩ with hx
  have hU₀ι : ∀ u : ↥(U₀ : Scheme.{u}), U₀.ι.base u = u.1 := fun u => rfl

  have hQ : v ≫ pullback.fst z g ≫ z = U₀.ι ≫ pullback.fst z f ≫ z := by rw [← Category.assoc, hv₁, Category.assoc]

  have hxs : (U₀.ι ≫ pullback.fst z f ≫ z).base x = IsLocalRing.closedPoint R := by
    rw [Scheme.Hom.comp_apply]; exact hη
  have hxmax : ∀ y : ↥(U₀ : Scheme.{u}), y ⤳ x → (U₀.ι ≫ pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint R →
      y = x := by
    intro y hy hys
    apply U₀.ι.isOpenEmbedding.injective
    rw [Scheme.Hom.comp_apply] at hys
    exact hmax _ (hy.map U₀.ι.continuous) hys
  obtain ⟨_, hdvr⟩ :=
    AlgebraicGeometry.Smooth.isDiscreteValuationRing_stalk_of_forall_specializes R (U₀.ι ≫ pullback.fst z f ≫ z)
      x hxs hxmax
  haveI := hdom
  haveI := hdvr

  obtain ⟨ϖ, hϖirr⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖirr
  have hvxs : (pullback.fst z g ≫ z).base (v.base x) = IsLocalRing.closedPoint R := by
    rw [← Scheme.Hom.comp_apply, hQ]; exact hxs
  letI algQ : Algebra R ((pullback z g).presheaf.stalk (v.base x)) := NeronModelInfra.stalkAlgebra (pullback.fst z g ≫ z) (v.base x)
  obtain ⟨hπ0, hπ⟩ :=
    AlgebraicGeometry.Smooth.algebraMap_stalk_ne_zero_and_isPrime_span_of_apply_eq_closedPoint ϖ hϖ
      (pullback.fst z g ≫ z) (v.base x) hvxs
      (NeronModelInfra.fromSpecStalk_comp_eq_specMap_algebraMap_stalkAlgebra (pullback.fst z g ≫ z) (v.base x))

  haveI : LocallyOfFiniteType (v ≫ pullback.fst z g ≫ z) := by rw [hQ]; infer_instance
  haveI : LocallyOfFiniteType v := locallyOfFiniteType_of_comp v (pullback.fst z g ≫ z)
  haveI : IsLocallyNoetherian (pullback z g) := LocallyOfFiniteType.isLocallyNoetherian (pullback.fst z g ≫ z)
  haveI := hdom'
  obtain ⟨V₁, hxV₁, hV₁⟩ :=
    AlgebraicGeometry.exists_isOpenImmersion_of_formallySmooth_stalk_of_isFractionRing_of_isDiscreteValuationRing
      v x (algebraMap R _ ϖ) hπ0 hπ hfrac hfs

  let U₁ : (pullback z f).Opens := U₀.ι ''ᵁ V₁
  have h₁ : U₁ ≤ U₀ := by simpa using U₀.ι.image_le_opensRange V₁
  have hηU₁ : η ∈ U₁ := ⟨x, hxV₁, rfl⟩
  have hhom : (pullback z f).homOfLE h₁ = (U₀.ι.isoImage V₁).inv ≫ V₁.ι := by
    rw [← cancel_mono U₀.ι, Scheme.homOfLE_ι, Category.assoc, Scheme.Hom.isoImage_inv_ι]
  haveI hv : IsOpenImmersion ((pullback z f).homOfLE h₁ ≫ v) := by
    rw [hhom, Category.assoc]; infer_instance
  refine ⟨?_, U₁, hηU₁, h₁, hv⟩

  have hgen₁ : GeneralizingMap ((pullback z f).homOfLE h₁ ≫ v).base :=
    Topology.IsOpenEmbedding.generalizingMap ((pullback z f).homOfLE h₁ ≫ v).isOpenEmbedding
  have hgen₂ : GeneralizingMap (pullback.snd z g).base := Flat.generalizingMap _
  have hgenq := hgen₁.comp hgen₂
  set x₁ : ↥(U₁ : Scheme.{u}) := ⟨η, hηU₁⟩ with hx₁
  have hx₁x : ((pullback z f).homOfLE h₁).base x₁ = x := by
    apply U₀.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
    rfl
  have hstr : U₁.ι ≫ pullback.fst z f ≫ z = ((pullback z f).homOfLE h₁ ≫ v) ≫ pullback.snd z g ≫ g := by
    rw [← Scheme.homOfLE_ι (pullback z f) h₁, Category.assoc, ← hQ, pullback.condition, Category.assoc]
  have key : ∀ y' : ↥Y, y' ⤳ (pullback.snd z g).base (v.base x) → g.base y' = IsLocalRing.closedPoint R →
      y' = (pullback.snd z g).base (v.base x) := by
    intro y' hy' hy's
    have hy'' : y' ⤳ ((pullback.snd z g).base ∘ ((pullback z f).homOfLE h₁ ≫ v).base) x₁ := by
      rwa [Function.comp_apply, Scheme.Hom.comp_apply, hx₁x]
    obtain ⟨x', hx'x₁, hx'y⟩ := hgenq hy''
    have hsp : U₁.ι.base x' ⤳ η := hx'x₁.map U₁.ι.continuous
    have hx's : (pullback.fst z f ≫ z).base (U₁.ι.base x') = IsLocalRing.closedPoint R := by
      rw [← Scheme.Hom.comp_apply, hstr, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, ← Function.comp_apply
        (f := ⇑(ConcreteCategory.hom (pullback.snd z g).base)), hx'y]
      exact hy's
    have hx'η : U₁.ι.base x' = η := hmax _ hsp hx's
    have hx'eq : x' = x₁ := U₁.ι.isOpenEmbedding.injective hx'η
    rw [← hx'y, hx'eq, Function.comp_apply, Scheme.Hom.comp_apply, hx₁x]
  rw [Scheme.Hom.comp_apply] at hgen ⊢
  exact (key yT hgen hyT).symm

end S_AlgebraicGeometry_Smooth_snd_apply_eq_and_exists_isOpenImmersion_homOfLE_comp_of_formallySmooth_stalk
end P2MW
export P2MW.S_AlgebraicGeometry_Smooth_snd_apply_eq_and_exists_isOpenImmersion_homOfLE_comp_of_formallySmooth_stalk (solution)
