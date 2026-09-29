-- Prove2me | solution 1 for AlgebraicGeometry.exists_mem_and_isClosedImmersion_pullbackMap_opens_of_isFinite_morphismRestrict_of_isIso_fiberToSpecResidueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/5c789c4c-b854-5c16-99f7-0582b7e25d40

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_mem_and_isClosedImmersion_pullbackMap_opens_of_isFinite_morphismRestrict_of_isIso_fiberToSpecResidueField

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace P2mWs49A1Surj

universe u

theorem exists_smul_mem_range_of_surjective_fiber {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] (𝔭 : PrimeSpectrum A)
    (hs : Function.Surjective (algebraMap 𝔭.asIdeal.ResidueField (𝔭.asIdeal.Fiber B))) :
    ∃ s : A, s ∉ 𝔭.asIdeal ∧ ∀ b : B, ∃ a : A, s • b = algebraMap A B a := by
  classical
  let N : Submodule A B := LinearMap.range (Algebra.linearMap A B)
  have h1 : (1 : B) ∈ N := ⟨1, by simp⟩

  have hT : Function.Surjective (LinearMap.lTensor 𝔭.asIdeal.ResidueField N.mkQ) :=
    LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective N)
  have hzero : ∀ z : 𝔭.asIdeal.ResidueField ⊗[A] (B ⧸ N), z = 0 := by
    intro z
    obtain ⟨w, rfl⟩ := hT z
    obtain ⟨c, rfl⟩ := hs w
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      LinearMap.lTensor_tmul, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).mpr h1, tmul_zero]
  have hsub : Subsingleton (𝔭.asIdeal.ResidueField ⊗[A] (B ⧸ N)) :=
    ⟨fun a b => by rw [hzero a, hzero b]⟩
  have h𝔭 : 𝔭 ∉ Module.support A (B ⧸ N) := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct, not_nontrivial_iff_subsingleton]
    exact hsub
  rw [Module.mem_support_iff_of_finite, SetLike.not_le_iff_exists] at h𝔭
  obtain ⟨s, hs1, hs2⟩ := h𝔭
  refine ⟨s, hs2, fun b => ?_⟩
  have h3 : s • N.mkQ b = 0 := Module.mem_annihilator.mp hs1 _
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h3
  obtain ⟨a, ha⟩ := h3
  exact ⟨a, by rw [← ha]; rfl⟩

theorem surjective_algebraMap_fiber_of_isIso {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (𝔭 : PrimeSpectrum A)
    (h : IsIso ((Spec.map (CommRingCat.ofHom (algebraMap A B))).fiberToSpecResidueField 𝔭)) :
    Function.Surjective (algebraMap 𝔭.asIdeal.ResidueField (𝔭.asIdeal.Fiber B)) := by
  have e := Spec.fiberToSpecResidueFieldIso A B 𝔭
  have h1 : IsIso (Spec.map (CommRingCat.ofHom
      (algebraMap 𝔭.asIdeal.ResidueField (𝔭.asIdeal.Fiber B)))) :=
    ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff e).mp h
  have h2 : IsIso (CommRingCat.ofHom (algebraMap 𝔭.asIdeal.ResidueField (𝔭.asIdeal.Fiber B))).op := by
    haveI : IsIso (Scheme.Spec.map (CommRingCat.ofHom
        (algebraMap 𝔭.asIdeal.ResidueField (𝔭.asIdeal.Fiber B))).op) := h1
    exact isIso_of_fully_faithful Scheme.Spec _
  have h3 : IsIso (CommRingCat.ofHom (algebraMap 𝔭.asIdeal.ResidueField (𝔭.asIdeal.Fiber B))) :=
    isIso_of_op _
  exact ((ConcreteCategory.isIso_iff_bijective _).mp h3).2

theorem finite_app {Γ X : Scheme.{u}} (ψ : Γ ⟶ X) [IsFinite ψ] (U : X.Opens) (hU : IsAffineOpen U) :
    (ψ.app U).hom.Finite := by
  have h1 : targetAffineLocally (affineAnd RingHom.Finite) ψ := by
    have := (inferInstance : IsFinite ψ)
    rwa [HasAffineProperty.eq_targetAffineLocally (P := @IsFinite)] at this
  obtain ⟨-, h⟩ := (targetAffineLocally_affineAnd_iff RingHom.finite_respectsIso ψ).mp h1 U hU
  exact h

theorem exists_isClosedImmersion_morphismRestrict {Z' X' : Scheme.{u}} (g : Z' ⟶ X') [IsFinite g]
    (x : X') (hx : IsIso (g.fiberToSpecResidueField x)) :
    ∃ W : X'.Opens, x ∈ W ∧ IsClosedImmersion (g ∣_ W) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X'.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU' : IsAffineOpen U := hU
  have hV : IsAffineOpen (g ⁻¹ᵁ U) := hU'.preimage g

  obtain ⟨𝔮, rfl⟩ : x ∈ Set.range hU'.fromSpec := by rw [hU'.range_fromSpec]; exact hxU

  let φ := g.app U
  letI alg : Algebra Γ(X', U) Γ(Z', g ⁻¹ᵁ U) := φ.hom.toAlgebra
  haveI : Module.Finite Γ(X', U) Γ(Z', g ⁻¹ᵁ U) := finite_app g U hU'

  have H : hV.fromSpec ≫ g = Spec.map φ ≫ hU'.fromSpec := by
    have := IsAffineOpen.SpecMap_appLE_fromSpec g hU' hV (le_rfl : g ⁻¹ᵁ U ≤ g ⁻¹ᵁ U)
    rw [← Scheme.Hom.app_eq_appLE] at this
    exact this.symm
  have sq : IsPullback (Spec.map φ) hV.fromSpec hU'.fromSpec g :=
    IsOpenImmersion.isPullback _ _ _ _ H (by rw [hU'.opensRange_fromSpec, hV.opensRange_fromSpec])
  have fib := isPullback_fiberToSpecResidueField_of_isPullback sq.flip 𝔮
  haveI := hx
  obtain ⟨e, he⟩ : ∃ e : (Spec.map φ).fiber 𝔮 ≅ pullback (g.fiberToSpecResidueField (hU'.fromSpec 𝔮))
      (Spec.map (hU'.fromSpec.residueFieldMap 𝔮)),
      e.hom ≫ pullback.snd _ _ = (Spec.map φ).fiberToSpecResidueField 𝔮 :=
    ⟨fib.isoPullback, fib.isoPullback_hom_snd⟩
  have hiso : IsIso ((Spec.map φ).fiberToSpecResidueField 𝔮) := by
    rw [← he]; infer_instance
  have hsurj : Function.Surjective (algebraMap 𝔮.asIdeal.ResidueField (𝔮.asIdeal.Fiber Γ(Z', g ⁻¹ᵁ U))) :=
    surjective_algebraMap_fiber_of_isIso 𝔮 hiso
  obtain ⟨s, hs𝔮, hsb⟩ := exists_smul_mem_range_of_surjective_fiber 𝔮 hsurj
  refine ⟨X'.basicOpen s, ?_, ?_⟩
  · change 𝔮 ∈ hU'.fromSpec ⁻¹ᵁ X'.basicOpen s
    rw [hU'.fromSpec_preimage_basicOpen]
    exact (PrimeSpectrum.mem_basicOpen _ _).mpr hs𝔮
  · haveI := hU'.isLocalization_basicOpen s
    haveI := hV.isLocalization_basicOpen (g.app U s)
    have hmap : Function.Surjective (IsLocalization.Away.map Γ(X', X'.basicOpen s)
        Γ(Z', Z'.basicOpen (g.app U s)) (g.app U).hom s) := by
      intro z
      obtain ⟨⟨b, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers ((g.app U) s)) z
      obtain ⟨a, ha⟩ := hsb b
      have ha' : (g.app U).hom s * b = (g.app U).hom a := by rw [Algebra.smul_def] at ha; exact ha
      refine ⟨IsLocalization.mk' _ a ⟨s ^ (n + 1), pow_mem (Submonoid.mem_powers s) (n + 1)⟩, ?_⟩
      rw [IsLocalization.Away.map, IsLocalization.map_mk', IsLocalization.mk'_eq_iff_eq]
      simp only [map_pow]
      congr 1
      rw [← ha', pow_succ, mul_assoc]
    have hε : Function.Bijective (Z'.presheaf.map (eqToHom (Scheme.preimage_basicOpen g s)).op).hom :=
      ConcreteCategory.bijective_of_isIso (Z'.presheaf.map (eqToHom (Scheme.preimage_basicOpen g s)).op)
    have happ : Function.Surjective (g.app (X'.basicOpen s)).hom := by
      rw [hU'.app_basicOpen_eq_away_map g hV s, CommRingCat.hom_comp, CommRingCat.hom_ofHom]
      exact hε.2.comp hmap
    have h1 : IsClosedImmersion (Spec.map (g.appLE (X'.basicOpen s) (g ⁻¹ᵁ X'.basicOpen s) le_rfl)) := by
      rw [← Scheme.Hom.app_eq_appLE]; exact IsClosedImmersion.spec_of_surjective _ happ
    have h2 := Scheme.Opens.toSpecΓ_SpecMap_appLE g (X'.basicOpen s) (g ⁻¹ᵁ X'.basicOpen s) le_rfl
    have hUs : IsAffineOpen (X'.basicOpen s) := hU'.basicOpen s
    have hVs : IsAffineOpen (g ⁻¹ᵁ X'.basicOpen s) := by
      rw [Scheme.preimage_basicOpen]; exact hV.basicOpen _
    haveI : IsIso (X'.basicOpen s).toSpecΓ := by rw [← hUs.isoSpec_hom]; infer_instance
    haveI : IsIso (g ⁻¹ᵁ X'.basicOpen s).toSpecΓ := by rw [← hVs.isoSpec_hom]; infer_instance
    have h3 : IsClosedImmersion (g.resLE (X'.basicOpen s) (g ⁻¹ᵁ X'.basicOpen s) le_rfl ≫
        (X'.basicOpen s).toSpecΓ) := by
      rw [← h2]; infer_instance
    have h4 : IsClosedImmersion (g.resLE (X'.basicOpen s) (g ⁻¹ᵁ X'.basicOpen s) le_rfl) :=
      (MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion) _ _).mp h3
    rwa [Scheme.Hom.resLE_eq_morphismRestrict] at h4

end P2mWs49A1Surj

open P2mWs49A1Surj in
theorem solution
    {X Y Z : Scheme.{0}} (p : Z ⟶ Y) (q : X ⟶ Y) (h : Z ⟶ X) (w : h ≫ q = p)
    [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
    [IsProper q] [Flat q] [LocallyOfFinitePresentation q]
    (y : Y) (V₀ : Y.Opens) (hy₀ : y ∈ V₀) (hfin : IsFinite (h ∣_ (q ⁻¹ᵁ V₀)))
    (hfib : ∀ x : X, q.base x = y → IsIso (h.fiberToSpecResidueField x)) :
    ∃ V : Y.Opens, y ∈ V ∧
      IsClosedImmersion (pullback.map p V.ι q V.ι h (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp])) := by
  haveI := hfin

  have loc : ∀ x : X, q.base x = y → ∃ U : X.Opens, x ∈ U ∧ IsClosedImmersion (h ∣_ U) := by
    intro x hx
    have hxO : x ∈ q ⁻¹ᵁ V₀ := by show q.base x ∈ V₀; rw [hx]; exact hy₀
    have sqO := (isPullback_morphismRestrict h (q ⁻¹ᵁ V₀)).flip
    have fib := isPullback_fiberToSpecResidueField_of_isPullback sqO ⟨x, hxO⟩
    have hpt : q.base ((q ⁻¹ᵁ V₀).ι.base ⟨x, hxO⟩) = y := hx
    haveI : IsIso (h.fiberToSpecResidueField ((q ⁻¹ᵁ V₀).ι.base ⟨x, hxO⟩)) := hfib _ hpt
    obtain ⟨e, he⟩ : ∃ e : (h ∣_ q ⁻¹ᵁ V₀).fiber ⟨x, hxO⟩ ≅
        pullback (h.fiberToSpecResidueField ((q ⁻¹ᵁ V₀).ι.base ⟨x, hxO⟩))
          (Spec.map ((q ⁻¹ᵁ V₀).ι.residueFieldMap ⟨x, hxO⟩)),
        e.hom ≫ pullback.snd _ _ = (h ∣_ q ⁻¹ᵁ V₀).fiberToSpecResidueField ⟨x, hxO⟩ :=
      ⟨fib.isoPullback, fib.isoPullback_hom_snd⟩
    have hiso : IsIso ((h ∣_ q ⁻¹ᵁ V₀).fiberToSpecResidueField ⟨x, hxO⟩) := by
      rw [← he]; infer_instance
    obtain ⟨W, hxW, hW⟩ := exists_isClosedImmersion_morphismRestrict (h ∣_ q ⁻¹ᵁ V₀) ⟨x, hxO⟩ hiso
    refine ⟨(q ⁻¹ᵁ V₀).ι ''ᵁ W, ⟨⟨x, hxO⟩, hxW, rfl⟩, ?_⟩
    exact (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion (morphismRestrictRestrict h (q ⁻¹ᵁ V₀) W)).mp hW
  choose U hU using loc

  let Wset : Set X := ⋃ x : {x : X // q.base x = y}, (U x.1 x.2 : Set X)
  have hWopen : IsOpen Wset := isOpen_iUnion fun x => (U x.1 x.2).isOpen
  let V : Y.Opens := ⟨(q.base '' Wsetᶜ)ᶜ, (q.isClosedMap _ hWopen.isClosed_compl).isOpen_compl⟩
  have hyV : y ∈ V := by
    rintro ⟨x, hx, hxy⟩
    exact hx (Set.mem_iUnion.mpr ⟨⟨x, hxy⟩, (hU x hxy).1⟩)
  have hVW : ∀ x : X, q.base x ∈ V → x ∈ Wset := fun x hx => by
    by_contra H; exact hx ⟨x, H, rfl⟩
  refine ⟨V, hyV, ?_⟩

  set m := pullback.map p V.ι q V.ι h (𝟙 _) (𝟙 _) (by rw [Category.comp_id, w])
    (by rw [Category.comp_id, Category.id_comp]) with hm
  have hm₁ : m ≫ pullback.fst q V.ι = pullback.fst p V.ι ≫ h := pullback.lift_fst _ _ _
  have hm₂ : m ≫ pullback.snd q V.ι = pullback.snd p V.ι := by
    rw [hm, pullback.lift_snd, Category.comp_id]
  have big : IsPullback (pullback.fst p V.ι) (m ≫ pullback.snd q V.ι) (h ≫ q) V.ι := by
    rw [hm₂, w]; exact IsPullback.of_hasPullback p V.ι
  have hT : IsPullback (pullback.fst p V.ι) m h (pullback.fst q V.ι) :=
    big.of_bot hm₁.symm (IsPullback.of_hasPullback q V.ι)
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := @IsClosedImmersion)
  intro x'

  have hx'V : q.base ((pullback.fst q V.ι).base x') ∈ V := by
    have h1 : (pullback.fst q V.ι ≫ q).base x' = (pullback.snd q V.ι ≫ V.ι).base x' := by
      rw [pullback.condition]
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h1
    rw [h1]
    have : V.ι.base ((pullback.snd q V.ι).base x') ∈ Set.range V.ι.base := ⟨_, rfl⟩
    rwa [Scheme.Opens.range_ι] at this
  obtain ⟨⟨x₀, hx₀⟩, hxU⟩ := Set.mem_iUnion.mp (hVW _ hx'V)
  refine ⟨(pullback.fst q V.ι) ⁻¹ᵁ (U x₀ hx₀), hxU, ?_⟩
  have hU₀ : IsClosedImmersion (h ∣_ U x₀ hx₀) := (hU x₀ hx₀).2

  have r1 := isPullback_morphismRestrict m ((pullback.fst q V.ι) ⁻¹ᵁ (U x₀ hx₀))
  have big2 := r1.paste_vert hT.flip

  have hrange : Set.range ((m ⁻¹ᵁ ((pullback.fst q V.ι) ⁻¹ᵁ (U x₀ hx₀))).ι ≫ pullback.fst p V.ι).base ⊆
      Set.range (h ⁻¹ᵁ (U x₀ hx₀)).ι.base := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    show h.base (((m ⁻¹ᵁ ((pullback.fst q V.ι) ⁻¹ᵁ (U x₀ hx₀))).ι ≫ pullback.fst p V.ι).base z) ∈ U x₀ hx₀
    have e1 : ((m ⁻¹ᵁ ((pullback.fst q V.ι) ⁻¹ᵁ (U x₀ hx₀))).ι ≫ pullback.fst p V.ι ≫ h).base z =
        (m ∣_ ((pullback.fst q V.ι) ⁻¹ᵁ (U x₀ hx₀)) ≫ ((pullback.fst q V.ι) ⁻¹ᵁ (U x₀ hx₀)).ι ≫
          pullback.fst q V.ι).base z := by
      rw [← hm₁, ← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    have e2 : h.base (((m ⁻¹ᵁ ((pullback.fst q V.ι) ⁻¹ᵁ (U x₀ hx₀))).ι ≫ pullback.fst p V.ι).base z) =
        (pullback.fst q V.ι).base ((((pullback.fst q V.ι) ⁻¹ᵁ (U x₀ hx₀)).ι).base
          ((m ∣_ ((pullback.fst q V.ι) ⁻¹ᵁ (U x₀ hx₀))).base z)) := by
      simp only [Scheme.Hom.comp_base, TopCat.comp_app] at e1 ⊢
      exact e1
    rw [e2]
    exact (((m ∣_ ((pullback.fst q V.ι) ⁻¹ᵁ (U x₀ hx₀))).base z)).2
  let t' := IsOpenImmersion.lift (h ⁻¹ᵁ (U x₀ hx₀)).ι _ hrange
  have ht' : t' ≫ (h ⁻¹ᵁ (U x₀ hx₀)).ι = (m ⁻¹ᵁ ((pullback.fst q V.ι) ⁻¹ᵁ (U x₀ hx₀))).ι ≫ pullback.fst p V.ι :=
    IsOpenImmersion.lift_fac _ _ _
  have big3 : IsPullback (t' ≫ (h ⁻¹ᵁ (U x₀ hx₀)).ι) (m ∣_ ((pullback.fst q V.ι) ⁻¹ᵁ (U x₀ hx₀))) h
      ((pullback.fst q V.ι ∣_ (U x₀ hx₀)) ≫ (U x₀ hx₀).ι) := by
    rw [ht', morphismRestrict_ι]; exact big2.flip
  have pcomm : t' ≫ (h ∣_ U x₀ hx₀) =
      (m ∣_ ((pullback.fst q V.ι) ⁻¹ᵁ (U x₀ hx₀))) ≫ (pullback.fst q V.ι ∣_ (U x₀ hx₀)) := by
    rw [← cancel_mono (U x₀ hx₀).ι]
    simp only [Category.assoc]
    rw [morphismRestrict_ι, morphismRestrict_ι, ← Category.assoc t', ht', Category.assoc, ← hm₁,
      ← Category.assoc ((m ⁻¹ᵁ ((pullback.fst q V.ι) ⁻¹ᵁ (U x₀ hx₀))).ι) m (pullback.fst q V.ι),
      ← morphismRestrict_ι, Category.assoc]
  have fin := big3.of_right pcomm (isPullback_morphismRestrict h (U x₀ hx₀)).flip
  exact MorphismProperty.of_isPullback fin hU₀

end S_AlgebraicGeometry_exists_mem_and_isClosedImmersion_pullbackMap_opens_of_isFinite_morphismRestrict_of_isIso_fiberToSpecResidueField
end P2MW
export P2MW.S_AlgebraicGeometry_exists_mem_and_isClosedImmersion_pullbackMap_opens_of_isFinite_morphismRestrict_of_isIso_fiberToSpecResidueField (solution)
