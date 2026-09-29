-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.kernelIsTwoTorsion_of_forall_kernelIsTwoTorsion_pullback_of_isPullback_pi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/03e243e6-8bbd-5392-b1ee-87ba1cc90718

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_kernelIsTwoTorsion_of_forall_kernelIsTwoTorsion_pullback_of_isPullback_pi

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

open TopologicalSpace Opposite

namespace KTClopen

variable {R₀ : Type} [CommRing R₀] {B : Scheme.{0}} {b : B ⟶ Spec (CommRingCat.of R₀)} (G : RelativeGroupLaw R₀ b)

theorem eq_one_of_mul_self {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R₀)) (P : SchemeHomOver t b)
    (h : G.mul t P P = P) : P = G.one t := by
  calc P = G.mul t (G.one t) P := (G.one_mul t P).symm
    _ = G.mul t (G.mul t (G.inv t P) P) P := by rw [G.inv_mul_cancel]
    _ = G.mul t (G.inv t P) (G.mul t P P) := G.mul_assoc t _ _ _
    _ = G.mul t (G.inv t P) P := by rw [h]
    _ = G.one t := G.inv_mul_cancel t P

theorem one_natural {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R₀)) (t' : T' ⟶ Spec (CommRingCat.of R₀))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') : schemeHomOverComp ψ hψ (G.one t) = G.one t' :=
  eq_one_of_mul_self G t' _ (by rw [← G.mul_natural, G.mul_one])

theorem one_val_congr {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R₀)} (h : t₁ = t₂) :
    (G.one t₁).1 = (G.one t₂).1 := by subst h; rfl

theorem mul_val_congr {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R₀)} (h : t₁ = t₂)
    (P Q : SchemeHomOver t₁ b) (P' Q' : SchemeHomOver t₂ b) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (G.mul t₁ P Q).1 = (G.mul t₂ P' Q').1 := by
  subst h
  obtain ⟨p, hp⟩ := P; obtain ⟨p', hp'⟩ := P'; obtain ⟨q, hq⟩ := Q; obtain ⟨q', hq'⟩ := Q'
  simp only at hP hQ
  subst hP; subst hQ; rfl

end KTClopen

namespace LocIsoCover

theorem locIsoOnBase_of_cover {S : Type} [CommRing S] {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of S)) (M M' : X.Modules)
    {J : Type} (Sj : J → Type) [∀ j, CommRing (Sj j)] (τ : ∀ j, Spec (CommRingCat.of (Sj j)) ⟶ Spec (CommRingCat.of S))
    [∀ j, IsOpenImmersion (τ j)] (hcov : ∀ s : ↥(Spec (CommRingCat.of S)), ∃ (j : J) (y : ↥(Spec (CommRingCat.of (Sj j)))), τ j y = s)
    {Xj : J → Scheme.{0}} (gj : ∀ j, Xj j ⟶ Spec (CommRingCat.of (Sj j))) (ρ : ∀ j, Xj j ⟶ X)
    (hρ : ∀ j, IsPullback (ρ j) (gj j) g (τ j))
    (h : ∀ j, LocIsoOnBase (gj j) ((Scheme.Modules.pullback (ρ j)).obj M) ((Scheme.Modules.pullback (ρ j)).obj M')) :
    LocIsoOnBase g M M' := by
  classical
  intro s
  obtain ⟨i, y, hy⟩ := hcov s
  obtain ⟨Ui, hyU, ⟨ei⟩⟩ := h i y
  let U : (Spec (CommRingCat.of S)).Opens := ⟨τ i '' (Ui : Set _), (τ i).isOpenEmbedding.isOpenMap _ Ui.isOpen⟩
  refine ⟨U, ⟨y, hyU, hy⟩, ?_⟩
  haveI : IsOpenImmersion (ρ i) := by
    rw [← (hρ i).isoPullback_hom_fst]; infer_instance
  have hsq : ∀ w, τ i (gj i w) = g (ρ i w) := fun w => by
    have := congrArg (fun φ => φ w) (hρ i).w
    simp only [Scheme.Hom.comp_apply] at this
    exact this.symm
  have hrange : Set.range (g ⁻¹ᵁ U).ι = Set.range (((gj i) ⁻¹ᵁ Ui).ι ≫ ρ i) := by
    ext x
    rw [Scheme.Opens.range_ι]
    constructor
    · rintro ⟨u, hu, hux⟩
      have hx : x ∈ Set.range (pullback.fst g (τ i)) := by
        rw [Scheme.Pullback.range_fst]; exact ⟨u, hux⟩
      obtain ⟨p, rfl⟩ := hx
      have hw : ρ i ((hρ i).isoPullback.inv p) = pullback.fst g (τ i) p := by
        rw [← Scheme.Hom.comp_apply, (hρ i).isoPullback_inv_fst]
      refine ⟨⟨(hρ i).isoPullback.inv p, ?_⟩, ?_⟩
      · change gj i ((hρ i).isoPullback.inv p) ∈ (Ui : Set _)
        have h1 := hsq ((hρ i).isoPullback.inv p)
        rw [hw, ← hux] at h1
        rwa [(τ i).isOpenEmbedding.injective h1]
      · rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
        exact hw
    · rintro ⟨⟨w, hw⟩, rfl⟩
      rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
      exact ⟨gj i w, hw, hsq w⟩
  let φ := IsOpenImmersion.isoOfRangeEq (g ⁻¹ᵁ U).ι (((gj i) ⁻¹ᵁ Ui).ι ≫ ρ i) hrange
  have hfac : φ.hom ≫ ((gj i) ⁻¹ᵁ Ui).ι ≫ ρ i = (g ⁻¹ᵁ U).ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  exact ⟨(Scheme.Modules.pullbackCongr hfac.symm).app M ≪≫
    ((Scheme.Modules.pullbackComp φ.hom (((gj i) ⁻¹ᵁ Ui).ι ≫ ρ i)).app M).symm ≪≫
    (Scheme.Modules.pullback φ.hom).mapIso
      (((Scheme.Modules.pullbackComp ((gj i) ⁻¹ᵁ Ui).ι (ρ i)).app M).symm ≪≫ ei ≪≫
        (Scheme.Modules.pullbackComp ((gj i) ⁻¹ᵁ Ui).ι (ρ i)).app M') ≪≫
    (Scheme.Modules.pullbackComp φ.hom (((gj i) ⁻¹ᵁ Ui).ι ≫ ρ i)).app M' ≪≫
    (Scheme.Modules.pullbackCongr hfac).app M'⟩

end LocIsoCover

namespace ClopenGlueRoot
theorem locIsoOnBase_congr {S' : Type} [CommRing S'] {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of S')) {M M' N N' : X.Modules}
    (eM : M ≅ N) (eM' : M' ≅ N') (h : LocIsoOnBase g M M') : LocIsoOnBase g N N' := by
  intro s
  obtain ⟨U, hs, ⟨e⟩⟩ := h s
  exact ⟨U, hs, ⟨((Scheme.Modules.pullback _).mapIso eM).symm ≪≫ e ≪≫ (Scheme.Modules.pullback _).mapIso eM'⟩⟩
end ClopenGlueRoot

open KTClopen in
theorem solution
    {k : ℕ} (C : Fin k → Type) [∀ i, CommRing (C i)]
    {A' : Scheme.{0}} (f' : A' ⟶ Spec (CommRingCat.of (∀ i, C i))) (L' : RelativeGroupLaw (∀ i, C i) f')
    (𝓛 : A'.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    {Ai : Fin k → Scheme.{0}} (fi : ∀ i, Ai i ⟶ Spec (CommRingCat.of (C i))) (v : ∀ i, Ai i ⟶ A')
    (hv : ∀ i, IsPullback (v i) (fi i) f' (Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i))))
    (Li : ∀ i, RelativeGroupLaw (C i) (fi i))
    (hLi : ∀ (i : Fin k) (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of (C i))) (P Q : SchemeHomOver t (fi i)),
      ((Li i).mul t P Q).1 ≫ v i =
        (L'.mul (t ≫ Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i)))
          ⟨P.1 ≫ v i, by rw [Category.assoc, (hv i).w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ v i, by rw [Category.assoc, (hv i).w, ← Category.assoc, Q.2]⟩).1)
    (h : ∀ i, KernelIsTwoTorsion (fi i) (Li i) ((Scheme.Modules.pullback (v i)).obj 𝓛)) :
    KernelIsTwoTorsion f' L' 𝓛 := by
  classical
  intro R _ t x

  let σ : ∀ i, Spec (CommRingCat.of (C i)) ⟶ Spec (CommRingCat.of (∀ i, C i)) := fun i =>
    Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i))
  haveI hσ : ∀ i, IsOpenImmersion (σ i) := fun i =>
    (inferInstance : IsOpenImmersion (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (C ·) i))))
  have hcov : ∀ s : ↥(Spec (CommRingCat.of (∀ i, C i))), ∃ (i : Fin k) (y : ↥(Spec (CommRingCat.of (C i)))), σ i y = s := by
    intro s
    let Rf : Fin k → CommRingCat.{0} := fun i => CommRingCat.of (C i)
    obtain ⟨⟨j, y⟩, hy⟩ := (sigmaMk (fun i => Spec (Rf i))).surjective (inv (sigmaSpec Rf) s)
    refine ⟨j, y, ?_⟩
    rw [sigmaMk_mk] at hy
    have e := congrArg (fun φ => φ y) (ι_sigmaSpec Rf j)
    simp only [Scheme.Hom.comp_apply] at e
    change (Spec.map (CommRingCat.ofHom (Pi.evalRingHom C j))) y = s
    rw [← e, hy, ← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl
  let 𝒰 : (Spec (CommRingCat.of (∀ i, C i))).OpenCover :=
    Scheme.Cover.mkOfCovers (Fin k) (fun i => Spec (CommRingCat.of (C i))) σ hcov
  let 𝒱 := 𝒰.pullback₁ t
  haveI : ∀ i, IsAffineHom (𝒰.f i) := fun i => by change IsAffineHom (σ i); infer_instance
  haveI : ∀ i, IsAffineHom (𝒱.f i) := fun i => MorphismProperty.pullback_fst _ _ inferInstance
  haveI : ∀ i, IsAffine (𝒱.X i) := fun i => isAffine_of_isAffineHom (𝒱.f i)

  let τ : ∀ i, Spec (Γ(𝒱.X i, ⊤)) ⟶ Spec (CommRingCat.of R) := fun i => (𝒱.X i).isoSpec.inv ≫ 𝒱.f i
  let tᵢ : ∀ i, Spec (Γ(𝒱.X i, ⊤)) ⟶ Spec (CommRingCat.of (C i)) := fun i => (𝒱.X i).isoSpec.inv ≫ 𝒰.pullbackHom t i
  have hτt : ∀ i, τ i ≫ t = tᵢ i ≫ σ i := fun i => by
    simp only [τ, tᵢ, Category.assoc]
    rw [← Scheme.Cover.pullbackHom_map]
    rfl
  haveI : ∀ i, IsOpenImmersion (τ i) := fun i => inferInstance
  have hτcov : ∀ s : ↥(Spec (CommRingCat.of R)), ∃ (i : Fin k) (y : ↥(Spec (Γ(𝒱.X i, ⊤)))), τ i y = s := by
    intro s
    obtain ⟨i, z, hz⟩ := Scheme.Cover.exists_eq 𝒱 s
    refine ⟨i, (𝒱.X i).isoSpec.hom z, ?_⟩
    change ((𝒱.X i).isoSpec.hom ≫ (𝒱.X i).isoSpec.inv ≫ 𝒱.f i) z = s
    rw [Iso.hom_inv_id_assoc]; exact hz

  let xᵢ : ∀ i, SchemeHomOver (tᵢ i) (fi i) := fun i =>
    ⟨(hv i).lift (τ i ≫ x.1) (tᵢ i) (by rw [Category.assoc, x.2, hτt]), (hv i).lift_snd _ _ _⟩
  have hxv : ∀ i, (xᵢ i).1 ≫ v i = τ i ≫ x.1 := fun i => (hv i).lift_fst _ _ _

  let vv : ∀ i, pullback (fi i) (fi i) ⟶ pullback f' f' := fun i =>
    pullback.lift (pullback.fst _ _ ≫ v i) (pullback.snd _ _ ≫ v i)
      (by rw [Category.assoc, Category.assoc, (hv i).w, ← Category.assoc, pullback.condition, Category.assoc])
  let ρ : ∀ i, pullback (fi i) (tᵢ i) ⟶ pullback f' t := fun i =>
    pullback.lift (pullback.fst _ _ ≫ v i) (pullback.snd _ _ ≫ τ i)
      (by rw [Category.assoc, Category.assoc, (hv i).w, hτt, ← Category.assoc, pullback.condition, Category.assoc])
  have hρ₁ : ∀ i, ρ i ≫ pullback.fst f' t = pullback.fst (fi i) (tᵢ i) ≫ v i := fun i => pullback.lift_fst _ _ _
  have hρ₂ : ∀ i, ρ i ≫ pullback.snd f' t = pullback.snd (fi i) (tᵢ i) ≫ τ i := fun i => pullback.lift_snd _ _ _
  have hρ : ∀ i, IsPullback (ρ i) (pullback.snd (fi i) (tᵢ i)) (pullback.snd f' t) (τ i) := by
    intro i
    have big : IsPullback (ρ i ≫ pullback.fst f' t) (pullback.snd (fi i) (tᵢ i)) f' (τ i ≫ t) := by
      rw [hρ₁, hτt]
      exact IsPullback.paste_horiz (IsPullback.of_hasPullback (fi i) (tᵢ i)) (hv i)
    exact big.of_right (hρ₂ i) (IsPullback.of_hasPullback f' t)
  have hslice : ∀ i, sliceAt (fi i) (xᵢ i) ≫ vv i = ρ i ≫ sliceAt f' x := by
    intro i
    apply pullback.hom_ext
    · simp only [sliceAt, vv, ρ, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [sliceAt, vv, ρ, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, hxv]

  have hadd : ∀ i, vv i ≫ addMor f' L' = addMor (fi i) (Li i) ≫ v i := by
    intro i
    change vv i ≫ (L'.mul _ _ _).1 = ((Li i).mul _ _ _).1 ≫ v i
    rw [hLi]
    have nat := congrArg Subtype.val
      (L'.mul_natural (pullback.fst f' f' ≫ f') (vv i ≫ pullback.fst f' f' ≫ f') (vv i) rfl
        ⟨pullback.fst f' f', rfl⟩ ⟨pullback.snd f' f', pullback.condition.symm⟩)
    rw [schemeHomOverComp] at nat
    change vv i ≫ _ = _ at nat
    rw [nat]
    exact mul_val_congr L' (by rw [pullback.lift_fst_assoc, Category.assoc, (hv i).w, Category.assoc]) _ _ _ _
      (by change vv i ≫ _ = _ ≫ _; rw [pullback.lift_fst]) (by change vv i ≫ _ = _ ≫ _; rw [pullback.lift_snd])
  have eS : ∀ i, Nonempty ((Scheme.Modules.pullback (sliceAt (fi i) (xᵢ i))).obj
      (mumfordBundle (fi i) (Li i) ((Scheme.Modules.pullback (v i)).obj 𝓛)) ≅
      (Scheme.Modules.pullback (ρ i)).obj ((Scheme.Modules.pullback (sliceAt f' x)).obj (mumfordBundle f' L' 𝓛))) := by
    intro i
    obtain ⟨d⟩ := h𝓛.pullback_dual_monoidalV2 (v i)
    have eΛ : (Scheme.Modules.pullback (vv i)).obj (mumfordBundle f' L' 𝓛) ≅
        mumfordBundle (fi i) (Li i) ((Scheme.Modules.pullback (v i)).obj 𝓛) := by
      unfold mumfordBundle
      exact Scheme.Modules.pullbackTensorObjIso (vv i) _ _ ≪≫
        (((Scheme.Modules.pullbackComp (vv i) (addMor f' L')).app 𝓛 ≪≫ (Scheme.Modules.pullbackCongr (hadd i)).app 𝓛 ≪≫
            ((Scheme.Modules.pullbackComp (addMor (fi i) (Li i)) (v i)).app 𝓛).symm) ⊗ᵢ
          (Scheme.Modules.pullbackTensorObjIso (vv i) _ _ ≪≫
            (((Scheme.Modules.pullbackComp (vv i) (pullback.fst f' f')).app _ ≪≫
                (Scheme.Modules.pullbackCongr (pullback.lift_fst _ _ _ : vv i ≫ pullback.fst f' f' = pullback.fst _ _ ≫ v i)).app _ ≪≫
                ((Scheme.Modules.pullbackComp (pullback.fst (fi i) (fi i)) (v i)).app _).symm ≪≫
                (Scheme.Modules.pullback _).mapIso d) ⊗ᵢ
             ((Scheme.Modules.pullbackComp (vv i) (pullback.snd f' f')).app _ ≪≫
                (Scheme.Modules.pullbackCongr (pullback.lift_snd _ _ _ : vv i ≫ pullback.snd f' f' = pullback.snd _ _ ≫ v i)).app _ ≪≫
                ((Scheme.Modules.pullbackComp (pullback.snd (fi i) (fi i)) (v i)).app _).symm ≪≫
                (Scheme.Modules.pullback _).mapIso d))))
    exact ⟨(Scheme.Modules.pullback _).mapIso eΛ.symm ≪≫ (Scheme.Modules.pullbackComp _ _).app _ ≪≫
      (Scheme.Modules.pullbackCongr (hslice i)).app _ ≪≫ ((Scheme.Modules.pullbackComp _ _).app _).symm⟩

  have hvone : ∀ i, ((Li i).one (tᵢ i)).1 ≫ v i = (L'.one (tᵢ i ≫ σ i)).1 := by
    intro i
    let O : SchemeHomOver (tᵢ i ≫ σ i) f' := ⟨((Li i).one (tᵢ i)).1 ≫ v i,
      by rw [Category.assoc, (hv i).w, ← Category.assoc, ((Li i).one (tᵢ i)).2]⟩
    have hO : O = L'.one (tᵢ i ≫ σ i) := by
      apply eq_one_of_mul_self
      apply Subtype.ext
      have := hLi i _ (tᵢ i) ((Li i).one (tᵢ i)) ((Li i).one (tᵢ i))
      rw [(Li i).mul_one] at this
      exact this.symm
    exact congrArg Subtype.val hO

  have hsq : ∀ i, ((Li i).mul (tᵢ i) (xᵢ i) (xᵢ i)).1 ≫ v i = τ i ≫ (L'.mul t x x).1 := by
    intro i
    rw [hLi]
    have nat := congrArg Subtype.val (L'.mul_natural t (τ i ≫ t) (τ i) rfl x x)
    rw [schemeHomOverComp] at nat
    change τ i ≫ _ = _ at nat
    rw [nat]
    exact mul_val_congr L' (hτt i).symm _ _ _ _ (hxv i) (hxv i)
  have hone_nat : ∀ i, τ i ≫ (L'.one t).1 = (L'.one (tᵢ i ≫ σ i)).1 := fun i => by
    rw [← one_val_congr L' (hτt i)]
    exact congrArg Subtype.val (one_natural L' t (τ i ≫ t) (τ i) rfl)
  haveI : ∀ i, Mono (v i) := fun i => by
    haveI : IsOpenImmersion (v i) := by rw [← (hv i).isoPullback_hom_fst]; infer_instance
    infer_instance
  constructor
  ·
    intro hx
    have hpiece : ∀ i, (Li i).mul (tᵢ i) (xᵢ i) (xᵢ i) = (Li i).one (tᵢ i) := by
      intro i
      refine (h i _ (tᵢ i) (xᵢ i)).1 ?_
      obtain ⟨eS⟩ := eS i
      intro s
      obtain ⟨U, hsU, ⟨e⟩⟩ := hx (τ i s)
      refine ⟨τ i ⁻¹ᵁ U, hsU, ?_⟩
      have hpre : pullback.snd (fi i) (tᵢ i) ⁻¹ᵁ (τ i ⁻¹ᵁ U) = ρ i ⁻¹ᵁ (pullback.snd f' t ⁻¹ᵁ U) := by
        rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hρ₂]
      rw [hpre]
      exact ⟨(Scheme.Modules.pullback _).mapIso eS ≪≫ (Scheme.Modules.pullbackComp _ _).app _ ≪≫
        (Scheme.Modules.pullbackCongr (morphismRestrict_ι (ρ i) (pullback.snd f' t ⁻¹ᵁ U)).symm).app _ ≪≫
        ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
        (Scheme.Modules.pullback (ρ i ∣_ (pullback.snd f' t ⁻¹ᵁ U))).mapIso (e ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _) ≪≫
        Scheme.Modules.pullbackTensorUnitObjIso _ ≪≫ (Scheme.Modules.pullbackTensorUnitObjIso _).symm⟩
    apply Subtype.ext
    apply Scheme.Cover.hom_ext 𝒱
    intro i
    rw [← cancel_epi (𝒱.X i).isoSpec.inv]
    change τ i ≫ (L'.mul t x x).1 = τ i ≫ (L'.one t).1
    rw [← hsq, hpiece, hvone, hone_nat]
  ·
    intro hmul
    have hpiece : ∀ i, (Li i).mul (tᵢ i) (xᵢ i) (xᵢ i) = (Li i).one (tᵢ i) := by
      intro i
      apply Subtype.ext
      rw [← cancel_mono (v i), hsq, hmul, hone_nat, hvone]
    refine LocIsoCover.locIsoOnBase_of_cover (pullback.snd f' t) _ _ (fun i => Γ(𝒱.X i, ⊤)) τ hτcov
      (fun i => pullback.snd (fi i) (tᵢ i)) ρ hρ fun i => ?_
    obtain ⟨eS⟩ := eS i
    exact ClopenGlueRoot.locIsoOnBase_congr _ eS (Scheme.Modules.pullbackTensorUnitObjIso _).symm ((h i _ (tᵢ i) (xᵢ i)).2 (hpiece i))

end S_AlgebraicGeometry_Polarisation_kernelIsTwoTorsion_of_forall_kernelIsTwoTorsion_pullback_of_isPullback_pi
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_kernelIsTwoTorsion_of_forall_kernelIsTwoTorsion_pullback_of_isPullback_pi (solution)
