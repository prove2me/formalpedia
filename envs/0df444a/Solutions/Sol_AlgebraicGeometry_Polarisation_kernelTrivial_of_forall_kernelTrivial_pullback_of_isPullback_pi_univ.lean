-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.kernelTrivial_of_forall_kernelTrivial_pullback_of_isPullback_pi_univ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/6accd4dc-a155-5fc1-a8cc-ba71e610d9b4

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

namespace P2MW.S_AlgebraicGeometry_Polarisation_kernelTrivial_of_forall_kernelTrivial_pullback_of_isPullback_pi_univ

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

universe u

open TopologicalSpace Opposite

namespace PiSpecCover

variable {k : ℕ} (C : Fin k → Type u) [∀ i, CommRing (C i)]

noncomputable def θ : (∀ i, C i) ≃+* (∀ j : ULift.{u} (Fin k), C j.down) :=
  RingEquiv.piCongrLeft' C Equiv.ulift.symm

theorem eval_comp_θ (i : Fin k) :
    (Pi.evalRingHom (fun j : ULift.{u} (Fin k) => C j.down) (ULift.up i)).comp (θ C).toRingHom = Pi.evalRingHom C i := by
  ext f; rfl

theorem specMap_eval (i : Fin k) :
    Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i)) =
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun j : ULift.{u} (Fin k) => C j.down) (ULift.up i))) ≫
        Spec.map (CommRingCat.ofHom (θ C).toRingHom) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, eval_comp_θ]

scoped instance : IsIso (Spec.map (CommRingCat.ofHom (θ C).toRingHom)) := by
  change IsIso (Scheme.Spec.map (Quiver.Hom.op (θ C).toCommRingCatIso.hom))
  infer_instance

theorem exists_eval_eq (s : ↥(Spec (CommRingCat.of (∀ i, C i)))) :
    ∃ (i : Fin k) (y : ↥(Spec (CommRingCat.of (C i)))), Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i)) y = s := by
  let Rf : ULift.{u} (Fin k) → CommRingCat.{u} := fun j => CommRingCat.of (C j.down)
  let Θ := Spec.map (CommRingCat.ofHom (θ C).toRingHom)
  obtain ⟨⟨j, y⟩, hy⟩ := (sigmaMk (fun j => Spec (Rf j))).surjective (inv (sigmaSpec Rf) (inv Θ s))
  refine ⟨j.down, y, ?_⟩
  rw [sigmaMk_mk] at hy
  have e := congrArg (fun φ => φ y) (ι_sigmaSpec Rf j)
  simp only [Scheme.Hom.comp_apply] at e
  rw [specMap_eval, Scheme.Hom.comp_apply]
  change Θ ((Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun j => ↑(Rf j)) j))) y) = s
  have h1 : ∀ x, (sigmaSpec Rf) ((inv (sigmaSpec Rf)) x) = x := fun x => by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl
  have h2 : ∀ x, Θ ((inv Θ) x) = x := fun x => by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl
  rw [← e, hy]
  change Θ ((sigmaSpec Rf) ((inv (sigmaSpec Rf)) ((inv Θ) s))) = s
  rw [h1, h2]

theorem isEmpty_of_comp_eval_eq {i₁ i₂ : Fin k} (h : i₁ ≠ i₂) {Z : Scheme.{u}}
    (a : Z ⟶ Spec (CommRingCat.of (C i₁))) (b : Z ⟶ Spec (CommRingCat.of (C i₂)))
    (hab : a ≫ Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i₁)) = b ≫ Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i₂))) :
    IsEmpty ↥Z := by
  let Rf : ULift.{u} (Fin k) → CommRingCat.{u} := fun j => CommRingCat.of (C j.down)
  rw [specMap_eval C i₁, specMap_eval C i₂, ← Category.assoc, ← Category.assoc, cancel_mono] at hab
  have hab' : (a ≫ Sigma.ι (fun j => Spec (Rf j)) (ULift.up i₁)) ≫ sigmaSpec Rf =
      (b ≫ Sigma.ι (fun j => Spec (Rf j)) (ULift.up i₂)) ≫ sigmaSpec Rf := by
    rw [Category.assoc, Category.assoc, ι_sigmaSpec, ι_sigmaSpec]; exact hab
  rw [cancel_mono] at hab'
  exact isEmpty_of_commSq_sigmaι_of_ne ⟨hab'⟩ (fun e => h (congrArg ULift.down e))

end PiSpecCover
p2m_reactivate "P2MW.S_AlgebraicGeometry_Polarisation_kernelTrivial_of_forall_kernelTrivial_pullback_of_isPullback_pi_univ.PiSpecCover"

namespace KTClopen

variable {R₀ : Type u} [CommRing R₀] {B : Scheme.{u}} {b : B ⟶ Spec (CommRingCat.of R₀)} (G : RelativeGroupLaw R₀ b)

theorem eq_one_of_mul_self {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R₀)) (P : SchemeHomOver t b)
    (h : G.mul t P P = P) : P = G.one t := by
  calc P = G.mul t (G.one t) P := (G.one_mul t P).symm
    _ = G.mul t (G.mul t (G.inv t P) P) P := by rw [G.inv_mul_cancel]
    _ = G.mul t (G.inv t P) (G.mul t P P) := G.mul_assoc t _ _ _
    _ = G.mul t (G.inv t P) P := by rw [h]
    _ = G.one t := G.inv_mul_cancel t P

theorem one_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R₀)) (t' : T' ⟶ Spec (CommRingCat.of R₀))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') : schemeHomOverComp ψ hψ (G.one t) = G.one t' :=
  eq_one_of_mul_self G t' _ (by rw [← G.mul_natural, G.mul_one])

theorem one_val_congr {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R₀)} (h : t₁ = t₂) :
    (G.one t₁).1 = (G.one t₂).1 := by subst h; rfl

theorem mul_val_congr {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R₀)} (h : t₁ = t₂)
    (P Q : SchemeHomOver t₁ b) (P' Q' : SchemeHomOver t₂ b) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (G.mul t₁ P Q).1 = (G.mul t₂ P' Q').1 := by
  subst h
  obtain ⟨p, hp⟩ := P; obtain ⟨p', hp'⟩ := P'; obtain ⟨q, hq⟩ := Q; obtain ⟨q', hq'⟩ := Q'
  simp only at hP hQ
  subst hP; subst hQ; rfl

end KTClopen
p2m_reactivate "P2MW.S_AlgebraicGeometry_Polarisation_kernelTrivial_of_forall_kernelTrivial_pullback_of_isPullback_pi_univ.PiSpecCover"

open KTClopen in
theorem solution
    {k : ℕ} (C : Fin k → Type u) [∀ i, CommRing (C i)]
    {A' : Scheme.{u}} (f' : A' ⟶ Spec (CommRingCat.of (∀ i, C i))) (L' : RelativeGroupLaw (∀ i, C i) f')
    (𝓛 : A'.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    {Ai : Fin k → Scheme.{u}} (fi : ∀ i, Ai i ⟶ Spec (CommRingCat.of (C i))) (v : ∀ i, Ai i ⟶ A')
    (hv : ∀ i, IsPullback (v i) (fi i) f' (Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i))))
    (Li : ∀ i, RelativeGroupLaw (C i) (fi i))
    (hLi : ∀ (i : Fin k) (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of (C i))) (P Q : SchemeHomOver t (fi i)),
      ((Li i).mul t P Q).1 ≫ v i =
        (L'.mul (t ≫ Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i)))
          ⟨P.1 ≫ v i, by rw [Category.assoc, (hv i).w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ v i, by rw [Category.assoc, (hv i).w, ← Category.assoc, Q.2]⟩).1)
    (h : ∀ i, KernelTrivial (fi i) (Li i) ((Scheme.Modules.pullback (v i)).obj 𝓛)) :
    KernelTrivial f' L' 𝓛 := by
  classical
  intro R _ t x hx

  let σ : ∀ i, Spec (CommRingCat.of (C i)) ⟶ Spec (CommRingCat.of (∀ i, C i)) := fun i =>
    Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i))
  haveI hσ : ∀ i, IsOpenImmersion (σ i) := fun i =>
    (inferInstance : IsOpenImmersion (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (C ·) i))))
  have hcov : ∀ s : ↥(Spec (CommRingCat.of (∀ i, C i))), ∃ (i : Fin k) (y : ↥(Spec (CommRingCat.of (C i)))), σ i y = s :=
    fun s => PiSpecCover.exists_eval_eq C s
  let 𝒰 : (Spec (CommRingCat.of (∀ i, C i))).OpenCover :=
    Scheme.Cover.mkOfCovers (Fin k) (fun i => Spec (CommRingCat.of (C i))) σ hcov
  let 𝒱 := 𝒰.pullback₁ t

  have key : ∀ i, 𝒱.f i ≫ x.1 = 𝒱.f i ≫ (L'.one t).1 := by
    intro i

    haveI : IsAffineHom (𝒰.f i) := by change IsAffineHom (σ i); infer_instance
    haveI : IsAffineHom (𝒱.f i) := MorphismProperty.pullback_fst _ _ inferInstance
    haveI : IsAffine (𝒱.X i) := isAffine_of_isAffineHom (𝒱.f i)
    let eT := (𝒱.X i).isoSpec
    let τ : Spec (Γ(𝒱.X i, ⊤)) ⟶ Spec (CommRingCat.of R) := eT.inv ≫ 𝒱.f i
    let tᵢ : Spec (Γ(𝒱.X i, ⊤)) ⟶ Spec (CommRingCat.of (C i)) := eT.inv ≫ 𝒰.pullbackHom t i
    have hτt : τ ≫ t = tᵢ ≫ σ i := by
      simp only [τ, tᵢ, Category.assoc]
      rw [← Scheme.Cover.pullbackHom_map]
      rfl

    let xᵢ : SchemeHomOver tᵢ (fi i) :=
      ⟨(hv i).lift (τ ≫ x.1) tᵢ (by rw [Category.assoc, x.2, hτt]), (hv i).lift_snd _ _ _⟩
    have hxv : xᵢ.1 ≫ v i = τ ≫ x.1 := (hv i).lift_fst _ _ _

    let vv : pullback (fi i) (fi i) ⟶ pullback f' f' :=
      pullback.lift (pullback.fst _ _ ≫ v i) (pullback.snd _ _ ≫ v i)
        (by rw [Category.assoc, Category.assoc, (hv i).w, ← Category.assoc, pullback.condition, Category.assoc])
    let ρ : pullback (fi i) tᵢ ⟶ pullback f' t :=
      pullback.lift (pullback.fst _ _ ≫ v i) (pullback.snd _ _ ≫ τ)
        (by rw [Category.assoc, Category.assoc, (hv i).w, hτt, ← Category.assoc, pullback.condition, Category.assoc])
    have hρ₂ : ρ ≫ pullback.snd f' t = pullback.snd (fi i) tᵢ ≫ τ := pullback.lift_snd _ _ _
    have hslice : sliceAt (fi i) xᵢ ≫ vv = ρ ≫ sliceAt f' x := by
      apply pullback.hom_ext
      · simp only [sliceAt, vv, ρ, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      · simp only [sliceAt, vv, ρ, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, hxv]

    have hadd : vv ≫ addMor f' L' = addMor (fi i) (Li i) ≫ v i := by
      change vv ≫ (L'.mul _ _ _).1 = ((Li i).mul _ _ _).1 ≫ v i
      rw [hLi]
      have nat := congrArg Subtype.val
        (L'.mul_natural (pullback.fst f' f' ≫ f') (vv ≫ pullback.fst f' f' ≫ f') vv rfl
          ⟨pullback.fst f' f', rfl⟩ ⟨pullback.snd f' f', pullback.condition.symm⟩)
      rw [schemeHomOverComp] at nat
      change vv ≫ _ = _ at nat
      rw [nat]
      exact mul_val_congr L' (by rw [pullback.lift_fst_assoc, Category.assoc, (hv i).w, Category.assoc]) _ _ _ _
        (by change vv ≫ _ = _ ≫ _; rw [pullback.lift_fst]) (by change vv ≫ _ = _ ≫ _; rw [pullback.lift_snd])
    have eΛ : Nonempty ((Scheme.Modules.pullback vv).obj (mumfordBundle f' L' 𝓛) ≅
        mumfordBundle (fi i) (Li i) ((Scheme.Modules.pullback (v i)).obj 𝓛)) := by
      obtain ⟨d⟩ := h𝓛.pullback_dual_monoidalV2 (v i)
      unfold mumfordBundle
      exact ⟨Scheme.Modules.pullbackTensorObjIso vv _ _ ≪≫
        (((Scheme.Modules.pullbackComp vv (addMor f' L')).app 𝓛 ≪≫ (Scheme.Modules.pullbackCongr hadd).app 𝓛 ≪≫
            ((Scheme.Modules.pullbackComp (addMor (fi i) (Li i)) (v i)).app 𝓛).symm) ⊗ᵢ
          (Scheme.Modules.pullbackTensorObjIso vv _ _ ≪≫
            (((Scheme.Modules.pullbackComp vv (pullback.fst f' f')).app _ ≪≫
                (Scheme.Modules.pullbackCongr (pullback.lift_fst _ _ _ : vv ≫ pullback.fst f' f' = pullback.fst _ _ ≫ v i)).app _ ≪≫
                ((Scheme.Modules.pullbackComp (pullback.fst (fi i) (fi i)) (v i)).app _).symm ≪≫
                (Scheme.Modules.pullback _).mapIso d) ⊗ᵢ
             ((Scheme.Modules.pullbackComp vv (pullback.snd f' f')).app _ ≪≫
                (Scheme.Modules.pullbackCongr (pullback.lift_snd _ _ _ : vv ≫ pullback.snd f' f' = pullback.snd _ _ ≫ v i)).app _ ≪≫
                ((Scheme.Modules.pullbackComp (pullback.snd (fi i) (fi i)) (v i)).app _).symm ≪≫
                (Scheme.Modules.pullback _).mapIso d))))⟩

    have hxᵢ : LocIsoOnBase (pullback.snd (fi i) tᵢ)
        ((Scheme.Modules.pullback (sliceAt (fi i) xᵢ)).obj (mumfordBundle (fi i) (Li i) ((Scheme.Modules.pullback (v i)).obj 𝓛)))
        (𝟙_ _) := by
      obtain ⟨eΛ⟩ := eΛ

      have eS : (Scheme.Modules.pullback (sliceAt (fi i) xᵢ)).obj (mumfordBundle (fi i) (Li i) ((Scheme.Modules.pullback (v i)).obj 𝓛)) ≅
          (Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback (sliceAt f' x)).obj (mumfordBundle f' L' 𝓛)) :=
        (Scheme.Modules.pullback _).mapIso eΛ.symm ≪≫ (Scheme.Modules.pullbackComp _ _).app _ ≪≫
          (Scheme.Modules.pullbackCongr hslice).app _ ≪≫ ((Scheme.Modules.pullbackComp _ _).app _).symm
      intro s
      obtain ⟨U, hsU, ⟨e⟩⟩ := hx (τ s)
      refine ⟨τ ⁻¹ᵁ U, hsU, ?_⟩
      have hpre : pullback.snd (fi i) tᵢ ⁻¹ᵁ (τ ⁻¹ᵁ U) = ρ ⁻¹ᵁ (pullback.snd f' t ⁻¹ᵁ U) := by
        rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hρ₂]
      rw [hpre]
      refine ⟨(Scheme.Modules.pullback _).mapIso eS ≪≫ (Scheme.Modules.pullbackComp _ _).app _ ≪≫
        (Scheme.Modules.pullbackCongr (morphismRestrict_ι ρ (pullback.snd f' t ⁻¹ᵁ U)).symm).app _ ≪≫
        ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
        (Scheme.Modules.pullback (ρ ∣_ (pullback.snd f' t ⁻¹ᵁ U))).mapIso (e ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _) ≪≫
        Scheme.Modules.pullbackTensorUnitObjIso _ ≪≫ (Scheme.Modules.pullbackTensorUnitObjIso _).symm⟩

    have hone : xᵢ = (Li i).one tᵢ := h i _ tᵢ xᵢ hxᵢ

    have hvone : ((Li i).one tᵢ).1 ≫ v i = (L'.one (tᵢ ≫ σ i)).1 := by
      let O : SchemeHomOver (tᵢ ≫ σ i) f' := ⟨((Li i).one tᵢ).1 ≫ v i,
        by rw [Category.assoc, (hv i).w, ← Category.assoc, ((Li i).one tᵢ).2]⟩
      have hO : O = L'.one (tᵢ ≫ σ i) := by
        apply eq_one_of_mul_self
        apply Subtype.ext
        have := hLi i _ tᵢ ((Li i).one tᵢ) ((Li i).one tᵢ)
        rw [(Li i).mul_one] at this
        exact this.symm
      exact congrArg Subtype.val hO
    calc 𝒱.f i ≫ x.1 = eT.hom ≫ τ ≫ x.1 := by simp only [τ, eT, Category.assoc, Iso.hom_inv_id_assoc]
      _ = eT.hom ≫ xᵢ.1 ≫ v i := by rw [hxv]
      _ = eT.hom ≫ (L'.one (tᵢ ≫ σ i)).1 := by rw [hone, hvone]
      _ = eT.hom ≫ (L'.one (τ ≫ t)).1 := by rw [one_val_congr L' hτt]
      _ = eT.hom ≫ (schemeHomOverComp τ rfl (L'.one t)).1 := by rw [one_natural L' t (τ ≫ t) τ rfl]
      _ = 𝒱.f i ≫ (L'.one t).1 := by simp only [schemeHomOverComp, τ, eT, Category.assoc, Iso.hom_inv_id_assoc]
  exact Subtype.ext (Scheme.Cover.hom_ext 𝒱 _ _ key)

end S_AlgebraicGeometry_Polarisation_kernelTrivial_of_forall_kernelTrivial_pullback_of_isPullback_pi_univ
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_kernelTrivial_of_forall_kernelTrivial_pullback_of_isPullback_pi_univ (solution)
