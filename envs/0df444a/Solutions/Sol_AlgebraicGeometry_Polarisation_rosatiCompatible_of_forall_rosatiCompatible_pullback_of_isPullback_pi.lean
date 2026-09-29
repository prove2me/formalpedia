-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.rosatiCompatible_of_forall_rosatiCompatible_pullback_of_isPullback_pi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/2edc217e-79dc-532f-bb17-1917e77d1559

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_of_forall_locIsoOnBase_pullback_of_isPullback_pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_rosatiCompatible_of_forall_rosatiCompatible_pullback_of_isPullback_pi

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

namespace ClopenC2

theorem mul_val_congr {R₀ : Type} [CommRing R₀] {B : Scheme.{0}} {b : B ⟶ Spec (CommRingCat.of R₀)} (G : RelativeGroupLaw R₀ b)
    {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R₀)} (h : t₁ = t₂)
    (P Q : SchemeHomOver t₁ b) (P' Q' : SchemeHomOver t₂ b) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (G.mul t₁ P Q).1 = (G.mul t₂ P' Q').1 := by
  subst h
  obtain ⟨p, hp⟩ := P; obtain ⟨p', hp'⟩ := P'; obtain ⟨q, hq⟩ := Q; obtain ⟨q', hq'⟩ := Q'
  simp only at hP hQ
  subst hP; subst hQ; rfl

theorem locIsoOnBase_congr {S' : Type} [CommRing S'] {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of S')) {M M' N N' : X.Modules}
    (eM : M ≅ N) (eM' : M' ≅ N') (h : LocIsoOnBase g M M') : LocIsoOnBase g N N' := by
  intro s
  obtain ⟨U, hs, ⟨e⟩⟩ := h s
  exact ⟨U, hs, ⟨((Scheme.Modules.pullback _).mapIso eM).symm ≪≫ e ≪≫ (Scheme.Modules.pullback _).mapIso eM'⟩⟩

end ClopenC2

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
    {I : Type} (act : I → (A' ⟶ A')) (act_over : ∀ x : I, act x ≫ f' = f') (star : I → I)
    (acti : ∀ i, I → (Ai i ⟶ Ai i)) (acti_over : ∀ (i : Fin k) (x : I), acti i x ≫ fi i = fi i)
    (hact : ∀ (i : Fin k) (x : I), acti i x ≫ v i = v i ≫ act x)
    (h : ∀ i, RosatiCompatible (fi i) (Li i) ((Scheme.Modules.pullback (v i)).obj 𝓛) (acti i) (acti_over i) star) :
    RosatiCompatible f' L' 𝓛 act act_over star := by
  classical
  intro b

  let vv : ∀ i, pullback (fi i) (fi i) ⟶ pullback f' f' := fun i =>
    pullback.lift (pullback.fst _ _ ≫ v i) (pullback.snd _ _ ≫ v i)
      (by rw [Category.assoc, Category.assoc, (hv i).w, ← Category.assoc, pullback.condition, Category.assoc])
  have hvv1 : ∀ i, vv i ≫ pullback.fst f' f' = pullback.fst _ _ ≫ v i := fun i => pullback.lift_fst _ _ _
  have hvv2 : ∀ i, vv i ≫ pullback.snd f' f' = pullback.snd _ _ ≫ v i := fun i => pullback.lift_snd _ _ _
  have hvv : ∀ i, IsPullback (vv i) (pullback.fst (fi i) (fi i) ≫ fi i) (pullback.fst f' f' ≫ f')
      (Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i))) := by
    intro i
    have outer : IsPullback (vv i ≫ pullback.snd f' f') (pullback.fst (fi i) (fi i)) f' (v i ≫ f') := by
      rw [hvv2, (hv i).w]
      exact IsPullback.paste_horiz (IsPullback.of_hasPullback (fi i) (fi i)).flip (hv i)
    have Q1 : IsPullback (vv i) (pullback.fst (fi i) (fi i)) (pullback.fst f' f') (v i) :=
      outer.of_right (hvv1 i) (IsPullback.of_hasPullback f' f').flip
    exact Q1.paste_vert (hv i)

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
    exact ClopenC2.mul_val_congr L' (by rw [pullback.lift_fst_assoc, Category.assoc, (hv i).w, Category.assoc]) _ _ _ _
      (by change vv i ≫ _ = _ ≫ _; rw [pullback.lift_fst]) (by change vv i ≫ _ = _ ≫ _; rw [pullback.lift_snd])
  have eΛ : ∀ i, Nonempty ((Scheme.Modules.pullback (vv i)).obj (mumfordBundle f' L' 𝓛) ≅
      mumfordBundle (fi i) (Li i) ((Scheme.Modules.pullback (v i)).obj 𝓛)) := by
    intro i
    obtain ⟨d⟩ := h𝓛.pullback_dual_monoidalV2 (v i)
    unfold mumfordBundle
    exact ⟨Scheme.Modules.pullbackTensorObjIso (vv i) _ _ ≪≫
      (((Scheme.Modules.pullbackComp (vv i) (addMor f' L')).app 𝓛 ≪≫ (Scheme.Modules.pullbackCongr (hadd i)).app 𝓛 ≪≫
          ((Scheme.Modules.pullbackComp (addMor (fi i) (Li i)) (v i)).app 𝓛).symm) ⊗ᵢ
        (Scheme.Modules.pullbackTensorObjIso (vv i) _ _ ≪≫
          (((Scheme.Modules.pullbackComp (vv i) (pullback.fst f' f')).app _ ≪≫
              (Scheme.Modules.pullbackCongr (hvv1 i)).app _ ≪≫
              ((Scheme.Modules.pullbackComp (pullback.fst (fi i) (fi i)) (v i)).app _).symm ≪≫
              (Scheme.Modules.pullback _).mapIso d) ⊗ᵢ
           ((Scheme.Modules.pullbackComp (vv i) (pullback.snd f' f')).app _ ≪≫
              (Scheme.Modules.pullbackCongr (hvv2 i)).app _ ≪≫
              ((Scheme.Modules.pullbackComp (pullback.snd (fi i) (fi i)) (v i)).app _).symm ≪≫
              (Scheme.Modules.pullback _).mapIso d))))⟩

  have hL : ∀ i, vv i ≫ pullback.lift (pullback.fst f' f') (pullback.snd f' f' ≫ act b)
      (by rw [Category.assoc, act_over]; exact pullback.condition) =
      pullback.lift (pullback.fst (fi i) (fi i)) (pullback.snd (fi i) (fi i) ≫ acti i b)
        (by rw [Category.assoc, acti_over]; exact pullback.condition) ≫ vv i := by
    intro i
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, hvv1, pullback.lift_fst_assoc]
    · simp only [Category.assoc, pullback.lift_snd, hvv2, pullback.lift_snd_assoc, hact]
      rw [← Category.assoc, hvv2, Category.assoc]
  have hR : ∀ i, vv i ≫ pullback.lift (pullback.fst f' f' ≫ act (star b)) (pullback.snd f' f')
      (by rw [Category.assoc, act_over]; exact pullback.condition) =
      pullback.lift (pullback.fst (fi i) (fi i) ≫ acti i (star b)) (pullback.snd (fi i) (fi i))
        (by rw [Category.assoc, acti_over]; exact pullback.condition) ≫ vv i := by
    intro i
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, hvv1, pullback.lift_fst_assoc, hact]
      rw [← Category.assoc, hvv1, Category.assoc]
    · simp only [Category.assoc, pullback.lift_snd, hvv2, pullback.lift_snd_assoc]

  refine AlgebraicGeometry.Polarisation.locIsoOnBase_of_forall_locIsoOnBase_pullback_of_isPullback_pi C _ _ _
    (fun i => pullback.fst (fi i) (fi i) ≫ fi i) vv hvv fun i => ?_
  obtain ⟨eΛ⟩ := eΛ i
  refine ClopenC2.locIsoOnBase_congr _ ?_ ?_ (h i b)
  · exact (Scheme.Modules.pullback _).mapIso eΛ.symm ≪≫ (Scheme.Modules.pullbackComp _ _).app _ ≪≫
      (Scheme.Modules.pullbackCongr (hL i).symm).app _ ≪≫ ((Scheme.Modules.pullbackComp _ _).app _).symm
  · exact (Scheme.Modules.pullback _).mapIso eΛ.symm ≪≫ (Scheme.Modules.pullbackComp _ _).app _ ≪≫
      (Scheme.Modules.pullbackCongr (hR i).symm).app _ ≪≫ ((Scheme.Modules.pullbackComp _ _).app _).symm

end S_AlgebraicGeometry_Polarisation_rosatiCompatible_of_forall_rosatiCompatible_pullback_of_isPullback_pi
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_rosatiCompatible_of_forall_rosatiCompatible_pullback_of_isPullback_pi (solution)
