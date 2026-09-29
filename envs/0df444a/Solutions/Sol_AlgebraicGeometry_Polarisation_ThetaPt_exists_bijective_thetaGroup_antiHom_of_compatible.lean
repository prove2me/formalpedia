-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.ThetaPt.exists_bijective_thetaGroup_antiHom_of_compatible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/981b83c8-c118-52b3-9597-6206f005e7b5

import Mathlib
import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_ThetaGroup
import Theorems.Thm_AlgebraicGeometry_Polarisation_ThetaPt_mul_act
import Theorems.Thm_AlgebraicGeometry_Polarisation_ThetaPt_act_add_and_act_baseScalar_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_ThetaPt_exists_bijective_thetaGroup_antiHom_of_compatible

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped commutatorElement

namespace B0E11

open TopologicalSpace Opposite

theorem Hom.comp_app_apply {X : Scheme.{0}} {M N P : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ P) (U : X.Opens)
    (x : Γ(M, U)) : (φ ≫ ψ).app U x = ψ.app U (φ.app U x) := rfl

theorem pullbackId_hom_app_app_pullbackLocalSection {X : Scheme.{0}} (M : X.Modules) (U : X.Opens) (s : Γ(M, U)) :
    ((Scheme.Modules.pullbackId X).hom.app M).app ((𝟙 X) ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection (𝟙 X) s) = s := by
  have h := unit_conjugateEquiv (CategoryTheory.Adjunction.id (C := X.Modules)) (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X))
    (Scheme.Modules.pullbackId X).hom M
  rw [Scheme.Modules.conjugateEquiv_pullbackId_hom] at h
  have h2 : (CategoryTheory.Adjunction.id.unit.app M ≫ (Scheme.Modules.pushforwardId X).inv.app ((𝟭 X.Modules).obj M)).app U s =
      ((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).unit.app M ≫
        (Scheme.Modules.pushforward (𝟙 X)).map ((Scheme.Modules.pullbackId X).hom.app M)).app U s := by
    rw [h]
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app] at h2
  change ((Scheme.Modules.pushforwardId X).inv.app ((𝟭 X.Modules).obj M)).app U ((CategoryTheory.Adjunction.id.unit.app M).app U s) =
    ((Scheme.Modules.pushforward (𝟙 X)).map ((Scheme.Modules.pullbackId X).hom.app M)).app U
      (((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).unit.app M).app U s) at h2
  rw [Scheme.Modules.pushforward_map_app, Scheme.Modules.pushforwardId_inv_app_app,
    ← Scheme.Modules.pullbackLocalSection_def] at h2
  exact h2.symm

theorem pullbackCongr_hom_app_top_pullbackLocalSection {X Y : Scheme.{0}} {a b : X ⟶ Y} (h : a = b)
    (M : Y.Modules) (s : Γ(M, ⊤)) :
    ((Scheme.Modules.pullbackCongr h).hom.app M).app ⊤
        (Scheme.Modules.pullbackLocalSection a s : Γ((Scheme.Modules.pullback a).obj M, ⊤)) =
      (Scheme.Modules.pullbackLocalSection b s : Γ((Scheme.Modules.pullback b).obj M, ⊤)) := by
  subst h
  simp [Scheme.Modules.pullbackCongr]

theorem pullbackId_hom_app_top_pullbackLocalSection {X : Scheme.{0}} (M : X.Modules) (s : Γ(M, ⊤)) :
    ((Scheme.Modules.pullbackId X).hom.app M).app ⊤
      (Scheme.Modules.pullbackLocalSection (𝟙 X) s : Γ((Scheme.Modules.pullback (𝟙 X)).obj M, ⊤)) = s :=
  pullbackId_hom_app_app_pullbackLocalSection M ⊤ s

variable {X : Scheme.{0}} (M : X.Modules)

noncomputable def actOf (a : X ⟶ X) (φ : (Scheme.Modules.pullback a).obj M ≅ M) (s : Γ(M, ⊤)) : Γ(M, ⊤) :=
  (φ.hom.app (a ⁻¹ᵁ ⊤) (Scheme.Modules.pullbackLocalSection a s) : Γ(M, a ⁻¹ᵁ ⊤))

theorem actOf_eq (a : X ⟶ X) (φ : (Scheme.Modules.pullback a).obj M ≅ M) (s : Γ(M, ⊤)) :
    actOf M a φ s = φ.hom.app ⊤ (Scheme.Modules.pullbackLocalSection a s : Γ((Scheme.Modules.pullback a).obj M, ⊤)) := rfl

theorem actOf_reflIso_trans (e : X ≅ X) (h : e.hom = 𝟙 X) (α : M ≅ M) (s : Γ(M, ⊤)) :
    actOf M e.hom (Scheme.Modules.fibration.reflIso M e h ≪≫ α) s = α.hom.app ⊤ s := by
  rw [actOf_eq]
  simp only [Scheme.Modules.fibration.reflIso, Iso.trans_hom, Iso.app_hom, Category.assoc]
  change α.hom.app ⊤ ((((Scheme.Modules.pullbackId X).hom.app M).app ⊤
    ((((Scheme.Modules.pullbackCongr h).hom.app M).app ⊤
      (Scheme.Modules.pullbackLocalSection e.hom s : Γ((Scheme.Modules.pullback e.hom).obj M, ⊤)))))) = _
  rw [pullbackCongr_hom_app_top_pullbackLocalSection h, pullbackId_hom_app_top_pullbackLocalSection]

theorem actOf_reflIso (e : X ≅ X) (h : e.hom = 𝟙 X) (s : Γ(M, ⊤)) :
    actOf M e.hom (Scheme.Modules.fibration.reflIso M e h) s = s := by
  have := actOf_reflIso_trans M e h (Iso.refl M) s
  rw [Iso.trans_refl] at this
  exact this

theorem unitReading_autOfIso (e : X ≅ X) (φ : (Scheme.Modules.pullback e.hom).obj M ≅ M)
    (h : (Scheme.Modules.fibration.autOfIso M e φ).hom.base = 𝟙 X) :
    RiemannForm.thetaGroup.unitReading M h = φ.inv ≫ (Scheme.Modules.fibration.reflIso M e h).hom := by
  rfl

theorem eq_smul_actOf_of_unitReading_eq (e : X ≅ X) (φ : (Scheme.Modules.pullback e.hom).obj M ≅ M)
    (h : (Scheme.Modules.fibration.autOfIso M e φ).hom.base = 𝟙 X) (r : Γ(X, ⊤))
    (hr : ∀ (U : X.Opens) (x : Γ(M, U)),
      (RiemannForm.thetaGroup.unitReading M h).app U x = Scheme.Modules.topRes r U • x)
    (s : Γ(M, ⊤)) : s = r • actOf M e.hom φ s := by
  have h1 := hr ⊤ (actOf M e.hom φ s)
  rw [Scheme.Modules.topRes_top] at h1
  have h2 : (RiemannForm.thetaGroup.unitReading M h).app ⊤ (actOf M e.hom φ s) = s := by
    change (φ.hom ≫ (φ.inv ≫ (Scheme.Modules.fibration.reflIso M e h).hom)).app ⊤
      (Scheme.Modules.pullbackLocalSection e.hom s : Γ((Scheme.Modules.pullback e.hom).obj M, ⊤)) = s
    rw [Iso.hom_inv_id_assoc]
    exact actOf_reflIso M e h s
  exact h2.symm.trans h1

end B0E11

namespace B0Fib

p2m_open "CategoryTheory.Pseudofunctor.CoGrothendieck"

theorem isSplitMono_of_comp_eq {C : Type*} [Category C] {X Y Z : C} (f : X ⟶ Y) (r : Y ⟶ Z) (i : X ⟶ Z) (hi : IsIso i)
    (h : f ≫ r = i) : IsSplitMono f :=
  IsSplitMono.mk' ⟨r ≫ inv i, by rw [← Category.assoc, h, IsIso.hom_inv_id]⟩

theorem isIso_of_comp_eq {C : Type*} [Category C] {X Y Z : C} (f : X ⟶ Y) (r : Y ⟶ Z) (i : X ⟶ Z) (hi : IsIso i) (hr : Mono r)
    (h : f ≫ r = i) : IsIso f := by
  have h1 : f ≫ (r ≫ inv i) = 𝟙 _ := by rw [← Category.assoc, h, IsIso.hom_inv_id]
  haveI : Mono (r ≫ inv i) := mono_comp _ _
  have h2 : (r ≫ inv i) ≫ f = 𝟙 _ := by
    rw [← cancel_mono (r ≫ inv i), Category.assoc, h1, Category.comp_id, Category.id_comp]
  exact ⟨⟨r ≫ inv i, h1, h2⟩⟩

theorem isIso_mapId_inv_app (X : Pseudofunctor.CoGrothendieck Scheme.Modules.fibration) :
    IsIso ((Scheme.Modules.fibration.mapId ⟨Opposite.op X.base⟩).inv.toNatTrans.app X.fiber) := by
  refine ⟨⟨(Scheme.Modules.fibration.mapId ⟨Opposite.op X.base⟩).hom.toNatTrans.app X.fiber, ?_, ?_⟩⟩
  · rw [← Cat.Hom₂.comp_app, Iso.inv_hom_id, Cat.Hom₂.id_app]
  · rw [← Cat.Hom₂.comp_app, Iso.hom_inv_id, Cat.Hom₂.id_app]

theorem mono_mapComp_inv_app {X Y Z : Pseudofunctor.CoGrothendieck Scheme.Modules.fibration} (a : X ⟶ Y) (b : Y ⟶ Z) :
    IsIso ((Scheme.Modules.fibration.mapComp b.base.op.toLoc a.base.op.toLoc).inv.toNatTrans.app Z.fiber) := by
  refine ⟨⟨(Scheme.Modules.fibration.mapComp b.base.op.toLoc a.base.op.toLoc).hom.toNatTrans.app Z.fiber, ?_, ?_⟩⟩
  · rw [← Cat.Hom₂.comp_app, Iso.inv_hom_id, Cat.Hom₂.id_app]
  · rw [← Cat.Hom₂.comp_app, Iso.hom_inv_id, Cat.Hom₂.id_app]

theorem isSplitMono_fiber {X Y : Pseudofunctor.CoGrothendieck Scheme.Modules.fibration} (g : X ≅ Y) :
    IsSplitMono g.hom.fiber := by
  have e1 := Hom.congr g.hom_inv_id
  simp only [categoryStruct_comp_fiber, categoryStruct_id_fiber] at e1
  obtain ⟨p, e1'⟩ : ∃ p : (Scheme.Modules.fibration.map (Hom.base (𝟙 X)).op.toLoc).toFunctor.obj X.fiber =
      (Scheme.Modules.fibration.map (g.inv.base.op.toLoc ≫ g.hom.base.op.toLoc)).toFunctor.obj X.fiber,
      g.hom.fiber ≫ (Scheme.Modules.fibration.map g.hom.base.op.toLoc).toFunctor.map g.inv.fiber ≫
        (Scheme.Modules.fibration.mapComp g.inv.base.op.toLoc g.hom.base.op.toLoc).inv.toNatTrans.app X.fiber =
      (Scheme.Modules.fibration.mapId ⟨Opposite.op X.base⟩).inv.toNatTrans.app X.fiber ≫ eqToHom p := ⟨_, e1⟩
  refine isSplitMono_of_comp_eq _ _ _ ?_ e1'
  exact IsIso.comp_isIso' (isIso_mapId_inv_app X) (Iso.isIso_hom (eqToIso p))

theorem isIso_fiber {X Y : Pseudofunctor.CoGrothendieck Scheme.Modules.fibration} (g : X ≅ Y) :
    IsIso g.hom.fiber := by
  have e1 := Hom.congr g.hom_inv_id
  simp only [categoryStruct_comp_fiber, categoryStruct_id_fiber] at e1
  haveI : IsSplitMono g.inv.fiber := isSplitMono_fiber g.symm
  have m1 : Mono ((Scheme.Modules.fibration.map g.hom.base.op.toLoc).toFunctor.map g.inv.fiber) := inferInstance
  have m2 : Mono ((Scheme.Modules.fibration.mapComp g.inv.base.op.toLoc g.hom.base.op.toLoc).inv.toNatTrans.app X.fiber) :=
    @IsIso.mono_of_iso _ _ _ _ _ (mono_mapComp_inv_app g.hom g.inv)
  obtain ⟨p, e1'⟩ : ∃ p : (Scheme.Modules.fibration.map (Hom.base (𝟙 X)).op.toLoc).toFunctor.obj X.fiber =
      (Scheme.Modules.fibration.map (g.inv.base.op.toLoc ≫ g.hom.base.op.toLoc)).toFunctor.obj X.fiber,
      g.hom.fiber ≫ (Scheme.Modules.fibration.map g.hom.base.op.toLoc).toFunctor.map g.inv.fiber ≫
        (Scheme.Modules.fibration.mapComp g.inv.base.op.toLoc g.hom.base.op.toLoc).inv.toNatTrans.app X.fiber =
      (Scheme.Modules.fibration.mapId ⟨Opposite.op X.base⟩).inv.toNatTrans.app X.fiber ≫ eqToHom p := ⟨_, e1⟩
  refine isIso_of_comp_eq _ _ _ ?_ (mono_comp' m1 m2) e1'
  exact IsIso.comp_isIso' (isIso_mapId_inv_app X) (Iso.isIso_hom (eqToIso p))

end B0Fib

namespace B0

variable {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
  (𝓛 : A.Modules) {K : Type} [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of S))
  (L' : RelativeGroupLaw K (pullback.snd f t)) (hc' : L'.IsCommutative)

def Compat : Prop :=
  ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t' (pullback.snd f t)),
      (L'.mul t' P Q).1 ≫ pullback.fst f t =
        (L.mul (t' ≫ t)
          ⟨P.1 ≫ pullback.fst f t, by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ pullback.fst f t, by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1

noncomputable abbrev MK : (pullback f t).Modules := (Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛

abbrev TG : Type _ := RiemannForm.thetaGroup (pullback.snd f t) L' hc' (MK f 𝓛 t)

noncomputable def ptK (x : SchemeHomOver t f) : RiemannForm.Pt (pullback.snd f t) :=
  ⟨pullback.lift x.1 (𝟙 _) (by rw [Category.id_comp]; exact x.2),
    by rw [pullback.lift_snd, RiemannForm.specMap_algebraMap_self]⟩

@[scoped simp] theorem ptK_coe (x : SchemeHomOver t f) :
    (ptK f t x).1 = pullback.lift x.1 (𝟙 _) (by rw [Category.id_comp]; exact x.2) := rfl

theorem ptK_fst (x : SchemeHomOver t f) : (ptK f t x).1 ≫ pullback.fst f t = x.1 := pullback.lift_fst _ _ _

theorem ptK_snd (x : SchemeHomOver t f) : (ptK f t x).1 ≫ pullback.snd f t = 𝟙 _ := pullback.lift_snd _ _ _

theorem translate_eq_translation (hL' : Compat f L t L') (x : SchemeHomOver t f) :
    Polarisation.translate f L t x = RiemannForm.translation (pullback.snd f t) L' (ptK f t x) := by
  apply pullback.hom_ext
  · rw [translate_fst]
    unfold RiemannForm.translation
    rw [hL']
    have h1 : (⟨(RelativeGroupLaw.idPoint (f := pullback.snd f t)).1 ≫ pullback.fst f t, by
          rw [Category.assoc, pullback.condition, ← Category.assoc, (RelativeGroupLaw.idPoint (f := pullback.snd f t)).2]⟩ :
          SchemeHomOver (pullback.snd f t ≫ t) f) = prPt f t := by
      apply Subtype.ext
      show (RelativeGroupLaw.idPoint (f := pullback.snd f t)).1 ≫ pullback.fst f t = pullback.fst f t
      exact Category.id_comp _
    have h2 : (⟨(RiemannForm.constPt (pullback.snd f t) (ptK f t x)).1 ≫ pullback.fst f t, by
          rw [Category.assoc, pullback.condition, ← Category.assoc, (RiemannForm.constPt (pullback.snd f t) (ptK f t x)).2]⟩ :
          SchemeHomOver (pullback.snd f t ≫ t) f) = constPtR f t x := by
      apply Subtype.ext
      show (pullback.snd f t ≫ (ptK f t x).1) ≫ pullback.fst f t = (constPtR f t x).1
      rw [constPtR_coe, Category.assoc, ptK_fst]
    rw [h1, h2]
  · rw [translate_snd]
    exact (L'.mul (pullback.snd f t) RelativeGroupLaw.idPoint (RiemannForm.constPt (pullback.snd f t) (ptK f t x))).2.symm

noncomputable def Φ (hL' : Compat f L t L') (θ : ThetaPt f L 𝓛 t) : TG f 𝓛 t L' hc' :=
  ⟨(ThetaPt.toAut θ, Multiplicative.ofAdd (RelativeGroupLaw.AlgPoints.ofPoint (ptK f t θ.pt))), by
    show (ThetaPt.toAut θ).hom.base = RiemannForm.translation (pullback.snd f t) L'
      (RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd (Multiplicative.ofAdd
        (RelativeGroupLaw.AlgPoints.ofPoint (L := L') (hc := hc') (ptK f t θ.pt)))))
    rw [toAdd_ofAdd, RelativeGroupLaw.AlgPoints.toPoint_ofPoint, ← translate_eq_translation f L t L' hL']
    exact Scheme.Modules.fibration.autOfIso_hom_base _ _ _⟩

variable (hL' : Compat f L t L')

theorem Φ_fst (θ : ThetaPt f L 𝓛 t) : (Φ f L 𝓛 t L' hc' hL' θ).1.1 = ThetaPt.toAut θ := rfl

theorem Φ_snd (θ : ThetaPt f L 𝓛 t) :
    (Φ f L 𝓛 t L' hc' hL' θ).1.2 = Multiplicative.ofAdd (RelativeGroupLaw.AlgPoints.ofPoint (ptK f t θ.pt)) := rfl

theorem pt_Φ (θ : ThetaPt f L 𝓛 t) :
    RiemannForm.thetaGroup.pt (pullback.snd f t) L' hc' _ (Φ f L 𝓛 t L' hc' hL' θ) =
      Multiplicative.ofAdd (RelativeGroupLaw.AlgPoints.ofPoint (ptK f t θ.pt)) := rfl

theorem clause_pt (θ : ThetaPt f L 𝓛 t) :
    (RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd
      (RiemannForm.thetaGroup.pt (pullback.snd f t) L' hc' _ (Φ f L 𝓛 t L' hc' hL' θ)))).1 ≫
        pullback.fst f t = θ.pt.1 :=
  ptK_fst f t θ.pt

theorem clause_mul (θ θ' : ThetaPt f L 𝓛 t) :
    Φ f L 𝓛 t L' hc' hL' (θ * θ') = Φ f L 𝓛 t L' hc' hL' θ' * Φ f L 𝓛 t L' hc' hL' θ := by
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · show ThetaPt.toAut (θ * θ') = ThetaPt.toAut θ' * ThetaPt.toAut θ
    rw [ThetaPt.toAut_mul, Aut.Aut_mul_def]
  · show Multiplicative.ofAdd (RelativeGroupLaw.AlgPoints.ofPoint (L := L') (hc := hc') (ptK f t (θ * θ').pt)) =
      Multiplicative.ofAdd (RelativeGroupLaw.AlgPoints.ofPoint (L := L') (hc := hc') (ptK f t θ'.pt)) *
      Multiplicative.ofAdd (RelativeGroupLaw.AlgPoints.ofPoint (L := L') (hc := hc') (ptK f t θ.pt))
    rw [← ofAdd_add]
    congr 1
    apply RelativeGroupLaw.AlgPoints.toPoint_injective
    rw [RelativeGroupLaw.AlgPoints.toPoint_ofPoint, RelativeGroupLaw.AlgPoints.toPoint_add,
      RelativeGroupLaw.AlgPoints.toPoint_ofPoint, RelativeGroupLaw.AlgPoints.toPoint_ofPoint]

    rw [hc']
    apply Subtype.ext
    apply pullback.hom_ext
    · rw [hL', ptK_fst]
      show (L.mul t θ.pt θ'.pt).1 = _
      have key : ∀ {t₁ t₂ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of S)} (h : t₁ = t₂)
          (a b : SchemeHomOver t₁ f) (a' b' : SchemeHomOver t₂ f), a.1 = a'.1 → b.1 = b'.1 →
          (L.mul t₁ a b).1 = (L.mul t₂ a' b').1 := by
        intro t₁ t₂ h a b a' b' ha hb; subst h; cases Subtype.ext ha; cases Subtype.ext hb; rfl
      refine key ?_ _ _ _ _ (ptK_fst f t θ.pt).symm (ptK_fst f t θ'.pt).symm
      rw [RiemannForm.specMap_algebraMap_self, Category.id_comp]
    · rw [ptK_snd, (L'.mul _ (ptK f t θ.pt) (ptK f t θ'.pt)).2, RiemannForm.specMap_algebraMap_self]

theorem clause_one : Φ f L 𝓛 t L' hc' hL' 1 = 1 := by
  have h := clause_mul f L 𝓛 t L' hc' hL' 1 1
  rw [mul_one] at h

  exact (mul_eq_left.mp h.symm)

theorem Φ_injective : Function.Injective (Φ f L 𝓛 t L' hc' hL') := by
  intro θ θ' h
  apply ThetaPt.toGrp_injective
  refine Prod.ext ?_ ?_
  · show MulOpposite.op (ThetaPt.toAut θ) = MulOpposite.op (ThetaPt.toAut θ')
    rw [← Φ_fst f L 𝓛 t L' hc' hL' θ, ← Φ_fst f L 𝓛 t L' hc' hL' θ', h]
  · have e1 := clause_pt f L 𝓛 t L' hc' hL' θ
    have e2 := clause_pt f L 𝓛 t L' hc' hL' θ'
    rw [h] at e1
    exact Subtype.ext (e1.symm.trans e2)

noncomputable def ofPtK (P : RiemannForm.Pt (pullback.snd f t)) : SchemeHomOver t f :=
  ⟨P.1 ≫ pullback.fst f t, by
    rw [Category.assoc, pullback.condition, ← Category.assoc, P.2, RiemannForm.specMap_algebraMap_self,
      Category.id_comp]⟩

theorem ptK_ofPtK (P : RiemannForm.Pt (pullback.snd f t)) : ptK f t (ofPtK f t P) = P := by
  apply Subtype.ext
  apply pullback.hom_ext
  · rw [ptK_fst]; rfl
  · rw [ptK_snd, P.2, RiemannForm.specMap_algebraMap_self]

theorem Φ_surjective : Function.Surjective (Φ f L 𝓛 t L' hc' hL') := by
  rintro ⟨⟨a, m⟩, ha⟩
  change a.hom.base = RiemannForm.translation (pullback.snd f t) L'
    (RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd m)) at ha
  set P : RiemannForm.Pt (pullback.snd f t) := RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd m) with hP
  have hb : translate f L t (ofPtK f t P) = a.hom.base := by
    rw [translate_eq_translation f L t L' hL', ptK_ofPtK, ha]
  have hI : IsIso a.hom.fiber := B0Fib.isIso_fiber a
  let e : MK f 𝓛 t ≅ (Scheme.Modules.pullback a.hom.base).obj (MK f 𝓛 t) := @asIso _ _ _ _ a.hom.fiber hI
  let ψ : (Scheme.Modules.pullback (translate f L t (ofPtK f t P))).obj (MK f 𝓛 t) ≅ MK f 𝓛 t :=
    (Scheme.Modules.pullbackCongr hb).app _ ≪≫ e.symm
  refine ⟨⟨ofPtK f t P, ψ⟩, ?_⟩
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · show ThetaPt.toAut (⟨ofPtK f t P, ψ⟩ : ThetaPt f L 𝓛 t) = a
    apply Iso.ext
    refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ hb ?_
    show ψ.inv = a.hom.fiber ≫ eqToHom _
    simp only [ψ, e, Iso.trans_inv, Iso.symm_inv, asIso_hom, Iso.app_inv,
      Scheme.Modules.fibration.pullbackCongr_inv_app_eq_eqToHom]
    rfl
  · show Multiplicative.ofAdd (RelativeGroupLaw.AlgPoints.ofPoint (L := L') (hc := hc') (ptK f t (ofPtK f t P))) = m
    rw [ptK_ofPtK]
    rfl

theorem baseScalar_eq (c : K) :
    baseScalar f t c = (pullback.snd f t).appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c) := rfl

theorem eq_smul_act_of_isScalarElt (κ : ThetaPt f L 𝓛 t) (c : K)
    (h : RiemannForm.thetaGroup.IsScalarElt (pullback.snd f t) L' hc' _ (Φ f L 𝓛 t L' hc' hL' κ) c)
    (s : Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, ⊤)) :
    s = baseScalar f t c • κ.act s := by
  obtain ⟨hpt, hcs⟩ := h

  exact B0E11.eq_smul_actOf_of_unitReading_eq _ (translateIso f L t κ.pt) κ.iso
    (RiemannForm.thetaGroup.base_eq_id_of_pt_eq_one (pullback.snd f t) L' hc' _ _ hpt) (baseScalar f t c) hcs s

theorem Φ_inv (θ : ThetaPt f L 𝓛 t) : Φ f L 𝓛 t L' hc' hL' θ⁻¹ = (Φ f L 𝓛 t L' hc' hL' θ)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← clause_mul, mul_inv_cancel, clause_one]

theorem commutator_Φ (θ θ' : ThetaPt f L 𝓛 t) :
    ⁅Φ f L 𝓛 t L' hc' hL' θ, Φ f L 𝓛 t L' hc' hL' θ'⁆ = Φ f L 𝓛 t L' hc' hL' (θ'⁻¹ * θ⁻¹ * θ' * θ) := by
  rw [commutatorElement_def, clause_mul, clause_mul, clause_mul, Φ_inv, Φ_inv, mul_assoc, mul_assoc]

theorem clause_comm (θ θ' : ThetaPt f L 𝓛 t) (c : K)
    (h : RiemannForm.thetaGroup.IsScalarElt (pullback.snd f t) L' hc' _
      ⁅Φ f L 𝓛 t L' hc' hL' θ, Φ f L 𝓛 t L' hc' hL' θ'⁆ c)
    (s : Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, ⊤)) :
    θ.act (θ'.act s) = baseScalar f t c • θ'.act (θ.act s) := by
  rw [commutator_Φ] at h
  have hκ := eq_smul_act_of_isScalarElt f L 𝓛 t L' hc' hL' (θ'⁻¹ * θ⁻¹ * θ' * θ) c h s
  have hgrp : θ * θ' * (θ'⁻¹ * θ⁻¹ * θ' * θ) = θ' * θ := by group
  conv_lhs => rw [hκ]
  rw [← ThetaPt.mul_act θ θ', (ThetaPt.act_add_and_act_baseScalar_smul f L 𝓛 t (θ * θ')).2,
    ← ThetaPt.mul_act, hgrp, ThetaPt.mul_act]

theorem unitReading_ofUnit (u : Γ(pullback f t, ⊤)ˣ)
    (h : (ThetaPt.toAut (ThetaPt.ofUnit u : ThetaPt f L 𝓛 t)).hom.base = 𝟙 _) :
    RiemannForm.thetaGroup.unitReading (MK f 𝓛 t) h =
      Scheme.Modules.homothety (MK f 𝓛 t) ((u⁻¹ : Γ(pullback f t, ⊤)ˣ) : Γ(pullback f t, ⊤)) := by
  change (ThetaPt.ofUnit u : ThetaPt f L 𝓛 t).iso.inv ≫
      (Scheme.Modules.fibration.reflIso (MK f 𝓛 t) (translateIso f L t (L.one t)) h).hom = _
  rw [ThetaPt.ofUnit_iso]
  change ((Scheme.Modules.fibration.reflIso (MK f 𝓛 t) (translateIso f L t (L.one t)) (translate_one f L t)) ≪≫
      Scheme.Modules.homothetyIso _ u).inv ≫
      (Scheme.Modules.fibration.reflIso (MK f 𝓛 t) (translateIso f L t (L.one t)) h).hom = _
  rw [Iso.trans_inv, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

theorem clause_scalar (c : Kˣ) :
    RiemannForm.thetaGroup.IsScalarElt (pullback.snd f t) L' hc' _
      (Φ f L 𝓛 t L' hc' hL' (ThetaPt.ofScalar c)) ((c⁻¹ : Kˣ) : K) := by
  have hpt : RiemannForm.thetaGroup.pt (pullback.snd f t) L' hc' _ (Φ f L 𝓛 t L' hc' hL' (ThetaPt.ofScalar c)) = 1 := by
    have e : RiemannForm.thetaGroup.pt (pullback.snd f t) L' hc' _ (Φ f L 𝓛 t L' hc' hL' (ThetaPt.ofScalar c)) =
        RiemannForm.thetaGroup.pt (pullback.snd f t) L' hc' _ (Φ f L 𝓛 t L' hc' hL' 1) := rfl
    rw [e, clause_one, map_one]
  refine ⟨hpt, ?_⟩
  intro U x
  have hu : RiemannForm.thetaGroup.unitReading _
      (RiemannForm.thetaGroup.base_eq_id_of_pt_eq_one (pullback.snd f t) L' hc' _
        (Φ f L 𝓛 t L' hc' hL' (ThetaPt.ofScalar c)) hpt) =
      Scheme.Modules.homothety _ ((((Units.map (baseScalarHom f t).toMonoidHom c)⁻¹ : Γ(pullback f t, ⊤)ˣ)) :
        Γ(pullback f t, ⊤)) :=
    unitReading_ofUnit f L 𝓛 t (Units.map (baseScalarHom f t).toMonoidHom c) _
  have hcoe : ((((Units.map (baseScalarHom f t).toMonoidHom c)⁻¹ : Γ(pullback f t, ⊤)ˣ)) : Γ(pullback f t, ⊤)) =
      baseScalar f t ((c⁻¹ : Kˣ) : K) := by
    rw [← map_inv, Units.coe_map]; rfl
  rw [hu, Scheme.Modules.homothety_app, hcoe]
  rfl

end B0
p2m_reactivate "P2MW.S_AlgebraicGeometry_Polarisation_ThetaPt_exists_bijective_thetaGroup_antiHom_of_compatible.B0"

theorem solution
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (𝓛 : A.Modules)
    {K : Type} [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of S))
    (L' : RelativeGroupLaw K (pullback.snd f t)) (hc' : L'.IsCommutative)
    (hL' : ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t' (pullback.snd f t)),
      (L'.mul t' P Q).1 ≫ pullback.fst f t =
        (L.mul (t' ≫ t)
          ⟨P.1 ≫ pullback.fst f t, by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ pullback.fst f t, by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) :
    ∃ Φ : ThetaPt f L 𝓛 t →
        RiemannForm.thetaGroup (pullback.snd f t) L' hc'
          ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛),
      Function.Bijective Φ ∧ Φ 1 = 1 ∧ (∀ θ θ' : ThetaPt f L 𝓛 t, Φ (θ * θ') = Φ θ' * Φ θ) ∧
      (∀ θ : ThetaPt f L 𝓛 t,
        (RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd
          (RiemannForm.thetaGroup.pt (pullback.snd f t) L' hc' _ (Φ θ)))).1 ≫
            pullback.fst f t = θ.pt.1) ∧
      (∀ (θ θ' : ThetaPt f L 𝓛 t) (c : K),
        RiemannForm.thetaGroup.IsScalarElt (pullback.snd f t) L' hc' _ ⁅Φ θ, Φ θ'⁆ c →
          ∀ s : Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, ⊤),
            θ.act (θ'.act s) = baseScalar f t c • θ'.act (θ.act s)) ∧
      (∀ c : Kˣ, RiemannForm.thetaGroup.IsScalarElt (pullback.snd f t) L' hc' _
          (Φ (ThetaPt.ofScalar c)) ((c⁻¹ : Kˣ) : K)) :=
  ⟨B0.Φ f L 𝓛 t L' hc' hL',
    ⟨B0.Φ_injective f L 𝓛 t L' hc' hL', B0.Φ_surjective f L 𝓛 t L' hc' hL'⟩,
    B0.clause_one f L 𝓛 t L' hc' hL', B0.clause_mul f L 𝓛 t L' hc' hL', B0.clause_pt f L 𝓛 t L' hc' hL',
    B0.clause_comm f L 𝓛 t L' hc' hL', B0.clause_scalar f L 𝓛 t L' hc' hL'⟩

end S_AlgebraicGeometry_Polarisation_ThetaPt_exists_bijective_thetaGroup_antiHom_of_compatible
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_ThetaPt_exists_bijective_thetaGroup_antiHom_of_compatible (solution)
