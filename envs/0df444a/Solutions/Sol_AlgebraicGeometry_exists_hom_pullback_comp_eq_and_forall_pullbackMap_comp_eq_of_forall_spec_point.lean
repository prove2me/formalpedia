-- Prove2me | solution 1 for AlgebraicGeometry.exists_hom_pullback_comp_eq_and_forall_pullbackMap_comp_eq_of_forall_spec_point
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/3911fe98-2094-5408-8aa5-e56f8db2566e

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_hom_pullback_comp_eq_and_forall_pullbackMap_comp_eq_of_forall_spec_point

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace UnivMor

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc pullback.lift_snd_assoc

variable {X Y B : Scheme.{u}} (f : X ⟶ B)

theorem map_map {W₁ W₂ W₃ : Scheme.{u}} (t₁ : W₁ ⟶ B) (t₂ : W₂ ⟶ B) (t₃ : W₃ ⟶ B)
    (c : W₁ ⟶ W₂) (d : W₂ ⟶ W₃)
    (h₁ : t₁ ≫ 𝟙 B = c ≫ t₂) (h₂ : t₂ ≫ 𝟙 B = d ≫ t₃) (h₃ : t₁ ≫ 𝟙 B = (c ≫ d) ≫ t₃) :
    pullback.map f t₁ f t₂ (𝟙 X) c (𝟙 B) (by rw [Category.comp_id, Category.id_comp]) h₁ ≫
      pullback.map f t₂ f t₃ (𝟙 X) d (𝟙 B) (by rw [Category.comp_id, Category.id_comp]) h₂ =
      pullback.map f t₁ f t₃ (𝟙 X) (c ≫ d) (𝟙 B) (by rw [Category.comp_id, Category.id_comp]) h₃ := by
  apply pullback.hom_ext <;> simp [pullback.map]

theorem map_eq_lift {W₁ W₂ : Scheme.{u}} (t₁ : W₁ ⟶ B) (t₂ : W₂ ⟶ B) (d : W₁ ⟶ W₂)
    (h : t₁ ≫ 𝟙 B = d ≫ t₂) (h' : pullback.fst f t₁ ≫ f = (pullback.snd f t₁ ≫ d) ≫ t₂) :
    pullback.map f t₁ f t₂ (𝟙 X) d (𝟙 B) (by rw [Category.comp_id, Category.id_comp]) h =
      pullback.lift (pullback.fst f t₁) (pullback.snd f t₁ ≫ d) h' := by
  apply pullback.hom_ext <;> simp [pullback.map]

theorem isPullback_map {W W' : Scheme.{u}} (t : W ⟶ B) (d : W' ⟶ W) (t' : W' ⟶ B) (hd : t' = d ≫ t)
    (h : t' ≫ 𝟙 B = d ≫ t) :
    IsPullback (pullback.map f t' f t (𝟙 X) d (𝟙 B) (by rw [Category.comp_id, Category.id_comp]) h)
      (pullback.snd f t') (pullback.snd f t) d := by
  refine IsPullback.of_right ?_ (by simp [pullback.map]) (IsPullback.of_hasPullback f t)
  have e : pullback.map f t' f t (𝟙 X) d (𝟙 B) (by rw [Category.comp_id, Category.id_comp]) h ≫ pullback.fst f t =
      pullback.fst f t' := by simp [pullback.map]
  rw [e, ← hd]
  exact IsPullback.of_hasPullback f t'

end UnivMor

open UnivMor

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc pullback.lift_snd_assoc

set_option backward.defeqAttrib.useBackward true in
theorem solution
    (S : Type u) [CommRing S] {X Y M : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ Spec (CommRingCat.of S)) (πM : M ⟶ Spec (CommRingCat.of S))
    (pt : ∀ (S' : Type u) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
        (φ : pullback f s ⟶ Y), φ ≫ g = pullback.snd f s ≫ s → SchemeHomOver s πM)

    (hnat : ∀ (S' S'' : Type u) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
          (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
          (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
          (φ : pullback f s ⟶ Y) (hφ : φ ≫ g = pullback.snd f s ≫ s),
        (pt S'' s''
            (pullback.lift (pullback.fst f s'') (pullback.snd f s'' ≫ Spec.map (CommRingCat.ofHom ψ))
                (by rw [Category.assoc, hs]; exact pullback.condition) ≫ φ)
            (by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd, Category.assoc, hs])).1 =
          Spec.map (CommRingCat.ofHom ψ) ≫ (pt S' s φ hφ).1)

    (hsurj : ∀ (S' : Type u) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver s πM),
        ∃ (φ : pullback f s ⟶ Y) (hφ : φ ≫ g = pullback.snd f s ≫ s), pt S' s φ hφ = x)

    (hinj : ∀ (S' : Type u) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
          (φ φ' : pullback f s ⟶ Y) (hφ : φ ≫ g = pullback.snd f s ≫ s) (hφ' : φ' ≫ g = pullback.snd f s ≫ s),
        pt S' s φ hφ = pt S' s φ' hφ' → φ = φ') :
    ∃ Φ : pullback f πM ⟶ Y, Φ ≫ g = pullback.snd f πM ≫ πM ∧
      ∀ (S' : Type u) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
        (φ : pullback f s ⟶ Y) (hφ : φ ≫ g = pullback.snd f s ≫ s),
        pullback.map f s f πM (𝟙 X) (pt S' s φ hφ).1 (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, (pt S' s φ hφ).2]) ≫ Φ = φ := by
  classical

  have ptcongr : ∀ (S' : Type u) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
      (φ φ' : pullback f s ⟶ Y) (hφ : φ ≫ g = pullback.snd f s ≫ s) (hφ' : φ' ≫ g = pullback.snd f s ≫ s),
      φ = φ' → pt S' s φ hφ = pt S' s φ' hφ' := by
    rintro S' _ s φ φ' hφ hφ' rfl; rfl

  have hres : ∀ {W W' : Scheme.{u}} (t : W ⟶ Spec (CommRingCat.of S)) (t' : W' ⟶ Spec (CommRingCat.of S)) (d : W' ⟶ W)
      (h : t' ≫ 𝟙 _ = d ≫ t) (a : pullback f t ⟶ Y), a ≫ g = pullback.snd f t ≫ t →
      (pullback.map f t' f t (𝟙 X) d (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) h ≫ a) ≫ g = pullback.snd f t' ≫ t' := by
    intro W W' t t' d h a ha
    rw [Category.assoc, ha, ← Category.assoc, pullback.map, pullback.lift_snd, Category.assoc, ← h, Category.comp_id]

  have P0 : ∀ (S₀ : Type u) [CommRing S₀] (s₀ : Spec (CommRingCat.of S₀) ⟶ Spec (CommRingCat.of S))
      (φ₀ : pullback f s₀ ⟶ Y) (hφ₀ : φ₀ ≫ g = pullback.snd f s₀ ≫ s₀)
      (C : Type u) [CommRing C] (t : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of S))
      (d : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of S₀)) (hd : t ≫ 𝟙 _ = d ≫ s₀),
      (pt C t (pullback.map f t f s₀ (𝟙 X) d (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) hd ≫ φ₀)
        (hres s₀ t d hd φ₀ hφ₀)).1 = d ≫ (pt S₀ s₀ φ₀ hφ₀).1 := by
    intro S₀ _ s₀ φ₀ hφ₀ C _ t d hd
    obtain ⟨ψ, hψ⟩ : ∃ ψ : S₀ →+* C, Spec.map (CommRingCat.ofHom ψ) = d :=
      ⟨(Spec.preimage d).hom, Spec.map_preimage d⟩
    subst hψ
    have hs : Spec.map (CommRingCat.ofHom ψ) ≫ s₀ = t := by rw [← hd, Category.comp_id]
    have hn := hnat S₀ C ψ s₀ t hs φ₀ hφ₀
    rw [← hn]
    congr 1

  have hex : ∀ i : M.affineCover.I₀, ∃ (φ : pullback f (M.affineCover.f i ≫ πM) ⟶ Y) (hφ : φ ≫ g = pullback.snd f (M.affineCover.f i ≫ πM) ≫ (M.affineCover.f i ≫ πM)),
      pt _ (M.affineCover.f i ≫ πM) φ hφ = ⟨M.affineCover.f i, rfl⟩ := fun i => hsurj _ (M.affineCover.f i ≫ πM) ⟨M.affineCover.f i, rfl⟩
  choose φ hφ hptφ using hex

  have P1 : ∀ (i : M.affineCover.I₀) (C : Type u) [CommRing C] (t : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of S))
      (d : Spec (CommRingCat.of C) ⟶ M.affineCover.X i) (hd : t ≫ 𝟙 _ = d ≫ (M.affineCover.f i ≫ πM)),
      (pt C t (pullback.map f t f (M.affineCover.f i ≫ πM) (𝟙 X) d (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) hd ≫ φ i)
        (hres (M.affineCover.f i ≫ πM) t d hd (φ i) (hφ i))).1 = d ≫ M.affineCover.f i := by
    intro i C _ t d hd
    have h0 := P0 _ (M.affineCover.f i ≫ πM) (φ i) (hφ i) C t d hd
    exact h0.trans (congrArg (d ≫ ·) (congrArg Subtype.val (hptφ i)))

  have tV : ∀ j : M.affineCover.I₀, IsPullback ((Scheme.Pullback.openCoverOfRight M.affineCover f πM).f j) (pullback.snd f (M.affineCover.f j ≫ πM)) (pullback.snd f πM) (M.affineCover.f j) := fun j => by
    rw [Scheme.Pullback.openCoverOfRight_f]
    exact isPullback_map f πM (M.affineCover.f j) (M.affineCover.f j ≫ πM) rfl (Category.comp_id _)

  have hcompat : ∀ i j : M.affineCover.I₀, pullback.fst ((Scheme.Pullback.openCoverOfRight M.affineCover f πM).f i) ((Scheme.Pullback.openCoverOfRight M.affineCover f πM).f j) ≫ φ i = pullback.snd ((Scheme.Pullback.openCoverOfRight M.affineCover f πM).f i) ((Scheme.Pullback.openCoverOfRight M.affineCover f πM).f j) ≫ φ j := by
    intro i j
    have htQi : (pullback.fst (M.affineCover.f i) (M.affineCover.f j) ≫ (M.affineCover.f i ≫ πM)) ≫ 𝟙 _ = pullback.fst (M.affineCover.f i) (M.affineCover.f j) ≫ (M.affineCover.f i ≫ πM) := Category.comp_id _
    have htQj : (pullback.fst (M.affineCover.f i) (M.affineCover.f j) ≫ (M.affineCover.f i ≫ πM)) ≫ 𝟙 _ = pullback.snd (M.affineCover.f i) (M.affineCover.f j) ≫ (M.affineCover.f j ≫ πM) := by
      rw [Category.comp_id, ← Category.assoc, pullback.condition, Category.assoc]

    have sqA : IsPullback (pullback.map f (pullback.fst (M.affineCover.f i) (M.affineCover.f j) ≫ (M.affineCover.f i ≫ πM)) f (M.affineCover.f i ≫ πM) (𝟙 X) (pullback.fst (M.affineCover.f i) (M.affineCover.f j)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) htQi) (pullback.snd f (pullback.fst (M.affineCover.f i) (M.affineCover.f j) ≫ (M.affineCover.f i ≫ πM))) (pullback.snd f (M.affineCover.f i ≫ πM)) (pullback.fst (M.affineCover.f i) (M.affineCover.f j)) :=
      isPullback_map f (M.affineCover.f i ≫ πM) (pullback.fst (M.affineCover.f i) (M.affineCover.f j)) (pullback.fst (M.affineCover.f i) (M.affineCover.f j) ≫ (M.affineCover.f i ≫ πM)) rfl htQi
    have sbig : IsPullback (pullback.snd f (pullback.fst (M.affineCover.f i) (M.affineCover.f j) ≫ (M.affineCover.f i ≫ πM)) ≫ pullback.snd (M.affineCover.f i) (M.affineCover.f j)) (pullback.map f (pullback.fst (M.affineCover.f i) (M.affineCover.f j) ≫ (M.affineCover.f i ≫ πM)) f (M.affineCover.f i ≫ πM) (𝟙 X) (pullback.fst (M.affineCover.f i) (M.affineCover.f j)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) htQi) (M.affineCover.f j) (pullback.snd f (M.affineCover.f i ≫ πM) ≫ M.affineCover.f i) :=
      sqA.flip.paste_horiz (IsPullback.of_hasPullback (M.affineCover.f i) (M.affineCover.f j)).flip
    have e1 : (pullback.map f (pullback.fst (M.affineCover.f i) (M.affineCover.f j) ≫ (M.affineCover.f i ≫ πM)) f (M.affineCover.f j ≫ πM) (𝟙 X) (pullback.snd (M.affineCover.f i) (M.affineCover.f j)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) htQj) ≫ pullback.snd f (M.affineCover.f j ≫ πM) = pullback.snd f (pullback.fst (M.affineCover.f i) (M.affineCover.f j) ≫ (M.affineCover.f i ≫ πM)) ≫ pullback.snd (M.affineCover.f i) (M.affineCover.f j) := by simp [pullback.map]
    have e3 : (pullback.map f (pullback.fst (M.affineCover.f i) (M.affineCover.f j) ≫ (M.affineCover.f i ≫ πM)) f (M.affineCover.f j ≫ πM) (𝟙 X) (pullback.snd (M.affineCover.f i) (M.affineCover.f j)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) htQj) ≫ (Scheme.Pullback.openCoverOfRight M.affineCover f πM).f j = (pullback.map f (pullback.fst (M.affineCover.f i) (M.affineCover.f j) ≫ (M.affineCover.f i ≫ πM)) f (M.affineCover.f i ≫ πM) (𝟙 X) (pullback.fst (M.affineCover.f i) (M.affineCover.f j)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) htQi) ≫ (Scheme.Pullback.openCoverOfRight M.affineCover f πM).f i := by
      apply pullback.hom_ext <;> simp [Scheme.Pullback.openCoverOfRight_f, pullback.map, pullback.condition]
    have sqQ : IsPullback (pullback.map f (pullback.fst (M.affineCover.f i) (M.affineCover.f j) ≫ (M.affineCover.f i ≫ πM)) f (M.affineCover.f i ≫ πM) (𝟙 X) (pullback.fst (M.affineCover.f i) (M.affineCover.f j)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) htQi) (pullback.map f (pullback.fst (M.affineCover.f i) (M.affineCover.f j) ≫ (M.affineCover.f i ≫ πM)) f (M.affineCover.f j ≫ πM) (𝟙 X) (pullback.snd (M.affineCover.f i) (M.affineCover.f j)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) htQj) ((Scheme.Pullback.openCoverOfRight M.affineCover f πM).f i) ((Scheme.Pullback.openCoverOfRight M.affineCover f πM).f j) := by
      have e2 : (Scheme.Pullback.openCoverOfRight M.affineCover f πM).f i ≫ pullback.snd f πM = pullback.snd f (M.affineCover.f i ≫ πM) ≫ M.affineCover.f i := by
        simp [Scheme.Pullback.openCoverOfRight_f, pullback.map]
      refine (IsPullback.of_right ?_ e3 (tV j).flip).flip
      erw [e1, e2]
      exact sbig

    have hQ : (pullback.map f (pullback.fst (M.affineCover.f i) (M.affineCover.f j) ≫ (M.affineCover.f i ≫ πM)) f (M.affineCover.f i ≫ πM) (𝟙 X) (pullback.fst (M.affineCover.f i) (M.affineCover.f j)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) htQi) ≫ φ i = (pullback.map f (pullback.fst (M.affineCover.f i) (M.affineCover.f j) ≫ (M.affineCover.f i ≫ πM)) f (M.affineCover.f j ≫ πM) (𝟙 X) (pullback.snd (M.affineCover.f i) (M.affineCover.f j)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) htQj) ≫ φ j := by
      apply Scheme.Cover.hom_ext (Scheme.Pullback.openCoverOfRight (pullback (M.affineCover.f i) (M.affineCover.f j)).affineCover f (pullback.fst (M.affineCover.f i) (M.affineCover.f j) ≫ (M.affineCover.f i ≫ πM)))
      intro k
      have hci : ((pullback (M.affineCover.f i) (M.affineCover.f j)).affineCover.f k ≫ (pullback.fst (M.affineCover.f i) (M.affineCover.f j) ≫ (M.affineCover.f i ≫ πM))) ≫ 𝟙 _ = ((pullback (M.affineCover.f i) (M.affineCover.f j)).affineCover.f k ≫ pullback.fst (M.affineCover.f i) (M.affineCover.f j)) ≫ (M.affineCover.f i ≫ πM) := by
        rw [Category.comp_id, Category.assoc]
      have hcj : ((pullback (M.affineCover.f i) (M.affineCover.f j)).affineCover.f k ≫ (pullback.fst (M.affineCover.f i) (M.affineCover.f j) ≫ (M.affineCover.f i ≫ πM))) ≫ 𝟙 _ = ((pullback (M.affineCover.f i) (M.affineCover.f j)).affineCover.f k ≫ pullback.snd (M.affineCover.f i) (M.affineCover.f j)) ≫ (M.affineCover.f j ≫ πM) := by
        rw [Category.comp_id, pullback.condition_assoc, Category.assoc]
      have hmid : pullback.map f ((pullback (M.affineCover.f i) (M.affineCover.f j)).affineCover.f k ≫ (pullback.fst (M.affineCover.f i) (M.affineCover.f j) ≫ (M.affineCover.f i ≫ πM))) f (M.affineCover.f i ≫ πM) (𝟙 X) ((pullback (M.affineCover.f i) (M.affineCover.f j)).affineCover.f k ≫ pullback.fst (M.affineCover.f i) (M.affineCover.f j)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) hci ≫ φ i = pullback.map f ((pullback (M.affineCover.f i) (M.affineCover.f j)).affineCover.f k ≫ (pullback.fst (M.affineCover.f i) (M.affineCover.f j) ≫ (M.affineCover.f i ≫ πM))) f (M.affineCover.f j ≫ πM) (𝟙 X) ((pullback (M.affineCover.f i) (M.affineCover.f j)).affineCover.f k ≫ pullback.snd (M.affineCover.f i) (M.affineCover.f j)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) hcj ≫ φ j := by
        apply hinj _ ((pullback (M.affineCover.f i) (M.affineCover.f j)).affineCover.f k ≫ (pullback.fst (M.affineCover.f i) (M.affineCover.f j) ≫ (M.affineCover.f i ≫ πM))) _ _ (hres (M.affineCover.f i ≫ πM) _ _ hci (φ i) (hφ i)) (hres (M.affineCover.f j ≫ πM) _ _ hcj (φ j) (hφ j))
        apply Subtype.ext
        erw [P1 i _ _ _ hci, P1 j _ _ _ hcj]
        erw [Category.assoc, Category.assoc, pullback.condition]
      have ei : (Scheme.Pullback.openCoverOfRight (pullback (M.affineCover.f i) (M.affineCover.f j)).affineCover f (pullback.fst (M.affineCover.f i) (M.affineCover.f j) ≫ (M.affineCover.f i ≫ πM))).f k ≫ (pullback.map f (pullback.fst (M.affineCover.f i) (M.affineCover.f j) ≫ (M.affineCover.f i ≫ πM)) f (M.affineCover.f i ≫ πM) (𝟙 X) (pullback.fst (M.affineCover.f i) (M.affineCover.f j)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) htQi) = pullback.map f ((pullback (M.affineCover.f i) (M.affineCover.f j)).affineCover.f k ≫ (pullback.fst (M.affineCover.f i) (M.affineCover.f j) ≫ (M.affineCover.f i ≫ πM))) f (M.affineCover.f i ≫ πM) (𝟙 X) ((pullback (M.affineCover.f i) (M.affineCover.f j)).affineCover.f k ≫ pullback.fst (M.affineCover.f i) (M.affineCover.f j)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) hci := by
        apply pullback.hom_ext <;> simp [Scheme.Pullback.openCoverOfRight_f, pullback.map]
      have ej : (Scheme.Pullback.openCoverOfRight (pullback (M.affineCover.f i) (M.affineCover.f j)).affineCover f (pullback.fst (M.affineCover.f i) (M.affineCover.f j) ≫ (M.affineCover.f i ≫ πM))).f k ≫ (pullback.map f (pullback.fst (M.affineCover.f i) (M.affineCover.f j) ≫ (M.affineCover.f i ≫ πM)) f (M.affineCover.f j ≫ πM) (𝟙 X) (pullback.snd (M.affineCover.f i) (M.affineCover.f j)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) htQj) = pullback.map f ((pullback (M.affineCover.f i) (M.affineCover.f j)).affineCover.f k ≫ (pullback.fst (M.affineCover.f i) (M.affineCover.f j) ≫ (M.affineCover.f i ≫ πM))) f (M.affineCover.f j ≫ πM) (𝟙 X) ((pullback (M.affineCover.f i) (M.affineCover.f j)).affineCover.f k ≫ pullback.snd (M.affineCover.f i) (M.affineCover.f j)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) hcj := by
        apply pullback.hom_ext <;> simp [Scheme.Pullback.openCoverOfRight_f, pullback.map]
      have ei' := congrArg (· ≫ φ i) ei
      have ej' := congrArg (· ≫ φ j) ej
      simp only [Category.assoc] at ei' ej'
      erw [ei', ej']
      exact hmid

    have a1 : sqQ.isoPullback.hom ≫ (pullback.fst _ _ ≫ φ i) = (pullback.map f (pullback.fst (M.affineCover.f i) (M.affineCover.f j) ≫ (M.affineCover.f i ≫ πM)) f (M.affineCover.f i ≫ πM) (𝟙 X) (pullback.fst (M.affineCover.f i) (M.affineCover.f j)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) htQi) ≫ φ i := by
      have := congrArg (· ≫ φ i) sqQ.isoPullback_hom_fst
      simpa only [Category.assoc] using this
    have a2 : sqQ.isoPullback.hom ≫ (pullback.snd _ _ ≫ φ j) = (pullback.map f (pullback.fst (M.affineCover.f i) (M.affineCover.f j) ≫ (M.affineCover.f i ≫ πM)) f (M.affineCover.f j ≫ πM) (𝟙 X) (pullback.snd (M.affineCover.f i) (M.affineCover.f j)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) htQj) ≫ φ j := by
      have := congrArg (· ≫ φ j) sqQ.isoPullback_hom_snd
      simpa only [Category.assoc] using this
    exact (cancel_epi sqQ.isoPullback.hom).mp (a1.trans (hQ.trans a2.symm))

  refine ⟨Scheme.Cover.glueMorphisms (Scheme.Pullback.openCoverOfRight M.affineCover f πM) φ hcompat, ?_, ?_⟩
  ·
    apply Scheme.Cover.hom_ext (Scheme.Pullback.openCoverOfRight M.affineCover f πM)
    intro i
    rw [← Category.assoc]
    erw [Scheme.Cover.ι_glueMorphisms, hφ i]
    simp [Scheme.Pullback.openCoverOfRight_f, pullback.map]
  · intro S' _ s φ₁ hφ₁
    apply Scheme.Cover.hom_ext (Scheme.Pullback.openCoverOfRight ((M.affineCover.pullback₁ (pt S' s φ₁ hφ₁).1).bind (fun j => ((M.affineCover.pullback₁ (pt S' s φ₁ hφ₁).1).X j).affineCover)) f s)
    rintro ⟨j, l⟩
    have hz : (pt S' s φ₁ hφ₁).1 ≫ πM = s := (pt S' s φ₁ hφ₁).2
    have hcd : ((pullback (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)).affineCover.f l ≫ pullback.fst (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)) ≫ (pt S' s φ₁ hφ₁).1 = ((pullback (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)).affineCover.f l ≫ pullback.snd (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)) ≫ M.affineCover.f j := by
      rw [Category.assoc, Category.assoc, pullback.condition]
    have hC : (((pullback (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)).affineCover.f l ≫ pullback.fst (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)) ≫ s) ≫ 𝟙 _ = ((pullback (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)).affineCover.f l ≫ pullback.fst (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)) ≫ s := Category.comp_id _
    have hD : (((pullback (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)).affineCover.f l ≫ pullback.fst (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)) ≫ s) ≫ 𝟙 _ = ((pullback (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)).affineCover.f l ≫ pullback.snd (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)) ≫ (M.affineCover.f j ≫ πM) := by
      have e : ((pullback (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)).affineCover.f l ≫ pullback.fst (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)) ≫ ((pt S' s φ₁ hφ₁).1 ≫ πM) = ((pullback (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)).affineCover.f l ≫ pullback.snd (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)) ≫ (M.affineCover.f j ≫ πM) := by rw [← Category.assoc, hcd, Category.assoc]
      rw [Category.comp_id, ← e, hz]

    have hmid : pullback.map f (((pullback (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)).affineCover.f l ≫ pullback.fst (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)) ≫ s) f (M.affineCover.f j ≫ πM) (𝟙 X) ((pullback (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)).affineCover.f l ≫ pullback.snd (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) hD ≫ φ j = pullback.map f (((pullback (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)).affineCover.f l ≫ pullback.fst (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)) ≫ s) f s (𝟙 X) ((pullback (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)).affineCover.f l ≫ pullback.fst (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) hC ≫ φ₁ := by
      apply hinj _ (((pullback (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)).affineCover.f l ≫ pullback.fst (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)) ≫ s) _ _ (hres (M.affineCover.f j ≫ πM) _ _ hD (φ j) (hφ j)) (hres s _ _ hC φ₁ hφ₁)
      apply Subtype.ext
      erw [P1 j _ _ _ hD, P0 S' s φ₁ hφ₁ _ _ _ hC]
      exact hcd.symm

    have eL : (Scheme.Pullback.openCoverOfRight ((M.affineCover.pullback₁ (pt S' s φ₁ hφ₁).1).bind (fun j => ((M.affineCover.pullback₁ (pt S' s φ₁ hφ₁).1).X j).affineCover)) f s).f ⟨j, l⟩ ≫ pullback.map f s f πM (𝟙 X) (pt S' s φ₁ hφ₁).1 (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, (pt S' s φ₁ hφ₁).2]) = pullback.map f (((pullback (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)).affineCover.f l ≫ pullback.fst (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)) ≫ s) f (M.affineCover.f j ≫ πM) (𝟙 X) ((pullback (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)).affineCover.f l ≫ pullback.snd (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) hD ≫ (Scheme.Pullback.openCoverOfRight M.affineCover f πM).f j := by
      apply pullback.hom_ext <;>
        simp [Scheme.Pullback.openCoverOfRight_f, pullback.map, PreZeroHypercover.bind_f, Precoverage.ZeroHypercover.bind,
          pullback.condition]
    have eR : (Scheme.Pullback.openCoverOfRight ((M.affineCover.pullback₁ (pt S' s φ₁ hφ₁).1).bind (fun j => ((M.affineCover.pullback₁ (pt S' s φ₁ hφ₁).1).X j).affineCover)) f s).f ⟨j, l⟩ ≫ φ₁ = pullback.map f (((pullback (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)).affineCover.f l ≫ pullback.fst (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)) ≫ s) f s (𝟙 X) ((pullback (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)).affineCover.f l ≫ pullback.fst (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) hC ≫ φ₁ := rfl
    have s1 : (Scheme.Pullback.openCoverOfRight ((M.affineCover.pullback₁ (pt S' s φ₁ hφ₁).1).bind (fun j => ((M.affineCover.pullback₁ (pt S' s φ₁ hφ₁).1).X j).affineCover)) f s).f ⟨j, l⟩ ≫ (pullback.map f s f πM (𝟙 X) (pt S' s φ₁ hφ₁).1 (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, (pt S' s φ₁ hφ₁).2]) ≫ Scheme.Cover.glueMorphisms (Scheme.Pullback.openCoverOfRight M.affineCover f πM) φ hcompat) = (pullback.map f (((pullback (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)).affineCover.f l ≫ pullback.fst (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)) ≫ s) f (M.affineCover.f j ≫ πM) (𝟙 X) ((pullback (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)).affineCover.f l ≫ pullback.snd (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) hD ≫ (Scheme.Pullback.openCoverOfRight M.affineCover f πM).f j) ≫ Scheme.Cover.glueMorphisms (Scheme.Pullback.openCoverOfRight M.affineCover f πM) φ hcompat :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ Scheme.Cover.glueMorphisms (Scheme.Pullback.openCoverOfRight M.affineCover f πM) φ hcompat) eL)
    have s2 : (pullback.map f (((pullback (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)).affineCover.f l ≫ pullback.fst (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)) ≫ s) f (M.affineCover.f j ≫ πM) (𝟙 X) ((pullback (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)).affineCover.f l ≫ pullback.snd (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) hD ≫ (Scheme.Pullback.openCoverOfRight M.affineCover f πM).f j) ≫ Scheme.Cover.glueMorphisms (Scheme.Pullback.openCoverOfRight M.affineCover f πM) φ hcompat = pullback.map f (((pullback (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)).affineCover.f l ≫ pullback.fst (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)) ≫ s) f (M.affineCover.f j ≫ πM) (𝟙 X) ((pullback (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)).affineCover.f l ≫ pullback.snd (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) hD ≫ φ j :=
      (Category.assoc _ _ _).trans (congrArg (pullback.map f (((pullback (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)).affineCover.f l ≫ pullback.fst (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)) ≫ s) f (M.affineCover.f j ≫ πM) (𝟙 X) ((pullback (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)).affineCover.f l ≫ pullback.snd (pt S' s φ₁ hφ₁).1 (M.affineCover.f j)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) hD ≫ ·) (Scheme.Cover.ι_glueMorphisms (Scheme.Pullback.openCoverOfRight M.affineCover f πM) φ hcompat j))
    exact s1.trans (s2.trans (hmid.trans eR.symm))

end S_AlgebraicGeometry_exists_hom_pullback_comp_eq_and_forall_pullbackMap_comp_eq_of_forall_spec_point
end P2MW
export P2MW.S_AlgebraicGeometry_exists_hom_pullback_comp_eq_and_forall_pullbackMap_comp_eq_of_forall_spec_point (solution)
