-- Prove2me | solution 1 for AlgebraicGeometry.exists_affine_weilRestriction_forall_existsUnique
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/c795c3e5-ac5f-539a-9bd1-dac53e68d56b

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Theorems.Thm_Algebra_exists_weilRestriction_points_equiv_finiteType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_affine_weilRestriction_forall_existsUnique

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open scoped TensorProduct

universe u

namespace ResPointsAllW3

set_option backward.isDefEq.respectTransparency false

noncomputable section

noncomputable def specOverEquiv (A B C : Type u) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C] :
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap A C))) (Spec.map (CommRingCat.ofHom (algebraMap A B))) ≃
      (B →ₐ[A] C) where
  toFun x :=
    { (Spec.preimage x.1).hom with
      commutes' := fun a => by
        have h : CommRingCat.ofHom (algebraMap A B) ≫ Spec.preimage x.1 = CommRingCat.ofHom (algebraMap A C) := by
          apply Spec.map_injective
          rw [Spec.map_comp, Spec.map_preimage]
          exact x.2
        have := congrArg (fun g : CommRingCat.of A ⟶ CommRingCat.of C => g.hom a) h
        simpa using this }
  invFun χ := ⟨Spec.map (CommRingCat.ofHom χ.toRingHom), by
    rw [← Spec.map_comp]
    congr 1
    ext a
    simp⟩
  left_inv x := by
    apply Subtype.ext
    change Spec.map (CommRingCat.ofHom (Spec.preimage x.1).hom) = x.1
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  right_inv χ := by
    apply AlgHom.ext
    intro b
    change (Spec.preimage (Spec.map (CommRingCat.ofHom χ.toRingHom))).hom b = χ b
    rw [Spec.preimage_map]
    rfl

theorem coe_eq_specMap (A B C : Type u) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap A C))) (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :
    x.1 = Spec.map (CommRingCat.ofHom (specOverEquiv A B C x).toRingHom) :=
  (congrArg Subtype.val ((specOverEquiv A B C).left_inv x)).symm

theorem specMap_ofHom_injective (B C : Type u) [CommRing B] [CommRing C] {A : Type u} [CommRing A] [Algebra A B] [Algebra A C]
    (f g : B →ₐ[A] C) (h : Spec.map (CommRingCat.ofHom f.toRingHom) = Spec.map (CommRingCat.ofHom g.toRingHom)) : f = g := by
  have h1 := Spec.map_injective h
  have h2 : f.toRingHom = g.toRingHom := by
    have := congrArg CommRingCat.Hom.hom h1
    simpa using this
  exact AlgHom.coe_ringHom_injective h2

section BC

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R'] [Algebra R R'] {W : Type u} [CommRing W] [Algebra R W]

abbrev bc {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : T ⟶ Spec (CommRingCat.of W))
    (hx : x ≫ Spec.map (CommRingCat.ofHom (algebraMap R W)) = t) :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R R'))) t ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (Spec.map (CommRingCat.ofHom (algebraMap R W))) :=
  pullback.lift (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R R'))) t)
    (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R R'))) t ≫ x) (by rw [Category.assoc, hx, pullback.condition])

abbrev mg {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (g : T' ⟶ T) :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (g ≫ t) ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R R'))) t :=
  pullback.map _ _ _ _ (𝟙 _) g (𝟙 _) (by simp) (Category.comp_id _)

theorem mg_fst {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (g : T' ⟶ T) :
    mg (R' := R') t g ≫ pullback.fst _ _ = pullback.fst _ _ := by
  simp [mg]

theorem mg_bc {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (g : T' ⟶ T) (x : T ⟶ Spec (CommRingCat.of W))
    (hx : x ≫ Spec.map (CommRingCat.ofHom (algebraMap R W)) = t) :
    mg (R' := R') t g ≫ bc t x hx = bc (g ≫ t) (g ≫ x) (by rw [Category.assoc, hx]) := by
  apply pullback.hom_ext <;> simp [mg, bc]

theorem bc_congr {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) {x x' : T ⟶ Spec (CommRingCat.of W)}
    (hx : x ≫ Spec.map (CommRingCat.ofHom (algebraMap R W)) = t) (hx' : x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R W)) = t)
    (h : x = x') : bc (R' := R') t x hx = bc t x' hx' := by
  subst h; rfl

theorem iso_inv_bc_iso_hom (A : Type u) [CommRing A] [Algebra R A] (f : W →ₐ[R] A) :
    (pullbackSpecIso R R' A).inv ≫ bc (Spec.map (CommRingCat.ofHom (algebraMap R A))) (Spec.map (CommRingCat.ofHom f.toRingHom))
        (by rw [← Spec.map_comp]; congr 1; ext a; simp) ≫ (pullbackSpecIso R R' W).hom =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R' R') f).toRingHom) := by
  rw [← Category.assoc, ← Iso.eq_comp_inv]
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullbackSpecIso_inv_fst, Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]
    first
    | rfl
    | (congr 1; ext r; simp)
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullbackSpecIso_inv_snd, Category.assoc, pullbackSpecIso_inv_snd,
      ← Spec.map_comp, ← Spec.map_comp]
    first
    | rfl
    | (congr 1; ext w; simp)

end BC

section Affine

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R'] [Algebra R R'] {W : Type u} [CommRing W] [Algebra R W]
  {H : Type u} [CommRing H] [Algebra R' H]
  (eW : ∀ (T : Type u) [CommRing T] [Algebra R T], (W →ₐ[R] T) ≃ (H →ₐ[R'] (R' ⊗[R] T)))
  (he : ∀ (T T' : Type u) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T'] (u : T →ₐ[R] T')
          (f : W →ₐ[R] T), eW T' (u.comp f) = (Algebra.TensorProduct.map (AlgHom.id R' R') u).comp (eW T f))

def υ : pullback (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (Spec.map (CommRingCat.ofHom (algebraMap R W))) ⟶
    Spec (CommRingCat.of H) :=
  (pullbackSpecIso R R' W).hom ≫ Spec.map (CommRingCat.ofHom (eW W (AlgHom.id R W)).toRingHom)

theorem υ_over : υ eW ≫ Spec.map (CommRingCat.ofHom (algebraMap R' H)) = pullback.fst _ _ := by
  rw [υ, Category.assoc, ← Spec.map_comp]
  have : CommRingCat.ofHom (algebraMap R' H) ≫ CommRingCat.ofHom (eW W (AlgHom.id R W)).toRingHom =
      CommRingCat.ofHom (algebraMap R' (R' ⊗[R] W)) := by
    ext r
    simp
  rw [this]
  exact pullbackSpecIso_hom_fst' R R' W

include he in

theorem iso_inv_bc_υ (A : Type u) [CommRing A] [Algebra R A] (f : W →ₐ[R] A) :
    (pullbackSpecIso R R' A).inv ≫ bc (Spec.map (CommRingCat.ofHom (algebraMap R A))) (Spec.map (CommRingCat.ofHom f.toRingHom))
        (by rw [← Spec.map_comp]; congr 1; ext a; simp) ≫ υ eW =
      Spec.map (CommRingCat.ofHom (eW A f).toRingHom) := by
  have h1 := iso_inv_bc_iso_hom (R' := R') A f
  have h2 : eW A f = (Algebra.TensorProduct.map (AlgHom.id R' R') f).comp (eW W (AlgHom.id R W)) := by
    rw [← he W A f (AlgHom.id R W), AlgHom.comp_id]
  rw [υ, reassoc_of% h1, ← Spec.map_comp, h2]
  rfl

include he in

theorem existsUnique_affine (A : Type u) [CommRing A] [Algebra R A]
    (y : SchemeHomOver (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (Spec.map (CommRingCat.ofHom (algebraMap R A))))
      (Spec.map (CommRingCat.ofHom (algebraMap R' H)))) :
    ∃! x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R A))) (Spec.map (CommRingCat.ofHom (algebraMap R W))),
      bc _ x.1 x.2 ≫ υ eW = y.1 := by

  let y' : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R' (R' ⊗[R] A)))) (Spec.map (CommRingCat.ofHom (algebraMap R' H))) :=
    ⟨(pullbackSpecIso R R' A).inv ≫ y.1, by rw [Category.assoc, y.2, pullbackSpecIso_inv_fst']⟩
  let g : H →ₐ[R'] R' ⊗[R] A := specOverEquiv R' H (R' ⊗[R] A) y'
  have hg : (pullbackSpecIso R R' A).inv ≫ y.1 = Spec.map (CommRingCat.ofHom g.toRingHom) := coe_eq_specMap R' H _ y'

  let f : W →ₐ[R] A := (eW A).symm g
  let x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R A))) (Spec.map (CommRingCat.ofHom (algebraMap R W))) :=
    (specOverEquiv R W A).symm f
  have hx1 : x.1 = Spec.map (CommRingCat.ofHom f.toRingHom) := rfl
  refine ⟨x, ?_, ?_⟩
  · apply (cancel_epi (pullbackSpecIso R R' A).inv).mp
    rw [hg]
    have := iso_inv_bc_υ eW he A f
    rw [Equiv.apply_symm_apply] at this
    exact this
  ·
    intro x' hx'
    let f' : W →ₐ[R] A := specOverEquiv R W A x'
    have hx'1 : x'.1 = Spec.map (CommRingCat.ofHom f'.toRingHom) := coe_eq_specMap R W A x'
    have h1 : (pullbackSpecIso R R' A).inv ≫ bc _ x'.1 x'.2 ≫ υ eW = Spec.map (CommRingCat.ofHom (eW A f').toRingHom) := by
      rw [← iso_inv_bc_υ eW he A f']
      rw [bc_congr (R' := R') _ x'.2 (by rw [← Spec.map_comp]; congr 1; ext a; simp) hx'1]
    rw [hx', hg] at h1
    have hff : eW A f' = g := (specMap_ofHom_injective H (R' ⊗[R] A) _ _ h1).symm
    have hff' : f' = f := by
      apply (eW A).injective
      rw [hff, Equiv.apply_symm_apply]
    apply (specOverEquiv R W A).injective
    change f' = specOverEquiv R W A ((specOverEquiv R W A).symm f)
    rw [Equiv.apply_symm_apply]
    exact hff'

end Affine

section Glue

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R'] [Algebra R R'] {W : Type u} [CommRing W] [Algebra R W]
  {SH : Scheme.{u}} (pH : SH ⟶ Spec (CommRingCat.of R'))
  (υ : pullback (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (Spec.map (CommRingCat.ofHom (algebraMap R W))) ⟶ SH)
  (hυ : υ ≫ pH = pullback.fst _ _)
  (haff : ∀ (A : CommRingCat.{u}) (t : Spec A ⟶ Spec (CommRingCat.of R))
    (y : SchemeHomOver (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R R'))) t) pH),
    ∃! x : SchemeHomOver t (Spec.map (CommRingCat.ofHom (algebraMap R W))), bc t x.1 x.2 ≫ υ = y.1)

include haff hυ in

theorem unique_all {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x₁ x₂ : SchemeHomOver t (Spec.map (CommRingCat.ofHom (algebraMap R W))))
    (h : bc t x₁.1 x₁.2 ≫ υ = bc t x₂.1 x₂.2 ≫ υ) : x₁ = x₂ := by
  apply Subtype.ext
  apply Scheme.Cover.hom_ext T.affineCover
  intro i
  let g := T.affineCover.f i
  let z₁ : SchemeHomOver (g ≫ t) (Spec.map (CommRingCat.ofHom (algebraMap R W))) := ⟨g ≫ x₁.1, by rw [Category.assoc, x₁.2]⟩
  let z₂ : SchemeHomOver (g ≫ t) (Spec.map (CommRingCat.ofHom (algebraMap R W))) := ⟨g ≫ x₂.1, by rw [Category.assoc, x₂.2]⟩
  let y : SchemeHomOver (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (g ≫ t)) pH :=
    ⟨bc (g ≫ t) z₁.1 z₁.2 ≫ υ, by rw [Category.assoc, hυ, pullback.lift_fst]⟩
  obtain ⟨x₀, -, huniq⟩ := haff _ (g ≫ t) y
  have e1 : z₁ = x₀ := huniq z₁ rfl
  have e2 : z₂ = x₀ := huniq z₂ (by
    change bc (g ≫ t) (g ≫ x₂.1) _ ≫ υ = bc (g ≫ t) (g ≫ x₁.1) _ ≫ υ
    rw [← mg_bc t g x₂.1 x₂.2, ← mg_bc t g x₁.1 x₁.2, Category.assoc, Category.assoc, h])
  exact (congrArg Subtype.val e1).trans (congrArg Subtype.val e2).symm

include haff hυ in

theorem exists_all {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (y : SchemeHomOver (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R R'))) t) pH) :
    ∃ x : SchemeHomOver t (Spec.map (CommRingCat.ofHom (algebraMap R W))), bc t x.1 x.2 ≫ υ = y.1 := by
  let 𝒰 := T.affineCover

  have hloc : ∀ i, ∃ xi : SchemeHomOver (𝒰.f i ≫ t) (Spec.map (CommRingCat.ofHom (algebraMap R W))),
      bc (𝒰.f i ≫ t) xi.1 xi.2 ≫ υ = mg t (𝒰.f i) ≫ y.1 := by
    intro i
    let yi : SchemeHomOver (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (𝒰.f i ≫ t)) pH :=
      ⟨mg t (𝒰.f i) ≫ y.1, by rw [Category.assoc, y.2, mg_fst]⟩
    obtain ⟨xi, hxi, -⟩ := haff _ (𝒰.f i ≫ t) yi
    exact ⟨xi, hxi⟩
  choose xs hxs using hloc

  have hcompat : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ (xs i).1 = pullback.snd (𝒰.f i) (𝒰.f j) ≫ (xs j).1 := by
    intro i j
    let w₁ : SchemeHomOver (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ t) (Spec.map (CommRingCat.ofHom (algebraMap R W))) :=
      ⟨pullback.fst (𝒰.f i) (𝒰.f j) ≫ (xs i).1, by rw [Category.assoc, (xs i).2]⟩
    let w₂ : SchemeHomOver (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ t) (Spec.map (CommRingCat.ofHom (algebraMap R W))) :=
      ⟨pullback.snd (𝒰.f i) (𝒰.f j) ≫ (xs j).1, by rw [Category.assoc, (xs j).2, pullback.condition_assoc]⟩
    suffices heq : w₁ = w₂ from congrArg Subtype.val heq
    apply unique_all pH υ hυ haff (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ t)

    have hM : pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ t) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R R')) =
        (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ t) ≫
          pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) ≫ t := by
      rw [pullback.condition]; simp only [Category.assoc]
    have e1 : bc _ w₁.1 w₁.2 ≫ υ = pullback.lift _ _ hM ≫ y.1 := by
      have h1 : bc _ w₁.1 w₁.2 = mg (R' := R') (𝒰.f i ≫ t) (pullback.fst (𝒰.f i) (𝒰.f j)) ≫ bc (𝒰.f i ≫ t) (xs i).1 (xs i).2 := by
        rw [mg_bc]
      rw [h1, Category.assoc, hxs i, ← Category.assoc (mg (𝒰.f i ≫ t) (pullback.fst (𝒰.f i) (𝒰.f j))) (mg t (𝒰.f i)) y.1]
      congr 1
      apply pullback.hom_ext <;> simp [mg]
    have hM' : pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ t) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R R')) =
        (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ t) ≫
          pullback.snd (𝒰.f i) (𝒰.f j)) ≫ 𝒰.f j ≫ t := by
      rw [pullback.condition]; simp only [Category.assoc]; rw [pullback.condition_assoc]
    have e2 : bc _ w₂.1 w₂.2 ≫ υ = pullback.lift _ _ hM ≫ y.1 := by
      have h1 : bc _ w₂.1 w₂.2 = pullback.lift _ _ hM' ≫ bc (𝒰.f j ≫ t) (xs j).1 (xs j).2 := by
        apply pullback.hom_ext
        · simp [bc]
        · simp only [bc, pullback.lift_snd, Category.assoc, pullback.lift_snd_assoc]
          rfl
      rw [h1, Category.assoc, hxs j, ← Category.assoc (pullback.lift _ _ hM') (mg t (𝒰.f j)) y.1]
      congr 1
      apply pullback.hom_ext
      · simp [mg]
      · simp [mg, pullback.condition]
    rw [e1, e2]

  let x : T ⟶ Spec (CommRingCat.of W) := 𝒰.glueMorphisms (fun i => (xs i).1) hcompat
  have hxι : ∀ i, 𝒰.f i ≫ x = (xs i).1 := fun i => 𝒰.ι_glueMorphisms _ _ i
  have hx : x ≫ Spec.map (CommRingCat.ofHom (algebraMap R W)) = t := by
    apply Scheme.Cover.hom_ext 𝒰
    intro i
    rw [← Category.assoc, hxι, (xs i).2]
  refine ⟨⟨x, hx⟩, ?_⟩

  apply Scheme.Cover.hom_ext (Scheme.Pullback.openCoverOfRight 𝒰 (Spec.map (CommRingCat.ofHom (algebraMap R R'))) t)
  intro i
  rw [Scheme.Pullback.openCoverOfRight_f]
  change mg t (𝒰.f i) ≫ bc t x hx ≫ υ = mg t (𝒰.f i) ≫ y.1
  rw [← Category.assoc, mg_bc, ← hxs i]
  congr 2
  exact hxι i

end Glue

end

end ResPointsAllW3

open ResPointsAllW3 in
theorem solution
    (R : Type u) [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R'] [Module.Free R R']
    (H : Type u) [CommRing H] [Algebra R' H] [Algebra.FiniteType R' H] :
    ∃ (W : Type u) (_ : CommRing W) (_ : Algebra R W), Algebra.FiniteType R W ∧
      ∃ υ : pullback (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (Spec.map (CommRingCat.ofHom (algebraMap R W))) ⟶
          Spec (CommRingCat.of H),
        υ ≫ Spec.map (CommRingCat.ofHom (algebraMap R' H)) = pullback.fst _ _ ∧
        ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of R))
          (y : SchemeHomOver (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R R'))) t)
            (Spec.map (CommRingCat.ofHom (algebraMap R' H)))),
          ∃! x : SchemeHomOver t (Spec.map (CommRingCat.ofHom (algebraMap R W))),
            pullback.lift (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R R'))) t)
                (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R R'))) t ≫ x.1)
                (by rw [Category.assoc, x.2, pullback.condition]) ≫ υ = y.1 := by
  obtain ⟨W, iW, iWA, hft, eW, he⟩ := Algebra.exists_weilRestriction_points_equiv_finiteType R R' H
  letI := iW; letI := iWA
  refine ⟨W, iW, iWA, hft, ResPointsAllW3.υ eW, υ_over eW, ?_⟩

  have haff : ∀ (A : CommRingCat.{u}) (t : Spec A ⟶ Spec (CommRingCat.of R))
      (y : SchemeHomOver (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R R'))) t)
        (Spec.map (CommRingCat.ofHom (algebraMap R' H)))),
      ∃! x : SchemeHomOver t (Spec.map (CommRingCat.ofHom (algebraMap R W))), bc t x.1 x.2 ≫ ResPointsAllW3.υ eW = y.1 := by
    intro A t y
    obtain ⟨φ, rfl⟩ := Spec.map_surjective t
    letI : Algebra R A := φ.hom.toAlgebra
    exact existsUnique_affine eW he A y
  intro T t y
  obtain ⟨x, hx⟩ := exists_all (Spec.map (CommRingCat.ofHom (algebraMap R' H))) (ResPointsAllW3.υ eW) (υ_over eW) haff t y
  exact ⟨x, hx, fun x' hx' => unique_all (Spec.map (CommRingCat.ofHom (algebraMap R' H))) (ResPointsAllW3.υ eW) (υ_over eW) haff t x' x (hx'.trans hx.symm)⟩

end S_AlgebraicGeometry_exists_affine_weilRestriction_forall_existsUnique
end P2MW
export P2MW.S_AlgebraicGeometry_exists_affine_weilRestriction_forall_existsUnique (solution)
