-- Prove2me | solution 1 for AlgebraicGeometry.exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/2740c378-9364-5a3b-a55a-54fa67447f40

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
import Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType
import Theorems.Thm_Subalgebra_fg_restrictScalars_and_le_of_fg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans"

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace IsoDesc

variable {A₀ : Type u} [CommRing A₀]

noncomputable abbrev XR {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A₀)) (R : Type u) [CommRing R] [Algebra A₀ R] : Scheme.{u} :=
  pullback f (Spec.map (CommRingCat.ofHom (algebraMap A₀ R)))

section Stage

variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A₀))
  {R R' : Type u} [CommRing R] [Algebra A₀ R] [CommRing R'] [Algebra A₀ R']
  (φ : R →+* R') (hφ : φ.comp (algebraMap A₀ R) = algebraMap A₀ R')

include hφ in
theorem spec_comp : Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (algebraMap A₀ R)) =
    Spec.map (CommRingCat.ofHom (algebraMap A₀ R')) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]

noncomputable def stMap : XR f R' ⟶ XR f R :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom φ))
    (by rw [pullback.condition, Category.assoc, spec_comp φ hφ])

@[scoped simp, reassoc] theorem stMap_fst : stMap f φ hφ ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
@[scoped simp, reassoc] theorem stMap_snd : stMap f φ hφ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom φ) :=
  pullback.lift_snd _ _ _

theorem eq_stMap (q : XR f R' ⟶ XR f R) (h1 : q ≫ pullback.fst _ _ = pullback.fst _ _)
    (h2 : q ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom φ)) : q = stMap f φ hφ := by
  apply pullback.hom_ext
  · rw [h1, stMap_fst]
  · rw [h2, stMap_snd]

end Stage

section Comp

variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A₀))
  {R R' R'' : Type u} [CommRing R] [Algebra A₀ R] [CommRing R'] [Algebra A₀ R'] [CommRing R''] [Algebra A₀ R'']
  (φ : R →+* R') (hφ : φ.comp (algebraMap A₀ R) = algebraMap A₀ R')
  (ψ : R' →+* R'') (hψ : ψ.comp (algebraMap A₀ R') = algebraMap A₀ R'')
  (χ : R →+* R'') (hχ : χ.comp (algebraMap A₀ R) = algebraMap A₀ R'') (h : ψ.comp φ = χ)

include h in
theorem stMap_stMap : stMap f ψ hψ ≫ stMap f φ hφ = stMap f χ hχ := by
  apply pullback.hom_ext
  · rw [Category.assoc, stMap_fst, stMap_fst, stMap_fst]
  · rw [Category.assoc, stMap_snd, stMap_snd_assoc, stMap_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

end Comp

section BC

variable {X₁ X₂ : Scheme.{u}} (f₁ : X₁ ⟶ Spec (CommRingCat.of A₀)) (f₂ : X₂ ⟶ Spec (CommRingCat.of A₀))
  {R R' : Type u} [CommRing R] [Algebra A₀ R] [CommRing R'] [Algebra A₀ R']
  (φ : R →+* R') (hφ : φ.comp (algebraMap A₀ R) = algebraMap A₀ R')
  (g₀ : XR f₁ R ⟶ XR f₂ R) (hg₀ : g₀ ≫ pullback.snd _ _ = pullback.snd _ _)

noncomputable def bc : XR f₁ R' ⟶ XR f₂ R' :=
  pullback.lift (stMap f₁ φ hφ ≫ g₀ ≫ pullback.fst _ _) (pullback.snd _ _)
    (by rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc g₀, hg₀, stMap_snd_assoc, spec_comp φ hφ])

@[scoped simp, reassoc] theorem bc_fst : bc f₁ f₂ φ hφ g₀ hg₀ ≫ pullback.fst _ _ = stMap f₁ φ hφ ≫ g₀ ≫ pullback.fst _ _ :=
  pullback.lift_fst _ _ _
@[scoped simp, reassoc] theorem bc_snd : bc f₁ f₂ φ hφ g₀ hg₀ ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _

theorem bc_stMap : bc f₁ f₂ φ hφ g₀ hg₀ ≫ stMap f₂ φ hφ = stMap f₁ φ hφ ≫ g₀ := by
  apply pullback.hom_ext
  · rw [Category.assoc, stMap_fst, bc_fst, Category.assoc]
  · rw [Category.assoc, stMap_snd, bc_snd_assoc, Category.assoc, hg₀, stMap_snd]

theorem bc_compat {A : Type u} [CommRing A] [Algebra A₀ A]
    (ψ : R →+* A) (hψ : ψ.comp (algebraMap A₀ R) = algebraMap A₀ A)
    (ψ' : R' →+* A) (hψ' : ψ'.comp (algebraMap A₀ R') = algebraMap A₀ A) (hcomp : ψ'.comp φ = ψ)
    (e : XR f₁ A ⟶ XR f₂ A) (he : e ≫ pullback.snd _ _ = pullback.snd _ _)
    (h : stMap f₁ ψ hψ ≫ g₀ = e ≫ stMap f₂ ψ hψ) :
    stMap f₁ ψ' hψ' ≫ bc f₁ f₂ φ hφ g₀ hg₀ = e ≫ stMap f₂ ψ' hψ' := by
  apply pullback.hom_ext
  · rw [Category.assoc, bc_fst, ← Category.assoc, stMap_stMap f₁ φ hφ ψ' hψ' ψ hψ hcomp, ← Category.assoc, h,
      Category.assoc, Category.assoc, stMap_fst, stMap_fst]
  · rw [Category.assoc, bc_snd, stMap_snd, Category.assoc, stMap_snd, ← Category.assoc, he]

end BC

end IsoDesc
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation.IsoDesc"

namespace IsoDesc

section Main

variable {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]

theorem inclusion_comp_algebraMap {T T' : Subalgebra A₀ A} (h : T ≤ T') :
    (Subalgebra.inclusion h).toRingHom.comp (algebraMap A₀ ↥T) = algebraMap A₀ ↥T' :=
  RingHom.ext fun _ => rfl

theorem val_comp_algebraMap (T : Subalgebra A₀ A) : T.val.toRingHom.comp (algebraMap A₀ ↥T) = algebraMap A₀ A :=
  RingHom.ext fun _ => rfl

theorem val_comp_inclusion {T T' : Subalgebra A₀ A} (h : T ≤ T') :
    T'.val.toRingHom.comp (Subalgebra.inclusion h).toRingHom = T.val.toRingHom :=
  RingHom.ext fun _ => rfl

theorem exists_fg_stMap_comp_eq {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A₀)) [QuasiCompact f] [LocallyOfFinitePresentation f]
    (B : Subalgebra A₀ A) (a : XR f ↥B ⟶ XR f ↥B) (ha : a ≫ pullback.snd _ _ = pullback.snd _ _)
    (hlim : stMap f B.val.toRingHom (val_comp_algebraMap B) ≫ a = stMap f B.val.toRingHom (val_comp_algebraMap B)) :
    ∃ T' : Subalgebra ↥B A, T'.FG ∧
      pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥B))))
          (Spec.map (CommRingCat.ofHom (algebraMap ↥B ↥T'))) ≫ a =
        pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥B))))
          (Spec.map (CommRingCat.ofHom (algebraMap ↥B ↥T'))) := by

  let sndB := pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥B)))
  let gA := Spec.map (CommRingCat.ofHom (algebraMap ↥B A))
  have hvB : (algebraMap ↥B A : ↥B →+* A) = B.val.toRingHom := rfl
  have hvB' : (algebraMap ↥B A).comp (algebraMap A₀ ↥B) = algebraMap A₀ A := val_comp_algebraMap B
  let r : pullback sndB gA ⟶ XR f A :=
    pullback.lift (pullback.fst sndB gA ≫ pullback.fst f _) (pullback.snd sndB gA) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc]
      show _ ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥B A)) ≫ _ = _
      rw [spec_comp (algebraMap ↥B A) hvB'])
  have hr : r ≫ stMap f B.val.toRingHom (val_comp_algebraMap B) = pullback.fst sndB gA := by
    apply pullback.hom_ext
    · rw [Category.assoc, stMap_fst, pullback.lift_fst]
    · rw [Category.assoc, stMap_snd, pullback.lift_snd_assoc, ← hvB]
      exact (pullback.condition (f := sndB) (g := gA)).symm
  have hab : pullback.fst sndB gA ≫ a = pullback.fst sndB gA ≫ 𝟙 _ := by
    rw [Category.comp_id, ← hr, Category.assoc, hlim]
  obtain ⟨T', hT'fg, -, hEq⟩ := AlgebraicGeometry.exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType (A₀ := ↥B) (A := A) sndB sndB a (𝟙 _)
    (by rw [ha]) (Category.id_comp _) hab ∅
  exact ⟨T', hT'fg, by rw [hEq, Category.comp_id]⟩

end Main
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation.IsoDesc"

end IsoDesc
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation.IsoDesc"

open IsoDesc in
theorem solution
    {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X₁ X₂ : Scheme.{u}} (f₁ : X₁ ⟶ Spec (CommRingCat.of A₀)) (f₂ : X₂ ⟶ Spec (CommRingCat.of A₀))
    [QuasiCompact f₁] [QuasiSeparated f₁] [LocallyOfFinitePresentation f₁]
    [QuasiCompact f₂] [QuasiSeparated f₂] [LocallyOfFinitePresentation f₂]
    (e : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ≅
      pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))
    (he : e.hom ≫ pullback.snd f₂ _ = pullback.snd f₁ _) (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∃ e₀ : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))) ≅
          pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))),
        e₀.hom ≫ pullback.snd f₂ _ = pullback.snd f₁ _ ∧
        ∀ (q₁ : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ⟶
              pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))))
          (q₂ : pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ⟶
              pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T)))),
          q₁ ≫ pullback.fst f₁ _ = pullback.fst f₁ _ →
          q₁ ≫ pullback.snd f₁ _ = pullback.snd f₁ _ ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom) →
          q₂ ≫ pullback.fst f₂ _ = pullback.fst f₂ _ →
          q₂ ≫ pullback.snd f₂ _ = pullback.snd f₂ _ ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom) →
          q₁ ≫ e₀.hom = e.hom ≫ q₂ := by
  classical

  obtain ⟨T₁, hT₁fg, hsT₁, g₀, hg₀snd, hg₀q⟩ := AlgebraicGeometry.exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation f₁ f₂ e.hom he s
  have he' : e.inv ≫ pullback.snd f₁ _ = pullback.snd f₂ _ := by rw [← he, e.inv_hom_id_assoc]
  obtain ⟨T₂, hT₂fg, hsT₂, h₀, hh₀snd, hh₀q⟩ := AlgebraicGeometry.exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation f₂ f₁ e.inv he' s

  have cg₀ : stMap f₁ T₁.val.toRingHom (val_comp_algebraMap T₁) ≫ g₀ = e.hom ≫ stMap f₂ T₁.val.toRingHom (val_comp_algebraMap T₁) :=
    hg₀q _ _ (stMap_fst _ _ _) (stMap_snd _ _ _) (stMap_fst _ _ _) (stMap_snd _ _ _)
  have ch₀ : stMap f₂ T₂.val.toRingHom (val_comp_algebraMap T₂) ≫ h₀ = e.inv ≫ stMap f₁ T₂.val.toRingHom (val_comp_algebraMap T₂) :=
    hh₀q _ _ (stMap_fst _ _ _) (stMap_snd _ _ _) (stMap_fst _ _ _) (stMap_snd _ _ _)

  let B : Subalgebra A₀ A := T₁ ⊔ T₂
  have hBfg : B.FG := hT₁fg.sup hT₂fg
  let ι₁ : ↥T₁ →+* ↥B := (Subalgebra.inclusion (le_sup_left : T₁ ≤ B)).toRingHom
  let ι₂ : ↥T₂ →+* ↥B := (Subalgebra.inclusion (le_sup_right : T₂ ≤ B)).toRingHom
  have hι₁ := inclusion_comp_algebraMap (le_sup_left : T₁ ≤ B)
  have hι₂ := inclusion_comp_algebraMap (le_sup_right : T₂ ≤ B)
  let gB := bc f₁ f₂ ι₁ hι₁ g₀ hg₀snd
  let hB := bc f₂ f₁ ι₂ hι₂ h₀ hh₀snd
  have hgBsnd : gB ≫ pullback.snd _ _ = pullback.snd _ _ := bc_snd _ _ _ _ _ _
  have hhBsnd : hB ≫ pullback.snd _ _ = pullback.snd _ _ := bc_snd _ _ _ _ _ _
  have cgB : stMap f₁ B.val.toRingHom (val_comp_algebraMap B) ≫ gB = e.hom ≫ stMap f₂ B.val.toRingHom (val_comp_algebraMap B) :=
    bc_compat f₁ f₂ ι₁ hι₁ g₀ hg₀snd _ _ _ _ (val_comp_inclusion le_sup_left) e.hom he cg₀
  have chB : stMap f₂ B.val.toRingHom (val_comp_algebraMap B) ≫ hB = e.inv ≫ stMap f₁ B.val.toRingHom (val_comp_algebraMap B) :=
    bc_compat f₂ f₁ ι₂ hι₂ h₀ hh₀snd _ _ _ _ (val_comp_inclusion le_sup_right) e.inv he' ch₀

  obtain ⟨T', hT'fg, hEq1⟩ := exists_fg_stMap_comp_eq f₁ B (gB ≫ hB) (by rw [Category.assoc, hhBsnd, hgBsnd])
    (by rw [← Category.assoc, cgB, Category.assoc, chB, e.hom_inv_id_assoc])
  obtain ⟨T'', hT''fg, hEq2⟩ := exists_fg_stMap_comp_eq f₂ B (hB ≫ gB) (by rw [Category.assoc, hgBsnd, hhBsnd])
    (by rw [← Category.assoc, chB, Category.assoc, cgB, e.inv_hom_id_assoc])
  let Ts : Subalgebra ↥B A := T' ⊔ T''
  obtain ⟨hTfg, hBT⟩ := Subalgebra.fg_restrictScalars_and_le_of_fg B hBfg Ts (hT'fg.sup hT''fg)
  let T : Subalgebra A₀ A := Ts.restrictScalars A₀
  have hBT' : B ≤ T := hBT
  let κ : ↥B →+* ↥T := (Subalgebra.inclusion hBT').toRingHom
  have hκ := inclusion_comp_algebraMap hBT'

  have hκ' : ∀ (T₀ : Subalgebra ↥B A) (hT₀ : T₀ ≤ Ts),
      (Subalgebra.inclusion hT₀).toRingHom.comp (algebraMap ↥B ↥T₀) = κ := fun T₀ hT₀ => RingHom.ext fun _ => rfl

  have key : ∀ {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A₀)) (T₀ : Subalgebra ↥B A) (hT₀ : T₀ ≤ Ts)
      (a : XR f ↥B ⟶ XR f ↥B),
      pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥B))))
          (Spec.map (CommRingCat.ofHom (algebraMap ↥B ↥T₀))) ≫ a =
        pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥B))))
          (Spec.map (CommRingCat.ofHom (algebraMap ↥B ↥T₀))) →
      stMap f κ hκ ≫ a = stMap f κ hκ := by
    intro X f T₀ hT₀ a hEq
    let ρ : XR f ↥T ⟶ pullback (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥B))))
        (Spec.map (CommRingCat.ofHom (algebraMap ↥B ↥T₀))) :=
      pullback.lift (stMap f κ hκ) (pullback.snd f _ ≫ Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hT₀).toRingHom)) (by
        rw [stMap_snd, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        exact congrArg (fun φ : ↥B →+* ↥T => pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))) ≫
          Spec.map (CommRingCat.ofHom φ)) (hκ' T₀ hT₀).symm)
    have hρ : ρ ≫ pullback.fst _ _ = stMap f κ hκ := pullback.lift_fst _ _ _
    rw [← hρ, Category.assoc, hEq]

  let e₀ := bc f₁ f₂ κ hκ gB hgBsnd
  let e₀' := bc f₂ f₁ κ hκ hB hhBsnd
  have h1 : e₀ ≫ e₀' = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, bc_fst, ← Category.assoc e₀, bc_stMap, Category.id_comp, Category.assoc, ← Category.assoc gB,
        ← Category.assoc (stMap f₁ κ hκ), key f₁ T' le_sup_left (gB ≫ hB) hEq1, stMap_fst]
    · rw [Category.assoc, bc_snd, bc_snd, Category.id_comp]
  have h2 : e₀' ≫ e₀ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, bc_fst, ← Category.assoc e₀', bc_stMap, Category.id_comp, Category.assoc, ← Category.assoc hB,
        ← Category.assoc (stMap f₂ κ hκ), key f₂ T'' le_sup_right (hB ≫ gB) hEq2, stMap_fst]
    · rw [Category.assoc, bc_snd, bc_snd, Category.id_comp]
  refine ⟨T, hTfg, fun x hx => hBT (le_sup_left (α := Subalgebra A₀ A) (a := T₁) (b := T₂) (hsT₁ hx)), ⟨e₀, e₀', h1, h2⟩,
    bc_snd f₁ f₂ κ hκ gB hgBsnd, ?_⟩
  intro q₁ q₂ hq₁ hq₁' hq₂ hq₂'
  rw [eq_stMap f₁ T.val.toRingHom (val_comp_algebraMap T) q₁ hq₁ hq₁', eq_stMap f₂ T.val.toRingHom (val_comp_algebraMap T) q₂ hq₂ hq₂']
  exact bc_compat f₁ f₂ κ hκ gB hgBsnd _ _ _ _ (val_comp_inclusion hBT') e.hom he cgB

end S_AlgebraicGeometry_exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation
end P2MW
export P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation (solution)
