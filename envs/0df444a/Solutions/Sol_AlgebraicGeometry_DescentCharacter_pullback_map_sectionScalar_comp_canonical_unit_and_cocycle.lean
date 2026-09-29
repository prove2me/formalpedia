-- Prove2me | solution 1 for AlgebraicGeometry.DescentCharacter.pullback_map_sectionScalar_comp_canonical_unit_and_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/a65f9266-5b08-5484-8329-68bcd6c9008a

import Mathlib
import Definitions.Def_AlgebraicGeometry_DescentCharacter
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_DescentCharacter_pullback_map_sectionScalar_comp_canonical_unit_and_cocycle

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace FRC

variable {X Y Z W : Scheme.{u}}

theorem sa {V : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ V) : (f ≫ g) ≫ h = f ≫ g ≫ h := rfl

theorem pullbackCongr_hom_app {f g : X ⟶ Y} (h : f = g) (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr h).hom.app M = eqToHom (by rw [h]) := by
  subst h; simp [Scheme.Modules.pullbackCongr]

theorem assoc_app (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (M : W.Modules) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app M) ≫
        (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app M =
      (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
        (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M := by
  have H := congr_app (congr_arg Iso.hom
    (SheafOfModules.pullback_assoc.{u} h.toRingCatSheafHom g.toRingCatSheafHom f.toRingCatSheafHom)) M
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_inv_app] at H
  erw [Category.id_comp] at H
  exact H.symm

theorem hom_inv_app {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (e : F ≅ G) (M : C) :
    e.hom.app M ≫ e.inv.app M = 𝟙 _ := by
  rw [← NatTrans.comp_app, Iso.hom_inv_id, NatTrans.id_app]

theorem inv_hom_app {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (e : F ≅ G) (M : C) :
    e.inv.app M ≫ e.hom.app M = 𝟙 _ := by
  rw [← NatTrans.comp_app, Iso.inv_hom_id, NatTrans.id_app]

theorem star1 (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (M : W.Modules) :
    (Scheme.Modules.pullbackComp f g).inv.app ((Scheme.Modules.pullback h).obj M) ≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app M) =
      (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M ≫
        (Scheme.Modules.pullbackComp f (g ≫ h)).inv.app M := by
  have A := assoc_app f g h M
  have C := hom_inv_app (Scheme.Modules.pullbackComp f (g ≫ h)) M
  have B : (Scheme.Modules.pullbackComp f g).inv.app ((Scheme.Modules.pullback h).obj M) ≫
      ((Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app M) ≫
        (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app M) =
      (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M := by
    erw [A, reassoc_of% (inv_hom_app (Scheme.Modules.pullbackComp f g) ((Scheme.Modules.pullback h).obj M))]
  dsimp only [Functor.comp_obj, sa] at A B C ⊢
  rw [← B]
  simp only [Category.assoc]
  rw [C]
  simp only [Category.comp_id]

theorem star2 (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (M : W.Modules) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).inv.app M) ≫
        (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) =
      (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app M ≫
        (Scheme.Modules.pullbackComp (f ≫ g) h).inv.app M := by
  have A := assoc_app f g h M
  have C1 := hom_inv_app (Scheme.Modules.pullbackComp (f ≫ g) h) M
  have C2 : (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).inv.app M) ≫
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app M) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, inv_hom_app, CategoryTheory.Functor.map_id]
  have B : (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app M) ≫
      ((Scheme.Modules.pullbackComp f (g ≫ h)).hom.app M ≫ (Scheme.Modules.pullbackComp (f ≫ g) h).inv.app M) =
      (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) := by
    dsimp only [Functor.comp_obj, sa] at A C1 ⊢
    rw [reassoc_of% A, C1]
    try simp only [Category.comp_id]
  dsimp only [Functor.comp_obj, sa] at B C2 ⊢
  rw [← B]
  try simp only [Category.assoc]
  rw [reassoc_of% C2]

theorem comp_inv_eqToHom_comp_hom (s : X ⟶ Y) {g g' : Y ⟶ Z} (hg : g = g') (L : Z.Modules) :
    (Scheme.Modules.pullbackComp s g).inv.app L ≫
        eqToHom (show (Scheme.Modules.pullback s).obj ((Scheme.Modules.pullback g).obj L) =
          (Scheme.Modules.pullback s).obj ((Scheme.Modules.pullback g').obj L) by rw [hg]) ≫
        (Scheme.Modules.pullbackComp s g').hom.app L =
      eqToHom (by rw [hg]) := by
  subst hg
  erw [eqToHom_refl, Category.id_comp, ← NatTrans.comp_app, Iso.inv_hom_id, NatTrans.id_app]
  exact (eqToHom_refl _ _).symm

theorem eqToHom_comp_hom (a : Y ⟶ Z) {f f' : X ⟶ Y} (hf : f = f') (L : Z.Modules) :
    eqToHom (show (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback a).obj L) =
        (Scheme.Modules.pullback f').obj ((Scheme.Modules.pullback a).obj L) by rw [hf]) ≫
        (Scheme.Modules.pullbackComp f' a).hom.app L =
      (Scheme.Modules.pullbackComp f a).hom.app L ≫ eqToHom (by rw [hf]) := by
  subst hf; simp

end FRC

namespace G1C
variable {X Y P Z : Scheme.{u}}

noncomputable def canonIso (q : X ⟶ Y) (M : Y.Modules) (r : P ⟶ Y) (g₁ g₂ : P ⟶ X) (hg₁ : g₁ ≫ q = r) (hg₂ : g₂ ≫ q = r) :
    (Scheme.Modules.pullback g₁).obj ((Scheme.Modules.pullback q).obj M) ≅
      (Scheme.Modules.pullback g₂).obj ((Scheme.Modules.pullback q).obj M) :=
  (Scheme.Modules.pullbackComp g₁ q).app M ≪≫
    eqToIso (show (Scheme.Modules.pullback (g₁ ≫ q)).obj M = (Scheme.Modules.pullback (g₂ ≫ q)).obj M by
      rw [hg₁, hg₂]) ≪≫
    ((Scheme.Modules.pullbackComp g₂ q).app M).symm

theorem canonIso_hom (q : X ⟶ Y) (M : Y.Modules) (r : P ⟶ Y) (g₁ g₂ : P ⟶ X) (hg₁ : g₁ ≫ q = r) (hg₂ : g₂ ≫ q = r) :
    (canonIso q M r g₁ g₂ hg₁ hg₂).hom = (Scheme.Modules.pullbackComp g₁ q).hom.app M ≫
      eqToHom (show (Scheme.Modules.pullback (g₁ ≫ q)).obj M = (Scheme.Modules.pullback (g₂ ≫ q)).obj M by
        rw [hg₁, hg₂]) ≫ (Scheme.Modules.pullbackComp g₂ q).inv.app M := by
  simp only [canonIso, Iso.trans_hom, Iso.app_hom, eqToIso.hom, Iso.symm_hom, Iso.app_inv]

theorem canon_self (q : X ⟶ Y) (M : Y.Modules) (r : P ⟶ Y) (g : P ⟶ X) (hg : g ≫ q = r) :
    (canonIso q M r g g hg hg).hom = 𝟙 _ := by
  rw [canonIso_hom, eqToHom_refl, Category.id_comp, FRC.hom_inv_app]
  rfl

theorem canon_comp (q : X ⟶ Y) (M : Y.Modules) (r : P ⟶ Y) (g₁ g₂ g₃ : P ⟶ X) (h₁ : g₁ ≫ q = r) (h₂ : g₂ ≫ q = r)
    (h₃ : g₃ ≫ q = r) :
    (canonIso q M r g₁ g₂ h₁ h₂).hom ≫ (canonIso q M r g₂ g₃ h₂ h₃).hom = (canonIso q M r g₁ g₃ h₁ h₃).hom := by
  have C := FRC.inv_hom_app (Scheme.Modules.pullbackComp g₂ q) M
  rw [canonIso_hom, canonIso_hom, canonIso_hom]
  dsimp only [Functor.comp_obj] at C ⊢
  simp only [Category.assoc]
  rw [reassoc_of% C, eqToHom_trans_assoc]

theorem canon_pull (q : X ⟶ Y) (M : Y.Modules) (p₁ p₂ : P ⟶ X) (hp : p₁ ≫ q = p₂ ≫ q)
    (g : Z ⟶ P) (gf₁ gf₂ : Z ⟶ X) (hg₁ : g ≫ p₁ = gf₁) (hg₂ : g ≫ p₂ = gf₂) :
      (Scheme.Modules.pullbackCongr hg₁).inv.app ((Scheme.Modules.pullback q).obj M) ≫ (Scheme.Modules.pullbackComp g p₁).inv.app ((Scheme.Modules.pullback q).obj M) ≫
        (Scheme.Modules.pullback g).map (canonIso q M (p₁ ≫ q) p₁ p₂ rfl hp.symm).hom ≫
        (Scheme.Modules.pullbackComp g p₂).hom.app ((Scheme.Modules.pullback q).obj M) ≫ (Scheme.Modules.pullbackCongr hg₂).hom.app ((Scheme.Modules.pullback q).obj M) =
        (canonIso q M (g ≫ p₁ ≫ q) gf₁ gf₂ (by rw [← hg₁, Category.assoc]) (by rw [← hg₂, Category.assoc, hp])).hom := by
  subst hg₁ hg₂
  have e1 : (Scheme.Modules.pullbackCongr (rfl : g ≫ p₁ = g ≫ p₁)).inv.app ((Scheme.Modules.pullback q).obj M) = 𝟙 _ := by
    simp [Scheme.Modules.pullbackCongr]
  have e2 : (Scheme.Modules.pullbackCongr (rfl : g ≫ p₂ = g ≫ p₂)).hom.app ((Scheme.Modules.pullback q).obj M) = 𝟙 _ := by
    simp [Scheme.Modules.pullbackCongr]
  have hE : (Scheme.Modules.pullback (p₁ ≫ q)).obj M = (Scheme.Modules.pullback (p₂ ≫ q)).obj M := by rw [hp]
  rw [e1, e2, Category.id_comp, canonIso_hom, canonIso_hom]
  have hm := (Scheme.Modules.pullback g).map_comp ((Scheme.Modules.pullbackComp p₁ q).hom.app M)
    (eqToHom hE ≫ (Scheme.Modules.pullbackComp p₂ q).inv.app M)
  have hm2 := (Scheme.Modules.pullback g).map_comp (eqToHom hE) ((Scheme.Modules.pullbackComp p₂ q).inv.app M)
  have hem := eqToHom_map (Scheme.Modules.pullback g) hE
  dsimp only [Functor.comp_obj] at hm hm2 hem ⊢
  rw [hm, hm2, hem]
  simp only [Category.assoc, Category.comp_id]
  have s1 := FRC.star1 g p₁ q M
  have s2 := FRC.star2 g p₂ q M
  have mid := FRC.comp_inv_eqToHom_comp_hom g hp M
  dsimp only [Functor.comp_obj, FRC.sa] at s1 s2 mid ⊢
  rw [reassoc_of% s1, s2, reassoc_of% mid]

end G1C

noncomputable section

section G1ScalarPart
namespace G1ScalarPart
variable {X Y : Scheme.{u}}

noncomputable abbrev resTop (r : Γ(X, ⊤)) (U : X.Opens) : Γ(X, U) :=
  X.presheaf.map (homOfLE (le_top (a := U))).op r

noncomputable def smulLin (r : Γ(X, ⊤)) (P : X.Modules) (U : X.Opens) : Γ(P, U) →ₗ[Γ(X, U)] Γ(P, U) :=
  DistribSMul.toLinearMap Γ(X, U) Γ(P, U) (resTop r U)

@[scoped simp] theorem smulLin_apply (r : Γ(X, ⊤)) (P : X.Modules) (U : X.Opens) (s : Γ(P, U)) :
    smulLin r P U s = resTop r U • s := rfl

theorem smul_eq (P : X.Modules) (U : (Opens X)ᵒᵖ) (a : X.ringCatSheaf.obj.obj U) (x : P.val.obj U) :
    (show Γ(P, U.unop) from (a • x : P.val.obj U)) =
      (show Γ(X, U.unop) from a) • (show Γ(P, U.unop) from x) := rfl

noncomputable def scalarEnd (r : Γ(X, ⊤)) (P : X.Modules) : P ⟶ P :=
  ⟨PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom (smulLin r P U.unop).toAddMonoidHom
      naturality := by
        intro U V i
        ext s
        change (resTop r V.unop • (show Γ(P, V.unop) from P.presheaf.map i (show Γ(P, U.unop) from s)) :
            Γ(P, V.unop)) =
          (show Γ(P, V.unop) from P.presheaf.map i (resTop r U.unop • (show Γ(P, U.unop) from s)))
        have hi : i = (i.unop).op := rfl
        rw [hi, Scheme.Modules.map_smul, ← CategoryTheory.comp_apply, ← X.presheaf.map_comp]
        rfl }
    (fun U a x => by
      change resTop r U.unop • (show Γ(P, U.unop) from (a • x : P.val.obj U)) =
        (show Γ(P, U.unop) from (a • (show P.val.obj U from resTop r U.unop • (show Γ(P, U.unop) from x)) :
          P.val.obj U))
      rw [smul_eq, smul_eq, smul_smul, smul_smul, mul_comm])⟩

theorem scalarEnd_app (r : Γ(X, ⊤)) (P : X.Modules) (U : X.Opens) (s : Γ(P, U)) :
    (scalarEnd r P).app U s = resTop r U • s := rfl

@[reassoc]
theorem scalarEnd_comm {P Q : X.Modules} (r : Γ(X, ⊤)) (f : P ⟶ Q) :
    scalarEnd r P ≫ f = f ≫ scalarEnd r Q := by
  ext U s
  change f.app U (resTop r U • (show Γ(P, U) from s)) = resTop r U • f.app U (show Γ(P, U) from s)
  exact Scheme.Modules.Hom.app_smul f (resTop r U) _

theorem scalarEnd_one (P : X.Modules) : scalarEnd (1 : Γ(X, ⊤)) P = 𝟙 P := by
  ext U s
  change resTop (1 : Γ(X, ⊤)) U • (show Γ(P, U) from s) = s
  rw [show resTop (1 : Γ(X, ⊤)) U = 1 from map_one _, one_smul]

theorem scalarEnd_mul (r r' : Γ(X, ⊤)) (P : X.Modules) : scalarEnd (r * r') P = scalarEnd r' P ≫ scalarEnd r P := by
  ext U s
  change resTop (r * r') U • (show Γ(P, U) from s) = resTop r U • (resTop r' U • (show Γ(P, U) from s))
  rw [show resTop (r * r') U = resTop r U * resTop r' U from map_mul _ _ _, mul_smul]

theorem eq_scalarEnd_of_app (P : X.Modules) (u : Γ(X, ⊤)) (σ : P ⟶ P)
    (hσ : ∀ (U : X.Opens) (s : Γ(P, U)), σ.app U s = (X.presheaf.map (homOfLE (le_top (a := U))).op u) • s) :
    σ = scalarEnd u P := by
  ext U s
  exact hσ U s

theorem app_resTop {X' : Scheme.{u}} (g : X' ⟶ X) (r : Γ(X, ⊤)) (U : X.Opens) :
    g.app U (resTop r U) = resTop (g.appTop r) (g ⁻¹ᵁ U) := by
  unfold resTop
  rw [← CategoryTheory.comp_apply, g.naturality]
  rfl

theorem pullback_map_scalarEnd {X' : Scheme.{u}} (g : X' ⟶ X) (r : Γ(X, ⊤)) (P : X.Modules) :
    (Scheme.Modules.pullback g).map (scalarEnd r P) = scalarEnd (g.appTop r) ((Scheme.Modules.pullback g).obj P) := by
  apply Scheme.Modules.pullback_hom_ext g
  intro U s
  rw [← Scheme.Modules.pullbackLocalSection_app, scalarEnd_app, Scheme.Modules.pullbackLocalSection_smul,
    scalarEnd_app, app_resTop]

end G1ScalarPart
p2m_reactivate "P2MW.S_AlgebraicGeometry_DescentCharacter_pullback_map_sectionScalar_comp_canonical_unit_and_cocycle.G1ScalarPart"
end G1ScalarPart
p2m_reactivate "P2MW.S_AlgebraicGeometry_DescentCharacter_pullback_map_sectionScalar_comp_canonical_unit_and_cocycle.G1ScalarPart"

namespace G1Sol

set_option maxHeartbeats 1600000 in
theorem main
    {X Y P P₃ : Scheme.{u}} (q : X ⟶ Y)
    (p₁ p₂ : P ⟶ X) (hp : p₁ ≫ q = p₂ ≫ q)
    (δ : X ⟶ P) (hδ₁ : δ ≫ p₁ = 𝟙 X) (hδ₂ : δ ≫ p₂ = 𝟙 X)
    (a b : P₃ ⟶ P) (hab : a ≫ p₂ = b ≫ p₁) (c : P₃ ⟶ P) (hca : c ≫ p₁ = a ≫ p₁) (hcb : c ≫ p₂ = b ≫ p₂)
    (M : Y.Modules) (u : Γ(P, ⊤)) (hu₁ : δ.appTop u = 1) (hu₂ : a.appTop u * b.appTop u = c.appTop u)
    (σ : (Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback q).obj M) ⟶
      (Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback q).obj M))
    (hσ : ∀ (U : P.Opens) (s : Γ((Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback q).obj M), U)),
      σ.app U s = (P.presheaf.map (homOfLE (le_top (a := U))).op u) • s) :
    let φ : (Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback q).obj M) ⟶
        (Scheme.Modules.pullback p₂).obj ((Scheme.Modules.pullback q).obj M) :=
      σ ≫ ((Scheme.Modules.pullbackComp p₁ q).hom.app M ≫
        eqToHom (show (Scheme.Modules.pullback (p₁ ≫ q)).obj M = (Scheme.Modules.pullback (p₂ ≫ q)).obj M by
          rw [hp]) ≫
        (Scheme.Modules.pullbackComp p₂ q).inv.app M)
    ((Scheme.Modules.pullbackCongr hδ₁).inv.app ((Scheme.Modules.pullback q).obj M) ≫
        (Scheme.Modules.pullbackComp δ p₁).inv.app ((Scheme.Modules.pullback q).obj M) ≫
          (Scheme.Modules.pullback δ).map φ ≫
            (Scheme.Modules.pullbackComp δ p₂).hom.app ((Scheme.Modules.pullback q).obj M) ≫
              (Scheme.Modules.pullbackCongr hδ₂).hom.app ((Scheme.Modules.pullback q).obj M) = 𝟙 _) ∧
    (((Scheme.Modules.pullbackComp a p₁).inv.app ((Scheme.Modules.pullback q).obj M) ≫
        (Scheme.Modules.pullback a).map φ ≫
          (Scheme.Modules.pullbackComp a p₂).hom.app ((Scheme.Modules.pullback q).obj M)) ≫
      ((Scheme.Modules.pullbackCongr hab).hom.app ((Scheme.Modules.pullback q).obj M) ≫
        (Scheme.Modules.pullbackComp b p₁).inv.app ((Scheme.Modules.pullback q).obj M) ≫
          (Scheme.Modules.pullback b).map φ ≫
            (Scheme.Modules.pullbackComp b p₂).hom.app ((Scheme.Modules.pullback q).obj M)) =
      (Scheme.Modules.pullbackCongr hca).inv.app ((Scheme.Modules.pullback q).obj M) ≫
        (Scheme.Modules.pullbackComp c p₁).inv.app ((Scheme.Modules.pullback q).obj M) ≫
          (Scheme.Modules.pullback c).map φ ≫
            (Scheme.Modules.pullbackComp c p₂).hom.app ((Scheme.Modules.pullback q).obj M) ≫
              (Scheme.Modules.pullbackCongr hcb).hom.app ((Scheme.Modules.pullback q).obj M)) := by
  intro φ
  have hσ' : σ = G1ScalarPart.scalarEnd u ((Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback q).obj M)) :=
    G1ScalarPart.eq_scalarEnd_of_app _ u σ hσ
  have hφ : φ = G1ScalarPart.scalarEnd u ((Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback q).obj M)) ≫
      (G1C.canonIso q M (p₁ ≫ q) p₁ p₂ rfl hp.symm).hom := by
    dsimp only [φ]
    rw [hσ', G1C.canonIso_hom]

  have key : ∀ {Z : Scheme.{u}} (g : Z ⟶ P) (gf₁ gf₂ : Z ⟶ X) (hg₁ : g ≫ p₁ = gf₁) (hg₂ : g ≫ p₂ = gf₂),
      (Scheme.Modules.pullbackCongr hg₁).inv.app ((Scheme.Modules.pullback q).obj M) ≫ (Scheme.Modules.pullbackComp g p₁).inv.app ((Scheme.Modules.pullback q).obj M) ≫
        (Scheme.Modules.pullback g).map φ ≫ (Scheme.Modules.pullbackComp g p₂).hom.app ((Scheme.Modules.pullback q).obj M) ≫
          (Scheme.Modules.pullbackCongr hg₂).hom.app ((Scheme.Modules.pullback q).obj M) =
        G1ScalarPart.scalarEnd (g.appTop u) ((Scheme.Modules.pullback gf₁).obj ((Scheme.Modules.pullback q).obj M)) ≫
          (G1C.canonIso q M (g ≫ p₁ ≫ q) gf₁ gf₂ (by rw [← hg₁, Category.assoc]) (by rw [← hg₂, Category.assoc, hp])).hom := by
    intro Z g gf₁ gf₂ hg₁ hg₂
    have hD := G1C.canon_pull q M p₁ p₂ hp g gf₁ gf₂ hg₁ hg₂
    have hm := (Scheme.Modules.pullback g).map_comp (G1ScalarPart.scalarEnd u ((Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback q).obj M)))
      (G1C.canonIso q M (p₁ ≫ q) p₁ p₂ rfl hp.symm).hom
    rw [hφ]
    dsimp only [Functor.comp_obj] at hD hm ⊢
    rw [hm, G1ScalarPart.pullback_map_scalarEnd]
    rw [Category.assoc, ← G1ScalarPart.scalarEnd_comm_assoc, ← G1ScalarPart.scalarEnd_comm_assoc, hD]
  constructor
  ·
    rw [key δ (𝟙 X) (𝟙 X) hδ₁ hδ₂, hu₁, G1ScalarPart.scalarEnd_one, Category.id_comp]
    exact G1C.canon_self _ _ _ _ _
  ·
    have e1 : (Scheme.Modules.pullbackCongr (rfl : a ≫ p₁ = a ≫ p₁)).inv.app ((Scheme.Modules.pullback q).obj M) = 𝟙 _ := by
      simp [Scheme.Modules.pullbackCongr]
    have e2 : (Scheme.Modules.pullbackCongr (rfl : a ≫ p₂ = a ≫ p₂)).hom.app ((Scheme.Modules.pullback q).obj M) = 𝟙 _ := by
      simp [Scheme.Modules.pullbackCongr]
    have e3 : (Scheme.Modules.pullbackCongr (rfl : b ≫ p₂ = b ≫ p₂)).hom.app ((Scheme.Modules.pullback q).obj M) = 𝟙 _ := by
      simp [Scheme.Modules.pullbackCongr]
    have e4 : (Scheme.Modules.pullbackCongr hab.symm).inv.app ((Scheme.Modules.pullback q).obj M) =
        (Scheme.Modules.pullbackCongr hab).hom.app ((Scheme.Modules.pullback q).obj M) := by
      simp [Scheme.Modules.pullbackCongr]
    have hA := key a (a ≫ p₁) (a ≫ p₂) rfl rfl
    have hB := key b (a ≫ p₂) (b ≫ p₂) hab.symm rfl
    have hC := key c (a ≫ p₁) (b ≫ p₂) hca hcb
    rw [e1, e2, Category.id_comp] at hA
    rw [e3, e4] at hB
    simp only [Category.comp_id] at hA hB
    rw [hC]
    slice_lhs 1 3 => rw [hA]
    simp only [Category.assoc]
    rw [hB]
    try dsimp only [Functor.comp_obj]
    rw [← G1ScalarPart.scalarEnd_comm_assoc, ← Category.assoc, ← G1ScalarPart.scalarEnd_mul, mul_comm, hu₂]
    congr 1
    have hq : b ≫ p₁ ≫ q = a ≫ p₁ ≫ q := by rw [← Category.assoc, ← hab, Category.assoc, ← hp]
    have h1 := G1C.canon_comp q M (a ≫ p₁ ≫ q) (a ≫ p₁) (a ≫ p₂) (b ≫ p₂)
      (by rw [Category.assoc]) (by rw [Category.assoc, hp]) (by rw [← hq, Category.assoc, hp])
    convert h1 using 4 <;> first | rfl | exact hq | exact hq.symm

end G1Sol
p2m_reactivate "P2MW.S_AlgebraicGeometry_DescentCharacter_pullback_map_sectionScalar_comp_canonical_unit_and_cocycle.G1ScalarPart"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_DescentCharacter_pullback_map_sectionScalar_comp_canonical_unit_and_cocycle.G1ScalarPart"

theorem solution
    {X Y P P₃ : Scheme.{u}} (q : X ⟶ Y)
    (p₁ p₂ : P ⟶ X) (hp : p₁ ≫ q = p₂ ≫ q)
    (δ : X ⟶ P) (hδ₁ : δ ≫ p₁ = 𝟙 X) (hδ₂ : δ ≫ p₂ = 𝟙 X)
    (a b : P₃ ⟶ P) (hab : a ≫ p₂ = b ≫ p₁) (c : P₃ ⟶ P) (hca : c ≫ p₁ = a ≫ p₁) (hcb : c ≫ p₂ = b ≫ p₂)
    (M : Y.Modules) (u : Γ(P, ⊤)) (hu₁ : δ.appTop u = 1) (hu₂ : a.appTop u * b.appTop u = c.appTop u)
    (σ : (Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback q).obj M) ⟶
      (Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback q).obj M))
    (hσ : ∀ (U : P.Opens) (s : Γ((Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback q).obj M), U)),
      σ.app U s = (P.presheaf.map (homOfLE (le_top (a := U))).op u) • s) :
    let φ : (Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback q).obj M) ⟶
        (Scheme.Modules.pullback p₂).obj ((Scheme.Modules.pullback q).obj M) :=
      σ ≫ ((Scheme.Modules.pullbackComp p₁ q).hom.app M ≫
        eqToHom (show (Scheme.Modules.pullback (p₁ ≫ q)).obj M = (Scheme.Modules.pullback (p₂ ≫ q)).obj M by
          rw [hp]) ≫
        (Scheme.Modules.pullbackComp p₂ q).inv.app M)
    ((Scheme.Modules.pullbackCongr hδ₁).inv.app ((Scheme.Modules.pullback q).obj M) ≫
        (Scheme.Modules.pullbackComp δ p₁).inv.app ((Scheme.Modules.pullback q).obj M) ≫
          (Scheme.Modules.pullback δ).map φ ≫
            (Scheme.Modules.pullbackComp δ p₂).hom.app ((Scheme.Modules.pullback q).obj M) ≫
              (Scheme.Modules.pullbackCongr hδ₂).hom.app ((Scheme.Modules.pullback q).obj M) = 𝟙 _) ∧
    (((Scheme.Modules.pullbackComp a p₁).inv.app ((Scheme.Modules.pullback q).obj M) ≫
        (Scheme.Modules.pullback a).map φ ≫
          (Scheme.Modules.pullbackComp a p₂).hom.app ((Scheme.Modules.pullback q).obj M)) ≫
      ((Scheme.Modules.pullbackCongr hab).hom.app ((Scheme.Modules.pullback q).obj M) ≫
        (Scheme.Modules.pullbackComp b p₁).inv.app ((Scheme.Modules.pullback q).obj M) ≫
          (Scheme.Modules.pullback b).map φ ≫
            (Scheme.Modules.pullbackComp b p₂).hom.app ((Scheme.Modules.pullback q).obj M)) =
      (Scheme.Modules.pullbackCongr hca).inv.app ((Scheme.Modules.pullback q).obj M) ≫
        (Scheme.Modules.pullbackComp c p₁).inv.app ((Scheme.Modules.pullback q).obj M) ≫
          (Scheme.Modules.pullback c).map φ ≫
            (Scheme.Modules.pullbackComp c p₂).hom.app ((Scheme.Modules.pullback q).obj M) ≫
              (Scheme.Modules.pullbackCongr hcb).hom.app ((Scheme.Modules.pullback q).obj M)) :=
  G1Sol.main q p₁ p₂ hp δ hδ₁ hδ₂ a b hab c hca hcb M u hu₁ hu₂ σ hσ

end S_AlgebraicGeometry_DescentCharacter_pullback_map_sectionScalar_comp_canonical_unit_and_cocycle
end P2MW
export P2MW.S_AlgebraicGeometry_DescentCharacter_pullback_map_sectionScalar_comp_canonical_unit_and_cocycle (solution)
