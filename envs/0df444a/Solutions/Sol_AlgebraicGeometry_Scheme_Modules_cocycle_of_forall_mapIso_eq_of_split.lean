-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.cocycle_of_forall_mapIso_eq_of_split
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/758b32f8-17b0-56c9-b3ee-2e0fc3a607b4

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_toDescentData_map_bijective_of_openCover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_cocycle_of_forall_mapIso_eq_of_split

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Loc
set_option backward.isDefEq.respectTransparency false

universe u
variable {X : Scheme.{u}}

open _root_.AlgebraicGeometry.Scheme.Modules in
theorem pullbackCongr_hom_app {Y : Scheme.{u}} {b c : Y ⟶ X} (h : b = c) (N : X.Modules) :
    (Scheme.Modules.pullbackCongr h).hom.app N = eqToHom (by rw [h]) := by
  subst h
  simp [Scheme.Modules.pullbackCongr]

theorem pullbackCongr_inv_app {Y : Scheme.{u}} {b c : Y ⟶ X} (h : b = c) (N : X.Modules) :
    (Scheme.Modules.pullbackCongr h).inv.app N = eqToHom (by rw [h]) := by
  subst h
  simp [Scheme.Modules.pullbackCongr]

theorem pullbackComp_assoc_app {W Y Z : Scheme.{u}} (f : W ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ X) (N : X.Modules) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app N) ≫
        (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app N =
      (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj N) ≫
        (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app N ≫ eqToHom (by rw [Category.assoc]) := by
  have H := NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity f g h) N
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    eqToHom_app, Category.id_comp] at H

  rw [← cancel_epi ((Scheme.Modules.pullbackComp f (g ≫ h)).inv.app N ≫
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).inv.app N))]
  rw [Category.assoc, Category.assoc, ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id_app, reassoc_of% H, eqToHom_trans, eqToHom_refl]

theorem map_pullbackId_inv_comp_pullbackComp {Y : Scheme.{u}} (f : Y ⟶ X) (N : X.Modules) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackId X).inv.app N) ≫
        (Scheme.Modules.pullbackComp f (𝟙 X)).hom.app N = eqToHom (by simp) := by
  have H := NatTrans.congr_app (Scheme.Modules.pseudofunctor_left_unitality f) N
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app, eqToHom_app] at H

  rw [← cancel_epi ((Scheme.Modules.pullbackComp f (𝟙 X)).inv.app N ≫
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackId X).hom.app N))]
  rw [Category.assoc, Category.assoc, ← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id_app, reassoc_of% H, eqToHom_trans, eqToHom_refl]

variable (M : X.Modules)

noncomputable def loc {V : Scheme.{u}} (f₁ f₂ : V ⟶ X) (T : X ⟶ X) (ψ : M ≅ (Scheme.Modules.pullback T).obj M)
    (e : f₁ ≫ T = f₂) :
    (Scheme.Modules.pullback f₁).obj M ⟶ (Scheme.Modules.pullback f₂).obj M :=
  (Scheme.Modules.pullback f₁).map ψ.hom ≫ (Scheme.Modules.pullbackComp f₁ T).hom.app M ≫
    (Scheme.Modules.pullbackCongr e).hom.app M

theorem loc_def {V : Scheme.{u}} (f₁ f₂ : V ⟶ X) (T : X ⟶ X) (ψ : M ≅ (Scheme.Modules.pullback T).obj M)
    (e : f₁ ≫ T = f₂) :
    loc M f₁ f₂ T ψ e = (Scheme.Modules.pullback f₁).map ψ.hom ≫ (Scheme.Modules.pullbackComp f₁ T).hom.app M ≫
      (Scheme.Modules.pullbackCongr e).hom.app M := rfl

theorem loc_baseChange {V V' : Scheme.{u}} (w : V' ⟶ V) (f₁ f₂ : V ⟶ X) (T : X ⟶ X)
    (ψ : M ≅ (Scheme.Modules.pullback T).obj M) (e : f₁ ≫ T = f₂) (e' : (w ≫ f₁) ≫ T = w ≫ f₂) :
    (Scheme.Modules.pullback w).map (loc M f₁ f₂ T ψ e) =
      (Scheme.Modules.pullbackComp w f₁).hom.app M ≫ loc M (w ≫ f₁) (w ≫ f₂) T ψ e' ≫
        (Scheme.Modules.pullbackComp w f₂).inv.app M := by
  subst e
  rw [← cancel_mono ((Scheme.Modules.pullbackComp w (f₁ ≫ T)).hom.app M)]
  simp only [loc, pullbackCongr_hom_app, eqToHom_refl, Category.comp_id, Category.assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_comp]
  rw [pullbackComp_assoc_app, ← NatTrans.naturality_assoc]
  rfl

theorem loc_unit (T₀ : X ⟶ X) (e₀ : T₀ = 𝟙 X) (ψ₀ : M ≅ (Scheme.Modules.pullback T₀).obj M)
    (hψ₀ : ψ₀ = ((Scheme.Modules.pullbackId X).app M).symm ≪≫ ((Scheme.Modules.pullbackCongr e₀).app M).symm)
    {V : Scheme.{u}} (f : V ⟶ X) (e : f ≫ T₀ = f) : loc M f f T₀ ψ₀ e = 𝟙 _ := by
  subst e₀ hψ₀
  simp only [loc, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, pullbackCongr_hom_app, pullbackCongr_inv_app, eqToHom_refl,
    Category.comp_id]
  rw [map_pullbackId_inv_comp_pullbackComp]
  simp only [eqToHom_refl]
  rfl

theorem loc_comp (Tg Th Tgh : X ⟶ X) (emul : Tgh = Tg ≫ Th)
    (ψg : M ≅ (Scheme.Modules.pullback Tg).obj M) (ψh : M ≅ (Scheme.Modules.pullback Th).obj M)
    (ψgh : M ≅ (Scheme.Modules.pullback Tgh).obj M)
    (hmul : ψgh = ψg ≪≫ (Scheme.Modules.pullback Tg).mapIso ψh ≪≫ (Scheme.Modules.pullbackComp Tg Th).app M ≪≫
      ((Scheme.Modules.pullbackCongr emul).app M).symm)
    {V : Scheme.{u}} (f₁ f₂ f₃ : V ⟶ X) (e₁₂ : f₁ ≫ Tg = f₂) (e₂₃ : f₂ ≫ Th = f₃) (e₁₃ : f₁ ≫ Tgh = f₃) :
    loc M f₁ f₂ Tg ψg e₁₂ ≫ loc M f₂ f₃ Th ψh e₂₃ = loc M f₁ f₃ Tgh ψgh e₁₃ := by
  subst emul hmul e₁₂ e₂₃
  simp only [loc, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv, pullbackCongr_hom_app,
    pullbackCongr_inv_app, eqToHom_refl, Category.comp_id, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [pullbackComp_assoc_app]
  simp only [eqToHom_refl, Category.comp_id]
  rw [← NatTrans.naturality_assoc]
  rfl

end Loc

namespace Loc

universe u
variable {X : Scheme.{u}}

theorem mapComp'_hom_app {V V' : Scheme.{u}} (f₁ : V ⟶ X) (w : V' ⟶ V) (N : X.Modules)
    (h : f₁.op.toLoc ≫ w.op.toLoc = (w ≫ f₁).op.toLoc) :
    (((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).mapComp' f₁.op.toLoc w.op.toLoc (w ≫ f₁).op.toLoc h).hom.toNatTrans.app N =
      (Scheme.Modules.pullbackComp w f₁).inv.app N := by
  simp [Pseudofunctor.mapComp', Scheme.Modules.pseudofunctor, Pseudofunctor.comp, Bicategory.Adj.forget₁,
    LocallyDiscrete.mkPseudofunctor]
  rfl

theorem mapComp'_inv_app {V V' : Scheme.{u}} (f₁ : V ⟶ X) (w : V' ⟶ V) (N : X.Modules)
    (h : f₁.op.toLoc ≫ w.op.toLoc = (w ≫ f₁).op.toLoc) :
    (((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).mapComp' f₁.op.toLoc w.op.toLoc (w ≫ f₁).op.toLoc h).inv.toNatTrans.app N =
      (Scheme.Modules.pullbackComp w f₁).hom.app N := by
  simp [Pseudofunctor.mapComp', Scheme.Modules.pseudofunctor, Pseudofunctor.comp, Bicategory.Adj.forget₁,
    LocallyDiscrete.mkPseudofunctor]
  rfl

theorem map_eq_loc (M : X.Modules) {V V' : Scheme.{u}} (w : V' ⟶ V) (f₁ f₂ : V ⟶ X) (T : X ⟶ X)
    (ψ : M ≅ (Scheme.Modules.pullback T).obj M) (e : f₁ ≫ T = f₂) (e' : (w ≫ f₁) ≫ T = w ≫ f₂)
    (h₁ : f₁.op.toLoc ≫ w.op.toLoc = (w ≫ f₁).op.toLoc) (h₂ : f₂.op.toLoc ≫ w.op.toLoc = (w ≫ f₂).op.toLoc) :
    (((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).map w.op.toLoc).toFunctor.map (loc M f₁ f₂ T ψ e) =
      (((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).mapComp' f₁.op.toLoc w.op.toLoc (w ≫ f₁).op.toLoc h₁).inv.toNatTrans.app M ≫
        loc M (w ≫ f₁) (w ≫ f₂) T ψ e' ≫
      (((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).mapComp' f₂.op.toLoc w.op.toLoc (w ≫ f₂).op.toLoc h₂).hom.toNatTrans.app M := by
  rw [mapComp'_hom_app, mapComp'_inv_app]
  exact loc_baseChange M w f₁ f₂ T ψ e e'

theorem pullHom_loc (M : X.Modules) {V V' : Scheme.{u}} (w : V' ⟶ V) (f₁ f₂ : V ⟶ X) (T : X ⟶ X)
    (ψ : M ≅ (Scheme.Modules.pullback T).obj M) (e : f₁ ≫ T = f₂)
    (wf₁ wf₂ : V' ⟶ X) (hw₁ : w ≫ f₁ = wf₁) (hw₂ : w ≫ f₂ = wf₂) (e'' : wf₁ ≫ T = wf₂) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := (Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁) (M₁ := M) (M₂ := M)
        (f₁ := f₁) (f₂ := f₂) (loc M f₁ f₂ T ψ e) w wf₁ wf₂ hw₁ hw₂ =
      loc M wf₁ wf₂ T ψ e'' := by
  subst hw₁ hw₂
  delta Pseudofunctor.LocallyDiscreteOpToCat.pullHom
  rw [mapComp'_hom_app, mapComp'_inv_app]
  change (Scheme.Modules.pullbackComp w f₁).inv.app M ≫ (Scheme.Modules.pullback w).map (loc M f₁ f₂ T ψ e) ≫
    (Scheme.Modules.pullbackComp w f₂).hom.app M = _
  rw [loc_baseChange M w f₁ f₂ T ψ e e'']
  change (Scheme.Modules.pullbackComp w f₁).inv.app M ≫ ((Scheme.Modules.pullbackComp w f₁).hom.app M ≫
      loc M (w ≫ f₁) (w ≫ f₂) T ψ e'' ≫ (Scheme.Modules.pullbackComp w f₂).inv.app M) ≫
    (Scheme.Modules.pullbackComp w f₂).hom.app M = loc M (w ≫ f₁) (w ≫ f₂) T ψ e''
  simp only [Category.assoc, Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc, Category.comp_id]

end Loc

namespace Loc
set_option backward.isDefEq.respectTransparency false

universe u

open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat in

theorem restrict_piece {X X'' Ug W W' : Scheme.{u}} (M : X.Modules) (a₁ a₂ : X'' ⟶ X) (T : X ⟶ X)
    (ψ : M ≅ (Scheme.Modules.pullback T).obj M)
    (Φ : (Scheme.Modules.pullback a₁).obj M ⟶ (Scheme.Modules.pullback a₂).obj M)
    (ιg : Ug ⟶ X'') (eg : (ιg ≫ a₁) ≫ T = ιg ≫ a₂)
    (piece : pullHom (F := (Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁) (M₁ := M) (M₂ := M)
      (f₁ := a₁) (f₂ := a₂) Φ ιg (ιg ≫ a₁) (ιg ≫ a₂) rfl rfl = Loc.loc M (ιg ≫ a₁) (ιg ≫ a₂) T ψ eg)
    (w : W ⟶ X'') (hw : (w ≫ a₁) ≫ T = w ≫ a₂) (ι : W' ⟶ W) (w' : W' ⟶ Ug) (hfac : ι ≫ w = w' ≫ ιg)
    (e : (ι ≫ w ≫ a₁) ≫ T = ι ≫ w ≫ a₂) :
    pullHom (F := (Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁)
        (pullHom (F := (Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁) (M₁ := M) (M₂ := M)
          (f₁ := a₁) (f₂ := a₂) Φ w (w ≫ a₁) (w ≫ a₂) rfl rfl)
        ι (ι ≫ w ≫ a₁) (ι ≫ w ≫ a₂) rfl rfl =
      Loc.loc M (ι ≫ w ≫ a₁) (ι ≫ w ≫ a₂) T ψ e := by
  rw [pullHom_pullHom (F := (Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁) (M₁ := M) (M₂ := M)
    (f₁ := a₁) (f₂ := a₂) Φ w (w ≫ a₁) (w ≫ a₂) ι (ι ≫ w ≫ a₁) (ι ≫ w ≫ a₂) rfl rfl
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm]

  have key : ∀ (v : W' ⟶ X'') (hv : v = w' ≫ ιg) (p₁ : v ≫ a₁ = ι ≫ w ≫ a₁) (p₂ : v ≫ a₂ = ι ≫ w ≫ a₂),
      pullHom (F := (Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁) (M₁ := M) (M₂ := M)
        (f₁ := a₁) (f₂ := a₂) Φ v (ι ≫ w ≫ a₁) (ι ≫ w ≫ a₂) p₁ p₂ =
      Loc.loc M (ι ≫ w ≫ a₁) (ι ≫ w ≫ a₂) T ψ e := by
    intro v hv p₁ p₂
    subst hv
    rw [← pullHom_pullHom (F := (Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁) (M₁ := M) (M₂ := M)
      (f₁ := a₁) (f₂ := a₂) Φ ιg (ιg ≫ a₁) (ιg ≫ a₂) w' (ι ≫ w ≫ a₁) (ι ≫ w ≫ a₂) rfl rfl
      (by rw [← Category.assoc, p₁]) (by rw [← Category.assoc, p₂]), piece]
    exact pullHom_loc M w' (ιg ≫ a₁) (ιg ≫ a₂) T ψ eg _ _ _ _ e
  exact key (ι ≫ w) hfac (Category.assoc _ _ _) (Category.assoc _ _ _)

end Loc

namespace Loc
set_option backward.isDefEq.respectTransparency false

universe u

p2m_open "CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat"

theorem mapComp'_hom_app' {X V V' : Scheme.{u}} (f₁ : V ⟶ X) (w : V' ⟶ V) (wf : V' ⟶ X) (hw : w ≫ f₁ = wf)
    (N : X.Modules) (h : f₁.op.toLoc ≫ w.op.toLoc = wf.op.toLoc) :
    (((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).mapComp' f₁.op.toLoc w.op.toLoc wf.op.toLoc h).hom.toNatTrans.app N =
      (Scheme.Modules.pullbackCongr hw).inv.app N ≫ (Scheme.Modules.pullbackComp w f₁).inv.app N := by
  subst hw
  rw [mapComp'_hom_app, pullbackCongr_inv_app, eqToHom_refl, Category.id_comp]

theorem mapComp'_inv_app' {X V V' : Scheme.{u}} (f₁ : V ⟶ X) (w : V' ⟶ V) (wf : V' ⟶ X) (hw : w ≫ f₁ = wf)
    (N : X.Modules) (h : f₁.op.toLoc ≫ w.op.toLoc = wf.op.toLoc) :
    (((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).mapComp' f₁.op.toLoc w.op.toLoc wf.op.toLoc h).inv.toNatTrans.app N =
      (Scheme.Modules.pullbackComp w f₁).hom.app N ≫ (Scheme.Modules.pullbackCongr hw).hom.app N := by
  subst hw
  rw [mapComp'_inv_app, pullbackCongr_hom_app, eqToHom_refl, Category.comp_id]

theorem pullHom_eq {X₁ X₂ V V' : Scheme.{u}} {M₁ : X₁.Modules} {M₂ : X₂.Modules} {f₁ : V ⟶ X₁} {f₂ : V ⟶ X₂}
    (φ : (Scheme.Modules.pullback f₁).obj M₁ ⟶ (Scheme.Modules.pullback f₂).obj M₂)
    (w : V' ⟶ V) (wf₁ : V' ⟶ X₁) (wf₂ : V' ⟶ X₂) (h₁ : w ≫ f₁ = wf₁) (h₂ : w ≫ f₂ = wf₂) :
    pullHom (F := (Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁) (M₁ := M₁) (M₂ := M₂)
        (f₁ := f₁) (f₂ := f₂) φ w wf₁ wf₂ h₁ h₂ =
      (Scheme.Modules.pullbackCongr h₁).inv.app M₁ ≫ (Scheme.Modules.pullbackComp w f₁).inv.app M₁ ≫
        (Scheme.Modules.pullback w).map φ ≫
        (Scheme.Modules.pullbackComp w f₂).hom.app M₂ ≫ (Scheme.Modules.pullbackCongr h₂).hom.app M₂ := by
  delta Pseudofunctor.LocallyDiscreteOpToCat.pullHom
  rw [mapComp'_hom_app' f₁ w wf₁ h₁, mapComp'_inv_app' f₂ w wf₂ h₂]
  simp only [Category.assoc]
  rfl

variable {X : Scheme.{u}} (M : X.Modules)

theorem congr_loc_congr {V : Scheme.{u}} {f₁ f₁' f₂ f₂' : V ⟶ X} (p₁ : f₁' = f₁) (p₂ : f₂ = f₂') (T : X ⟶ X)
    (ψ : M ≅ (Scheme.Modules.pullback T).obj M) (e : f₁ ≫ T = f₂) (e' : f₁' ≫ T = f₂') :
    (Scheme.Modules.pullbackCongr p₁).hom.app M ≫ loc M f₁ f₂ T ψ e ≫ (Scheme.Modules.pullbackCongr p₂).hom.app M =
      loc M f₁' f₂' T ψ e' := by
  subst p₁ p₂
  simp only [pullbackCongr_hom_app, eqToHom_refl, Category.comp_id, Category.id_comp]

theorem pullHom_eq_loc_of_map_eq {X'' W : Scheme.{u}} (a₁ a₂ : X'' ⟶ X)
    (Ψ : (Scheme.Modules.pullback a₁).obj M ⟶ (Scheme.Modules.pullback a₂).obj M)
    (T : X ⟶ X) (ψ : M ≅ (Scheme.Modules.pullback T).obj M) (w : W ⟶ X'') (hw : (w ≫ a₁) ≫ T = w ≫ a₂)
    (hΨ : (Scheme.Modules.pullback w).map Ψ =
      (Scheme.Modules.pullbackComp w a₁).hom.app M ≫ loc M (w ≫ a₁) (w ≫ a₂) T ψ hw ≫
        (Scheme.Modules.pullbackComp w a₂).inv.app M)
    (wf₁ wf₂ : W ⟶ X) (h₁ : w ≫ a₁ = wf₁) (h₂ : w ≫ a₂ = wf₂) (e : wf₁ ≫ T = wf₂) :
    pullHom (F := (Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁) (M₁ := M) (M₂ := M)
        (f₁ := a₁) (f₂ := a₂) Ψ w wf₁ wf₂ h₁ h₂ = loc M wf₁ wf₂ T ψ e := by
  rw [pullHom_eq, hΨ]
  subst h₁ h₂
  simp only [pullbackCongr_hom_app, pullbackCongr_inv_app, eqToHom_refl, Category.comp_id, Category.id_comp,
    Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]

end Loc

namespace CoverCalc
set_option backward.isDefEq.respectTransparency false

section pullHom
open Opposite
universe v'' u'' v₃ u₃
variable {C : Type u₃} [Category.{v₃} C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v'', u''}}

theorem pullHom_id' ⦃X₁ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (h₁ h₂ : g ≫ f₁ = gf₁) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F)
      (𝟙 ((F.map f₁.op.toLoc).toFunctor.obj M₁)) g gf₁ gf₁ h₁ h₂ = 𝟙 _ := by
  delta Pseudofunctor.LocallyDiscreteOpToCat.pullHom
  rw [CategoryTheory.Functor.map_id]
  erw [Category.id_comp]
  rw [← Cat.Hom₂.comp_app, Iso.hom_inv_id, Cat.Hom₂.id_app]

theorem pullHom_comp' ⦃X₁ X₂ X₃ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄ ⦃M₃ : F.obj (.mk (op X₃))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄ ⦃f₃ : Y ⟶ X₃⦄
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (φ' : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶ (F.map f₃.op.toLoc).toFunctor.obj M₃)
    ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (gf₃ : Y' ⟶ X₃)
    (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) (h₃ : g ≫ f₃ = gf₃) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F) (φ ≫ φ') g gf₁ gf₃ h₁ h₃ =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F) φ g gf₁ gf₂ h₁ h₂ ≫
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F) φ' g gf₂ gf₃ h₂ h₃ := by
  delta Pseudofunctor.LocallyDiscreteOpToCat.pullHom
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← Cat.Hom₂.comp_app_assoc, Iso.inv_hom_id, Cat.Hom₂.id_app, Category.id_comp]

end pullHom

section opens
universe u
variable {Y : Scheme.{u}}

theorem iSup_inf_eq_top {ι κ : Type*} (U : ι → Y.Opens) (V : κ → Y.Opens)
    (hU : ⨆ i, U i = ⊤) (hV : ⨆ j, V j = ⊤) : ⨆ p : ι × κ, U p.1 ⊓ V p.2 = ⊤ := by
  rw [← iSup_inf_iSup, hU, hV, top_inf_eq]

theorem inf_inf_inf_eq_bot_of_ne {ι κ : Type*} (U : ι → Y.Opens) (V : κ → Y.Opens)
    (hU' : ∀ i i', i ≠ i' → U i ⊓ U i' = ⊥) (hV' : ∀ j j', j ≠ j' → V j ⊓ V j' = ⊥)
    (p p' : ι × κ) (hp : p ≠ p') : (U p.1 ⊓ V p.2) ⊓ (U p'.1 ⊓ V p'.2) = ⊥ := by
  by_cases h1 : p.1 = p'.1
  · have h2 : p.2 ≠ p'.2 := fun h2 => hp (Prod.ext h1 h2)
    apply le_bot_iff.mp
    calc (U p.1 ⊓ V p.2) ⊓ (U p'.1 ⊓ V p'.2) ≤ V p.2 ⊓ V p'.2 := inf_le_inf inf_le_right inf_le_right
      _ = ⊥ := hV' _ _ h2
  · apply le_bot_iff.mp
    calc (U p.1 ⊓ V p.2) ⊓ (U p'.1 ⊓ V p'.2) ≤ U p.1 ⊓ U p'.1 := inf_le_inf inf_le_left inf_le_left
      _ = ⊥ := hU' _ _ h1

theorem iSup_preimage_eq_top {Y' : Scheme.{u}} (g : Y' ⟶ Y) {ι : Type*} (U : ι → Y.Opens) (hU : ⨆ i, U i = ⊤) :
    ⨆ i, g ⁻¹ᵁ (U i) = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, hU, Scheme.Hom.preimage_top]

theorem preimage_inf_preimage_eq_bot {Y' : Scheme.{u}} (g : Y' ⟶ Y) (U V : Y.Opens) (h : U ⊓ V = ⊥) :
    g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V = ⊥ := by
  rw [← Scheme.Hom.preimage_inf, h, Scheme.Hom.preimage_bot]

end opens

end CoverCalc

namespace KPC
set_option backward.isDefEq.respectTransparency false

universe u v w

p2m_open "CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat"

theorem range_cover {Y : Scheme.{u}} {ι : Type w} (U : ι → Y.Opens) (hU : ⨆ i, U i = ⊤) :
    ∀ y : Y, ∃ i, y ∈ Set.range (U i).ι := by
  intro y
  have hy : y ∈ (⨆ i, U i : Y.Opens) := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  exact ⟨i, by rw [Scheme.Opens.range_ι]; exact hi⟩

theorem hom_ext_of_cover {Y : Scheme.{u}} {ι : Type w} (U : ι → Y.Opens) (hU : ⨆ i, U i = ⊤) {L₁ L₂ : Y.Modules}
    (Φ Φ' : L₁ ⟶ L₂)
    (h : ∀ i, (((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).map (U i).ι.op.toLoc).toFunctor.map Φ =
      (((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).map (U i).ι.op.toLoc).toFunctor.map Φ') : Φ = Φ' := by
  apply (AlgebraicGeometry.Scheme.Modules.toDescentData_map_bijective_of_openCover (fun i => (U i).ι)
    (range_cover U hU) L₁ L₂).1
  ext i
  exact h i

theorem hom_ext_pull {Y : Scheme.{u}} {ι : Type w} (U : ι → Y.Opens) (hU : ⨆ i, U i = ⊤)
    {X₁ X₂ : Scheme.{u}} {M₁ : X₁.Modules} {M₂ : X₂.Modules} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (Φ Φ' : (((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      (((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).map f₂.op.toLoc).toFunctor.obj M₂)
    (hΦ : ∀ i, pullHom Φ (U i).ι ((U i).ι ≫ f₁) ((U i).ι ≫ f₂) rfl rfl =
      pullHom Φ' (U i).ι ((U i).ι ≫ f₁) ((U i).ι ≫ f₂) rfl rfl) : Φ = Φ' := by
  apply hom_ext_of_cover U hU
  intro i
  rw [map_eq_pullHom Φ (U i).ι _ _ rfl rfl, map_eq_pullHom Φ' (U i).ι _ _ rfl rfl, hΦ i]

theorem iSup_inf_eq_top {Y : Scheme.{u}} {ι κ : Type w} (U : ι → Y.Opens) (V : κ → Y.Opens)
    (hU : ⨆ i, U i = ⊤) (hV : ⨆ j, V j = ⊤) : ⨆ p : ι × κ, U p.1 ⊓ V p.2 = ⊤ := by
  rw [← iSup_inf_iSup, hU, hV, top_inf_eq]

theorem iSup_preimage_eq_top {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) {ι : Type w} (U : ι → Y.Opens) (hU : ⨆ i, U i = ⊤) :
    ⨆ i, g ⁻¹ᵁ (U i) = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, hU, Scheme.Hom.preimage_top]

variable {X : Scheme.{u}} (M : X.Modules)

theorem map_hom_eq_of_mapIso_eq {X'' W : Scheme.{u}} (a₁ a₂ : X'' ⟶ X) (T : X ⟶ X)
    (ψ : M ≅ (Scheme.Modules.pullback T).obj M)
    (Ψ : (Scheme.Modules.pullback a₁).obj M ≅ (Scheme.Modules.pullback a₂).obj M) (w : W ⟶ X'')
    (hw : (w ≫ a₁) ≫ T = w ≫ a₂)
    (hΨ : (Scheme.Modules.pullback w).mapIso Ψ =
      (Scheme.Modules.pullbackComp w a₁).app M ≪≫ (Scheme.Modules.pullback (w ≫ a₁)).mapIso ψ ≪≫
        (Scheme.Modules.pullbackComp (w ≫ a₁) T).app M ≪≫ (Scheme.Modules.pullbackCongr hw).app M ≪≫
          ((Scheme.Modules.pullbackComp w a₂).app M).symm) :
    (Scheme.Modules.pullback w).map Ψ.hom =
      (Scheme.Modules.pullbackComp w a₁).hom.app M ≫ Loc.loc M (w ≫ a₁) (w ≫ a₂) T ψ hw ≫
        (Scheme.Modules.pullbackComp w a₂).inv.app M := by
  have := congrArg Iso.hom hΨ
  simp only [Functor.mapIso_hom, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv, Category.assoc] at this
  rw [this, Loc.loc_def]
  simp only [Category.assoc]

theorem piece {X'' X''' W : Scheme.{u}} (a₁ a₂ : X'' ⟶ X) (b₁₂ b₁₃ b₂₃ : X''' ⟶ X'')
    (h₁ : b₁₂ ≫ a₁ = b₁₃ ≫ a₁) (h₂ : b₁₂ ≫ a₂ = b₂₃ ≫ a₁) (h₃ : b₁₃ ≫ a₂ = b₂₃ ≫ a₂)
    (Tg Th Tgh : X ⟶ X) (emul : Tgh = Tg ≫ Th)
    (ψg : M ≅ (Scheme.Modules.pullback Tg).obj M) (ψh : M ≅ (Scheme.Modules.pullback Th).obj M)
    (ψgh : M ≅ (Scheme.Modules.pullback Tgh).obj M)
    (hmul : ψgh = ψg ≪≫ (Scheme.Modules.pullback Tg).mapIso ψh ≪≫ (Scheme.Modules.pullbackComp Tg Th).app M ≪≫
      ((Scheme.Modules.pullbackCongr emul).app M).symm)
    (Ψ : (Scheme.Modules.pullback a₁).obj M ≅ (Scheme.Modules.pullback a₂).obj M)
    (ι : W ⟶ X''')
    (hw₁₂ : ((ι ≫ b₁₂) ≫ a₁) ≫ Tg = (ι ≫ b₁₂) ≫ a₂) (hw₂₃ : ((ι ≫ b₂₃) ≫ a₁) ≫ Th = (ι ≫ b₂₃) ≫ a₂)
    (hw₁₃ : ((ι ≫ b₁₃) ≫ a₁) ≫ Tgh = (ι ≫ b₁₃) ≫ a₂)
    (H₁₂ : (Scheme.Modules.pullback (ι ≫ b₁₂)).map Ψ.hom =
      (Scheme.Modules.pullbackComp (ι ≫ b₁₂) a₁).hom.app M ≫ Loc.loc M ((ι ≫ b₁₂) ≫ a₁) ((ι ≫ b₁₂) ≫ a₂) Tg ψg hw₁₂ ≫
        (Scheme.Modules.pullbackComp (ι ≫ b₁₂) a₂).inv.app M)
    (H₂₃ : (Scheme.Modules.pullback (ι ≫ b₂₃)).map Ψ.hom =
      (Scheme.Modules.pullbackComp (ι ≫ b₂₃) a₁).hom.app M ≫ Loc.loc M ((ι ≫ b₂₃) ≫ a₁) ((ι ≫ b₂₃) ≫ a₂) Th ψh hw₂₃ ≫
        (Scheme.Modules.pullbackComp (ι ≫ b₂₃) a₂).inv.app M)
    (H₁₃ : (Scheme.Modules.pullback (ι ≫ b₁₃)).map Ψ.hom =
      (Scheme.Modules.pullbackComp (ι ≫ b₁₃) a₁).hom.app M ≫ Loc.loc M ((ι ≫ b₁₃) ≫ a₁) ((ι ≫ b₁₃) ≫ a₂) Tgh ψgh hw₁₃ ≫
        (Scheme.Modules.pullbackComp (ι ≫ b₁₃) a₂).inv.app M) :
    pullHom (F := (Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁)
        (pullHom (F := (Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁) (M₁ := M) (M₂ := M)
            (f₁ := a₁) (f₂ := a₂) Ψ.hom b₁₂ (b₁₃ ≫ a₁) (b₂₃ ≫ a₁) h₁ h₂ ≫
          pullHom (F := (Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁) (M₁ := M) (M₂ := M)
            (f₁ := a₁) (f₂ := a₂) Ψ.hom b₂₃ (b₂₃ ≫ a₁) (b₁₃ ≫ a₂) rfl h₃.symm)
        ι (ι ≫ b₁₃ ≫ a₁) (ι ≫ b₁₃ ≫ a₂) rfl rfl =
      pullHom (F := (Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁)
        (pullHom (F := (Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁) (M₁ := M) (M₂ := M)
          (f₁ := a₁) (f₂ := a₂) Ψ.hom b₁₃ (b₁₃ ≫ a₁) (b₁₃ ≫ a₂) rfl rfl)
        ι (ι ≫ b₁₃ ≫ a₁) (ι ≫ b₁₃ ≫ a₂) rfl rfl := by

  have e₁₂ : (ι ≫ b₁₃ ≫ a₁) ≫ Tg = ι ≫ b₂₃ ≫ a₁ := by
    have t := hw₁₂
    simp only [Category.assoc] at t ⊢
    rw [← reassoc_of% h₁, t, h₂]
  have e₂₃ : (ι ≫ b₂₃ ≫ a₁) ≫ Th = ι ≫ b₁₃ ≫ a₂ := by
    have t := hw₂₃
    simp only [Category.assoc] at t ⊢
    rw [t, h₃]
  have e₁₃ : (ι ≫ b₁₃ ≫ a₁) ≫ Tgh = ι ≫ b₁₃ ≫ a₂ := by
    simpa only [Category.assoc] using hw₁₃
  rw [CoverCalc.pullHom_comp' _ _ ι (ι ≫ b₁₃ ≫ a₁) (ι ≫ b₂₃ ≫ a₁) (ι ≫ b₁₃ ≫ a₂) rfl rfl rfl,
    pullHom_pullHom, pullHom_pullHom, pullHom_pullHom]
  rw [Loc.pullHom_eq_loc_of_map_eq M a₁ a₂ Ψ.hom Tg ψg (ι ≫ b₁₂) hw₁₂ H₁₂ _ _ _ _ e₁₂,
    Loc.pullHom_eq_loc_of_map_eq M a₁ a₂ Ψ.hom Th ψh (ι ≫ b₂₃) hw₂₃ H₂₃ _ _ _ _ e₂₃,
    Loc.pullHom_eq_loc_of_map_eq M a₁ a₂ Ψ.hom Tgh ψgh (ι ≫ b₁₃) hw₁₃ H₁₃ _ _ _ _ e₁₃]
  exact Loc.loc_comp M Tg Th Tgh emul ψg ψh ψgh hmul _ _ _ e₁₂ e₂₃ e₁₃

end KPC

namespace KPC
set_option backward.isDefEq.respectTransparency false

universe u v

p2m_open "CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat"

theorem hw_of_le {X X'' X''' : Scheme.{u}} (a₁ a₂ : X'' ⟶ X) (T : X ⟶ X) (b : X''' ⟶ X'') (Ug : X''.Opens)
    (hUg : Ug.ι ≫ a₂ = Ug.ι ≫ a₁ ≫ T) (V : X'''.Opens) (hle : V ≤ b ⁻¹ᵁ Ug) :
    ((V.ι ≫ b) ≫ a₁) ≫ T = (V.ι ≫ b) ≫ a₂ := by
  have fac : V.ι ≫ b = (X'''.homOfLE hle ≫ (b ∣_ Ug)) ≫ Ug.ι := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
  rw [fac]
  simp only [Category.assoc]
  rw [← hUg]

theorem cocycle_pullHom
    {X Y : Scheme.{u}} (q : X ⟶ Y)
    (G : Type v) [AddGroup G] (σ : G → (X ⟶ X))
    (hσadd : ∀ g h : G, σ (g + h) = σ g ≫ σ h)
    (hsplit : ∀ ⦃Z : Scheme.{u}⦄ (g₁ g₂ : Z ⟶ X), g₁ ≫ q = g₂ ≫ q →
      ∃ U : G → Z.Opens, ⨆ g, U g = ⊤ ∧ ∀ g, (U g).ι ≫ g₂ = (U g).ι ≫ g₁ ≫ σ g)
    (M : X.Modules)
    (ψ : ∀ g : G, M ≅ (Scheme.Modules.pullback (σ g)).obj M)
    (hψadd : ∀ g h : G, ψ (g + h) =
        ψ g ≪≫ (Scheme.Modules.pullback (σ g)).mapIso (ψ h) ≪≫
          (Scheme.Modules.pullbackComp (σ g) (σ h)).app M ≪≫ ((Scheme.Modules.pullbackCongr (hσadd g h)).app M).symm)
    {X'' X''' : Scheme.{u}} (a₁ a₂ : X'' ⟶ X) (ha : a₁ ≫ q = a₂ ≫ q)
    (b₁₂ b₁₃ b₂₃ : X''' ⟶ X'')
    (h₁ : b₁₂ ≫ a₁ = b₁₃ ≫ a₁) (h₂ : b₁₂ ≫ a₂ = b₂₃ ≫ a₁) (h₃ : b₁₃ ≫ a₂ = b₂₃ ≫ a₂)
    (Ψ : (Scheme.Modules.pullback a₁).obj M ≅ (Scheme.Modules.pullback a₂).obj M)
    (hΨ : ∀ (g : G) ⦃W : Scheme.{u}⦄ (w : W ⟶ X'') (hw : (w ≫ a₁) ≫ σ g = w ≫ a₂),
        (Scheme.Modules.pullback w).mapIso Ψ =
          (Scheme.Modules.pullbackComp w a₁).app M ≪≫ (Scheme.Modules.pullback (w ≫ a₁)).mapIso (ψ g) ≪≫
            (Scheme.Modules.pullbackComp (w ≫ a₁) (σ g)).app M ≪≫ (Scheme.Modules.pullbackCongr hw).app M ≪≫
              ((Scheme.Modules.pullbackComp w a₂).app M).symm) :
    pullHom (F := (Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁) (M₁ := M) (M₂ := M)
        (f₁ := a₁) (f₂ := a₂) Ψ.hom b₁₂ (b₁₃ ≫ a₁) (b₂₃ ≫ a₁) h₁ h₂ ≫
      pullHom (F := (Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁) (M₁ := M) (M₂ := M)
        (f₁ := a₁) (f₂ := a₂) Ψ.hom b₂₃ (b₂₃ ≫ a₁) (b₁₃ ≫ a₂) rfl h₃.symm =
    pullHom (F := (Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁) (M₁ := M) (M₂ := M)
        (f₁ := a₁) (f₂ := a₂) Ψ.hom b₁₃ (b₁₃ ≫ a₁) (b₁₃ ≫ a₂) rfl rfl := by
  obtain ⟨U, hU, hUeq⟩ := hsplit a₁ a₂ ha
  refine hom_ext_pull (fun p : G × G => b₁₂ ⁻¹ᵁ (U p.1) ⊓ b₂₃ ⁻¹ᵁ (U p.2))
    (iSup_inf_eq_top (fun g => b₁₂ ⁻¹ᵁ (U g)) (fun g => b₂₃ ⁻¹ᵁ (U g))
      (iSup_preimage_eq_top b₁₂ U hU) (iSup_preimage_eq_top b₂₃ U hU))
    (pullHom (F := (Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁) (M₁ := M) (M₂ := M)
        (f₁ := a₁) (f₂ := a₂) Ψ.hom b₁₂ (b₁₃ ≫ a₁) (b₂₃ ≫ a₁) h₁ h₂ ≫
      pullHom (F := (Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁) (M₁ := M) (M₂ := M)
        (f₁ := a₁) (f₂ := a₂) Ψ.hom b₂₃ (b₂₃ ≫ a₁) (b₁₃ ≫ a₂) rfl h₃.symm)
    (pullHom (F := (Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁) (M₁ := M) (M₂ := M)
        (f₁ := a₁) (f₂ := a₂) Ψ.hom b₁₃ (b₁₃ ≫ a₁) (b₁₃ ≫ a₂) rfl rfl) ?_
  rintro ⟨g, h⟩
  dsimp only
  have hw₁₂ := hw_of_le a₁ a₂ (σ g) b₁₂ (U g) (hUeq g) (b₁₂ ⁻¹ᵁ (U g) ⊓ b₂₃ ⁻¹ᵁ (U h)) inf_le_left
  have hw₂₃ := hw_of_le a₁ a₂ (σ h) b₂₃ (U h) (hUeq h) (b₁₂ ⁻¹ᵁ (U g) ⊓ b₂₃ ⁻¹ᵁ (U h)) inf_le_right
  have hw₁₃ : (((b₁₂ ⁻¹ᵁ (U g) ⊓ b₂₃ ⁻¹ᵁ (U h)).ι ≫ b₁₃) ≫ a₁) ≫ σ (g + h) =
      ((b₁₂ ⁻¹ᵁ (U g) ⊓ b₂₃ ⁻¹ᵁ (U h)).ι ≫ b₁₃) ≫ a₂ := by
    have t₁ := hw₁₂
    have t₂ := hw₂₃
    rw [hσadd]
    simp only [Category.assoc] at t₁ t₂ ⊢
    rw [← reassoc_of% h₁, reassoc_of% t₁, reassoc_of% h₂, t₂, h₃]
  exact piece M a₁ a₂ b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ (σ g) (σ h) (σ (g + h)) (hσadd g h) (ψ g) (ψ h) (ψ (g + h)) (hψadd g h)
    Ψ (b₁₂ ⁻¹ᵁ (U g) ⊓ b₂₃ ⁻¹ᵁ (U h)).ι hw₁₂ hw₂₃ hw₁₃
    (map_hom_eq_of_mapIso_eq M a₁ a₂ _ _ Ψ _ hw₁₂ (hΨ g _ hw₁₂))
    (map_hom_eq_of_mapIso_eq M a₁ a₂ _ _ Ψ _ hw₂₃ (hΨ h _ hw₂₃))
    (map_hom_eq_of_mapIso_eq M a₁ a₂ _ _ Ψ _ hw₁₃ (hΨ (g + h) _ hw₁₃))

theorem main
    {X Y : Scheme.{u}} (q : X ⟶ Y)
    (G : Type v) [AddGroup G] (σ : G → (X ⟶ X))
    (hσadd : ∀ g h : G, σ (g + h) = σ g ≫ σ h)
    (hsplit : ∀ ⦃Z : Scheme.{u}⦄ (g₁ g₂ : Z ⟶ X), g₁ ≫ q = g₂ ≫ q →
      ∃ U : G → Z.Opens, ⨆ g, U g = ⊤ ∧ ∀ g, (U g).ι ≫ g₂ = (U g).ι ≫ g₁ ≫ σ g)
    (M : X.Modules)
    (ψ : ∀ g : G, M ≅ (Scheme.Modules.pullback (σ g)).obj M)
    (hψadd : ∀ g h : G, ψ (g + h) =
        ψ g ≪≫ (Scheme.Modules.pullback (σ g)).mapIso (ψ h) ≪≫
          (Scheme.Modules.pullbackComp (σ g) (σ h)).app M ≪≫ ((Scheme.Modules.pullbackCongr (hσadd g h)).app M).symm)
    {X'' X''' : Scheme.{u}} (a₁ a₂ : X'' ⟶ X) (ha : a₁ ≫ q = a₂ ≫ q)
    (b₁₂ b₁₃ b₂₃ : X''' ⟶ X'')
    (h₁ : b₁₂ ≫ a₁ = b₁₃ ≫ a₁) (h₂ : b₁₂ ≫ a₂ = b₂₃ ≫ a₁) (h₃ : b₁₃ ≫ a₂ = b₂₃ ≫ a₂)
    (Ψ : (Scheme.Modules.pullback a₁).obj M ≅ (Scheme.Modules.pullback a₂).obj M)
    (hΨ : ∀ (g : G) ⦃W : Scheme.{u}⦄ (w : W ⟶ X'') (hw : (w ≫ a₁) ≫ σ g = w ≫ a₂),
        (Scheme.Modules.pullback w).mapIso Ψ =
          (Scheme.Modules.pullbackComp w a₁).app M ≪≫ (Scheme.Modules.pullback (w ≫ a₁)).mapIso (ψ g) ≪≫
            (Scheme.Modules.pullbackComp (w ≫ a₁) (σ g)).app M ≪≫ (Scheme.Modules.pullbackCongr hw).app M ≪≫
              ((Scheme.Modules.pullbackComp w a₂).app M).symm) :
    ((Scheme.Modules.pullbackCongr h₁).app M).symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₁).app M).symm ≪≫ (Scheme.Modules.pullback b₁₂).mapIso Ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₂).app M) ≪≫
          ((Scheme.Modules.pullbackCongr h₂).app M) ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₁).app M).symm ≪≫ (Scheme.Modules.pullback b₂₃).mapIso Ψ ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₂).app M) ≪≫ ((Scheme.Modules.pullbackCongr h₃).app M).symm
        = ((Scheme.Modules.pullbackComp b₁₃ a₁).app M).symm ≪≫ (Scheme.Modules.pullback b₁₃).mapIso Ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₃ a₂).app M) := by
  have H := cocycle_pullHom q G σ hσadd hsplit M ψ hψadd a₁ a₂ ha b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ Ψ hΨ
  rw [Loc.pullHom_eq, Loc.pullHom_eq, Loc.pullHom_eq] at H
  ext : 1
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, Category.assoc,
    Loc.pullbackCongr_hom_app, Loc.pullbackCongr_inv_app, eqToHom_refl, Category.id_comp, Category.comp_id] at H ⊢
  exact H

end KPC

universe u v

theorem solution
    {X Y : Scheme.{u}} (q : X ⟶ Y)
    (G : Type v) [AddGroup G] (σ : G → (X ⟶ X))
    (hσadd : ∀ g h : G, σ (g + h) = σ g ≫ σ h)
    (hsplit : ∀ ⦃Z : Scheme.{u}⦄ (g₁ g₂ : Z ⟶ X), g₁ ≫ q = g₂ ≫ q →
      ∃ U : G → Z.Opens, ⨆ g, U g = ⊤ ∧ ∀ g, (U g).ι ≫ g₂ = (U g).ι ≫ g₁ ≫ σ g)
    (M : X.Modules)
    (ψ : ∀ g : G, M ≅ (Scheme.Modules.pullback (σ g)).obj M)
    (hψadd : ∀ g h : G, ψ (g + h) =
        ψ g ≪≫ (Scheme.Modules.pullback (σ g)).mapIso (ψ h) ≪≫
          (Scheme.Modules.pullbackComp (σ g) (σ h)).app M ≪≫ ((Scheme.Modules.pullbackCongr (hσadd g h)).app M).symm)
    {X'' X''' : Scheme.{u}} (a₁ a₂ : X'' ⟶ X) (ha : a₁ ≫ q = a₂ ≫ q)
    (b₁₂ b₁₃ b₂₃ : X''' ⟶ X'')
    (h₁ : b₁₂ ≫ a₁ = b₁₃ ≫ a₁) (h₂ : b₁₂ ≫ a₂ = b₂₃ ≫ a₁) (h₃ : b₁₃ ≫ a₂ = b₂₃ ≫ a₂)
    (Ψ : (Scheme.Modules.pullback a₁).obj M ≅ (Scheme.Modules.pullback a₂).obj M)
    (hΨ : ∀ (g : G) ⦃W : Scheme.{u}⦄ (w : W ⟶ X'') (hw : (w ≫ a₁) ≫ σ g = w ≫ a₂),
        (Scheme.Modules.pullback w).mapIso Ψ =
          (Scheme.Modules.pullbackComp w a₁).app M ≪≫ (Scheme.Modules.pullback (w ≫ a₁)).mapIso (ψ g) ≪≫
            (Scheme.Modules.pullbackComp (w ≫ a₁) (σ g)).app M ≪≫ (Scheme.Modules.pullbackCongr hw).app M ≪≫
              ((Scheme.Modules.pullbackComp w a₂).app M).symm) :
    ((Scheme.Modules.pullbackCongr h₁).app M).symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₁).app M).symm ≪≫ (Scheme.Modules.pullback b₁₂).mapIso Ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₂).app M) ≪≫
          ((Scheme.Modules.pullbackCongr h₂).app M) ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₁).app M).symm ≪≫ (Scheme.Modules.pullback b₂₃).mapIso Ψ ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₂).app M) ≪≫ ((Scheme.Modules.pullbackCongr h₃).app M).symm
        = ((Scheme.Modules.pullbackComp b₁₃ a₁).app M).symm ≪≫ (Scheme.Modules.pullback b₁₃).mapIso Ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₃ a₂).app M) :=
  KPC.main q G σ hσadd hsplit M ψ hψadd a₁ a₂ ha b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ Ψ hΨ

end S_AlgebraicGeometry_Scheme_Modules_cocycle_of_forall_mapIso_eq_of_split
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_cocycle_of_forall_mapIso_eq_of_split (solution)
