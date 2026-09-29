-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.toDescentData_map_bijective_of_openCover
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/c8885cd3-f83c-523f-956e-c50999807a78

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_toDescentData_map_bijective_of_openCover

set_option autoImplicit false

universe v u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_toDescentData_map_bijective_of_openCover.AlgebraicGeometry Opposite TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.hom_ext IsOpenImmersion.lift Scheme.Modules.Hom.app_smul Scheme.Modules.pseudofunctor Scheme.Opens.range_ι Scheme.Hom Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Scheme.Hom.image_preimage_eq_opensRange_inf Scheme.Hom.comp_image Scheme.Hom.image_top_eq_opensRange Scheme Scheme.Modules.Hom.id_app Scheme.Modules.Hom.app IsOpenImmersion Scheme.Modules.pullbackCongr Scheme.Opens.ι_apply Scheme.Modules Scheme.Opens Scheme.Hom.coe_image IsOpenImmersion.lift_fac Scheme.Modules.map_smul Scheme.Opens.opensRange_ι Scheme.Hom.comp_apply Scheme.Modules.pullbackComp"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.hom_ext Modules.Hom.app_smul Modules.pseudofunctor Hom.id_app Opens.range_ι Hom mk Γ Modules.Hom.comp_app Hom.app Modules.Hom Hom.image_preimage_eq_opensRange_inf Hom.comp_image Hom.image_top_eq_opensRange Modules.Hom.id_app Modules.Hom.app restrictFunctor Hom.comp_app Modules.pullbackCongr Opens.ι_apply Modules Opens Hom.coe_image Modules.map_smul Opens.opensRange_ι restrict Hom.comp_apply PresheafOfModules Modules.pullbackComp"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "hom_ext Hom.app_smul pseudofunctor pushforward pushforwardComp pullback presheaf Hom.comp_app Hom restrictFunctorCongr restrictFunctor Hom.id_app Hom.app restrictFunctorIsoPullback restrictFunctorComp_hom_app_app restrictAdjunction pullbackCongr isSheaf pullbackPushforwardAdjunction restrictFunctorComp restrict conjugateEquiv_pullbackComp_inv map_smul pullbackComp"
namespace HomZar
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

theorem presheaf_map_eq {Y : Scheme.{u}} (M : Y.Modules) {A B : Y.Opens} (p q : op A ⟶ op B) :
    M.presheaf.map p = M.presheaf.map q := by
  have : p = q := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  rw [this]

theorem app_naturality {Y : Scheme.{u}} {M N : Y.Modules} (φ : M ⟶ N) {U V : Y.Opens} (i : op U ⟶ op V) :
    M.presheaf.map i ≫ φ.app V = φ.app U ≫ N.presheaf.map i :=
  φ.mapPresheaf.naturality i

section D3

variable {X₀ X₁ Y : Scheme.{u}} (h : X₀ ⟶ X₁) (g : X₁ ⟶ Y) [IsOpenImmersion h] [IsOpenImmersion g] (M : Y.Modules)

theorem D3_LA (W : Y.Opens) :
    (((((restrictAdjunction g).unit.app M ≫ (pushforward g).map ((restrictFunctorIsoPullback g).hom.app M)) ≫
      (pushforward g).map ((restrictAdjunction h).unit.app ((pullback g).obj M) ≫
        (pushforward h).map ((restrictFunctorIsoPullback h).hom.app ((pullback g).obj M)))) ≫
      (pushforwardComp h g).hom.app _) ≫
      (pushforward (h ≫ g)).map ((pullbackComp h g).hom.app M)).app W =
    (((M.presheaf.map (homOfLE (g.image_preimage_le W)).op ≫
      ((restrictFunctorIsoPullback g).hom.app M).app (g ⁻¹ᵁ W)) ≫
      (((pullback g).obj M).presheaf.map (homOfLE (h.image_preimage_le (g ⁻¹ᵁ W))).op ≫
        ((restrictFunctorIsoPullback h).hom.app ((pullback g).obj M)).app (h ⁻¹ᵁ (g ⁻¹ᵁ W)))) ≫
      𝟙 _) ≫
      ((pullbackComp h g).hom.app M).app ((h ≫ g) ⁻¹ᵁ W) := by
  rfl

theorem D3_RA (W : Y.Opens) :
    ((restrictAdjunction (h ≫ g)).unit.app M ≫ (pushforward (h ≫ g)).map
      ((restrictFunctorComp h g).hom.app M ≫ (restrictFunctor h).map ((restrictFunctorIsoPullback g).hom.app M) ≫
        (restrictFunctorIsoPullback h).hom.app ((pullback g).obj M) ≫ (pullbackComp h g).hom.app M)).app W =
    M.presheaf.map (homOfLE ((h ≫ g).image_preimage_le W)).op ≫
      (((restrictFunctorComp h g).hom.app M).app ((h ≫ g) ⁻¹ᵁ W) ≫
        ((restrictFunctorIsoPullback g).hom.app M).app (h ''ᵁ ((h ≫ g) ⁻¹ᵁ W)) ≫
        ((restrictFunctorIsoPullback h).hom.app ((pullback g).obj M)).app ((h ≫ g) ⁻¹ᵁ W) ≫
        ((pullbackComp h g).hom.app M).app ((h ≫ g) ⁻¹ᵁ W)) := by
  rfl

set_option maxHeartbeats 3200000 in

theorem D3_core :
    ((((restrictAdjunction g).unit.app M ≫ (pushforward g).map ((restrictFunctorIsoPullback g).hom.app M)) ≫
      (pushforward g).map ((restrictAdjunction h).unit.app ((pullback g).obj M) ≫
        (pushforward h).map ((restrictFunctorIsoPullback h).hom.app ((pullback g).obj M)))) ≫
      (pushforwardComp h g).hom.app _) ≫
      (pushforward (h ≫ g)).map ((pullbackComp h g).hom.app M) =
    (restrictAdjunction (h ≫ g)).unit.app M ≫ (pushforward (h ≫ g)).map
      ((restrictFunctorComp h g).hom.app M ≫ (restrictFunctor h).map ((restrictFunctorIsoPullback g).hom.app M) ≫
        (restrictFunctorIsoPullback h).hom.app ((pullback g).obj M) ≫ (pullbackComp h g).hom.app M) := by
  apply Scheme.Modules.hom_ext
  intro W
  rw [D3_LA h g M W, D3_RA h g M W]
  have nat : ((restrictFunctorIsoPullback g).hom.app M).app (g ⁻¹ᵁ W) ≫
      ((pullback g).obj M).presheaf.map (homOfLE (h.image_preimage_le (g ⁻¹ᵁ W))).op =
      M.presheaf.map (g.opensFunctor.map (homOfLE (h.image_preimage_le (g ⁻¹ᵁ W)))).op ≫
        ((restrictFunctorIsoPullback g).hom.app M).app (h ''ᵁ h ⁻¹ᵁ g ⁻¹ᵁ W) :=
    (app_naturality ((restrictFunctorIsoPullback g).hom.app M) (homOfLE (h.image_preimage_le (g ⁻¹ᵁ W))).op).symm
  have hrc : ((restrictFunctorComp h g).hom.app M).app ((h ≫ g) ⁻¹ᵁ W) =
      M.presheaf.map (eqToHom (show g ''ᵁ h ''ᵁ (h ≫ g) ⁻¹ᵁ W = (h ≫ g) ''ᵁ (h ≫ g) ⁻¹ᵁ W by simp)).op :=
    restrictFunctorComp_hom_app_app h g M

  have fin : ∀ {B C : Y.Opens} (p : op W ⟶ op B) (q : op B ⟶ op C) {B' : Y.Opens}
      (p'' : op W ⟶ op B') (q'' : op B' ⟶ op C) {Z : Ab} (r : Γ(M, C) ⟶ Z),
      M.presheaf.map p ≫ M.presheaf.map q ≫ r = M.presheaf.map p'' ≫ M.presheaf.map q'' ≫ r := by
    intros B C p q B' p'' q'' Z r
    rw [← Category.assoc, ← Category.assoc (M.presheaf.map p''), ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (fun t => t ≫ r) (presheaf_map_eq M _ _)
  simp only [Category.assoc, Category.id_comp]
  rw [hrc]

  refine (congrArg (fun t => M.presheaf.map (homOfLE (g.image_preimage_le W)).op ≫ t ≫
      (((restrictFunctorIsoPullback h).hom.app ((pullback g).obj M)).app (h ⁻¹ᵁ (g ⁻¹ᵁ W)) ≫
        ((pullbackComp h g).hom.app M).app ((h ≫ g) ⁻¹ᵁ W))) nat).trans ?_
  exact fin (homOfLE (g.image_preimage_le W)).op
    (g.opensFunctor.map (homOfLE (h.image_preimage_le (g ⁻¹ᵁ W)))).op
    (homOfLE ((h ≫ g).image_preimage_le W)).op
    (eqToHom (show g ''ᵁ h ''ᵁ (h ≫ g) ⁻¹ᵁ W = (h ≫ g) ''ᵁ (h ≫ g) ⁻¹ᵁ W by simp)).op
    (((restrictFunctorIsoPullback g).hom.app M).app (h ''ᵁ h ⁻¹ᵁ g ⁻¹ᵁ W) ≫
      ((restrictFunctorIsoPullback h).hom.app ((pullback g).obj M)).app (h ⁻¹ᵁ (g ⁻¹ᵁ W)) ≫
        ((pullbackComp h g).hom.app M).app ((h ≫ g) ⁻¹ᵁ W))

set_option maxHeartbeats 3200000 in

theorem restrictFunctorIsoPullback_comp_hom_app :
    (restrictFunctorIsoPullback (h ≫ g)).hom.app M =
      (restrictFunctorComp h g).hom.app M ≫ (restrictFunctor h).map ((restrictFunctorIsoPullback g).hom.app M) ≫
        (restrictFunctorIsoPullback h).hom.app ((pullback g).obj M) ≫ (pullbackComp h g).hom.app M := by
  apply ((restrictAdjunction (h ≫ g)).homEquiv _ _).injective
  have e1 : (restrictAdjunction (h ≫ g)).homEquiv _ _ ((restrictFunctorIsoPullback (h ≫ g)).hom.app M) =
      (pullbackPushforwardAdjunction (h ≫ g)).unit.app M :=
    Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ M
  rw [e1, Adjunction.homEquiv_unit]
  have hconj := unit_conjugateEquiv ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction h))
    (pullbackPushforwardAdjunction (h ≫ g)) (pullbackComp h g).inv M
  rw [conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at hconj
  dsimp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map] at hconj
  have key0 := (Iso.eq_comp_inv ((pushforward (h ≫ g)).mapIso ((pullbackComp h g).app M))).mp hconj
  dsimp only [Functor.mapIso_hom, Iso.app_hom, Functor.comp_obj] at key0
  have ug : (pullbackPushforwardAdjunction g).unit.app M =
      (restrictAdjunction g).unit.app M ≫ (pushforward g).map ((restrictFunctorIsoPullback g).hom.app M) :=
    (Adjunction.unit_leftAdjointUniq_hom_app _ _ M).symm
  have uh : (pullbackPushforwardAdjunction h).unit.app ((pullback g).obj M) =
      (restrictAdjunction h).unit.app ((pullback g).obj M) ≫
        (pushforward h).map ((restrictFunctorIsoPullback h).hom.app ((pullback g).obj M)) :=
    (Adjunction.unit_leftAdjointUniq_hom_app _ _ _).symm
  rw [← key0, ug, uh]
  exact D3_core h g M

end D3

noncomputable abbrev Mdl : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat :=
  (AlgebraicGeometry.Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁

theorem Mdl_keyMC {a b d : LocallyDiscrete Scheme.{u}ᵒᵖ} (u' : a ⟶ b) (v' : b ⟶ d) (M : Mdl.obj a) :
    (Mdl.mapComp' u' v' (u' ≫ v') rfl).hom.toNatTrans.app M = (Mdl.mapComp u' v').hom.toNatTrans.app M := by
  rw [Pseudofunctor.mapComp'_eq_mapComp]

theorem Mdl_keyMC_inv {a b d : LocallyDiscrete Scheme.{u}ᵒᵖ} (u' : a ⟶ b) (v' : b ⟶ d) (M : Mdl.obj a) :
    (Mdl.mapComp' u' v' (u' ≫ v') rfl).inv.toNatTrans.app M = (Mdl.mapComp u' v').inv.toNatTrans.app M := by
  rw [Pseudofunctor.mapComp'_eq_mapComp]

theorem Mdl_mapComp'_hom_app {X₀ X₁ Y : Scheme.{u}} (f : X₀ ⟶ X₁) (g : X₁ ⟶ Y) (L : Y.Modules)
    (fg : X₀ ⟶ Y) (hfg : f ≫ g = fg) :
    (Mdl.mapComp' g.op.toLoc f.op.toLoc fg.op.toLoc (by rw [← hfg]; rfl)).hom.toNatTrans.app L =
    (Scheme.Modules.pullbackCongr hfg.symm).hom.app L ≫ (Scheme.Modules.pullbackComp f g).inv.app L := by
  subst hfg
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  exact Mdl_keyMC g.op.toLoc f.op.toLoc L

theorem Mdl_mapComp'_inv_app {X₀ X₁ Y : Scheme.{u}} (f : X₀ ⟶ X₁) (g : X₁ ⟶ Y) (L : Y.Modules)
    (fg : X₀ ⟶ Y) (hfg : f ≫ g = fg) :
    (Mdl.mapComp' g.op.toLoc f.op.toLoc fg.op.toLoc (by rw [← hfg]; rfl)).inv.toNatTrans.app L =
    (Scheme.Modules.pullbackComp f g).hom.app L ≫ (Scheme.Modules.pullbackCongr hfg).hom.app L := by
  subst hfg
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id]
  exact Mdl_keyMC_inv g.op.toLoc f.op.toLoc L

theorem pullHom_eq {Z' Z X₁ X₂ : Scheme.{u}} (e : Z' ⟶ Z) (f₁ : Z ⟶ X₁) (f₂ : Z ⟶ X₂)
    (M₁ : X₁.Modules) (M₂ : X₂.Modules) (φ : (pullback f₁).obj M₁ ⟶ (pullback f₂).obj M₂) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := Mdl)
        (X₁ := X₁) (X₂ := X₂) (M₁ := M₁) (M₂ := M₂) (f₁ := f₁) (f₂ := f₂) φ e (e ≫ f₁) (e ≫ f₂) rfl rfl =
      (pullbackComp e f₁).inv.app M₁ ≫ (pullback e).map φ ≫ (pullbackComp e f₂).hom.app M₂ := by
  dsimp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  rw [ Mdl_mapComp'_hom_app e f₁ M₁ (e ≫ f₁) rfl, Mdl_mapComp'_inv_app e f₂ M₂ (e ≫ f₂) rfl]
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    Category.comp_id]
  rfl

theorem restrictFunctorCongr_rfl_hom_app {X' Y : Scheme.{u}} (f : X' ⟶ Y) [IsOpenImmersion f] (M : Y.Modules) :
    (restrictFunctorCongr (rfl : f = f)).hom.app M = 𝟙 _ := by
  apply Scheme.Modules.hom_ext
  intro U
  change M.presheaf.map (eqToHom (rfl : f ''ᵁ U = f ''ᵁ U)).op = _
  simp
  rfl

theorem restrictFunctorCongr_rfl_inv_app {X' Y : Scheme.{u}} (f : X' ⟶ Y) [IsOpenImmersion f] (M : Y.Modules) :
    (restrictFunctorCongr (rfl : f = f)).inv.app M = 𝟙 _ := by
  apply Scheme.Modules.hom_ext
  intro U
  change M.presheaf.map (eqToHom (rfl : f ''ᵁ U = f ''ᵁ U)).op = _
  simp
  rfl

section CruxApp

variable {Z' Z X₁ X₂ : Scheme.{u}} (e : Z' ⟶ Z) (f₁ : Z ⟶ X₁) (f₂ : Z ⟶ X₂)
    [IsOpenImmersion e] [IsOpenImmersion f₁] [IsOpenImmersion f₂]
    (M₁ : X₁.Modules) (M₂ : X₂.Modules) (φ : (pullback f₁).obj M₁ ⟶ (pullback f₂).obj M₂)

set_option maxRecDepth 20000 in
theorem CRUX_LA (U : Z'.Opens) :
    (((restrictFunctorComp e f₁).hom.app M₁ ≫ (restrictFunctor e).map ((restrictFunctorIsoPullback f₁).hom.app M₁) ≫
        (restrictFunctorIsoPullback e).hom.app ((pullback f₁).obj M₁) ≫ (pullbackComp e f₁).hom.app M₁) ≫
      ((pullbackComp e f₁).inv.app M₁ ≫ (pullback e).map φ ≫ (pullbackComp e f₂).hom.app M₂) ≫
      ((pullbackComp e f₂).inv.app M₂ ≫ (restrictFunctorIsoPullback e).inv.app ((pullback f₂).obj M₂) ≫
        (restrictFunctor e).map ((restrictFunctorIsoPullback f₂).inv.app M₂) ≫ (restrictFunctorComp e f₂).inv.app M₂)).app U =
    ((restrictFunctorComp e f₁).hom.app M₁).app U ≫
      ((restrictFunctorIsoPullback f₁).hom.app M₁).app (e ''ᵁ U) ≫
      ((restrictFunctorIsoPullback e).hom.app ((pullback f₁).obj M₁)).app U ≫
      (((pullbackComp e f₁).hom.app M₁).app U ≫ ((pullbackComp e f₁).inv.app M₁).app U) ≫
      ((pullback e).map φ).app U ≫ ((pullbackComp e f₂).hom.app M₂).app U ≫
      ((pullbackComp e f₂).inv.app M₂).app U ≫
      ((restrictFunctorIsoPullback e).inv.app ((pullback f₂).obj M₂)).app U ≫
      ((restrictFunctorIsoPullback f₂).inv.app M₂).app (e ''ᵁ U) ≫
      ((restrictFunctorComp e f₂).inv.app M₂).app U := by
  rfl

theorem CRUX_RA (U : Z'.Opens) :
    ((restrictFunctorComp e f₁).hom.app M₁ ≫
      (restrictFunctor e).map ((restrictFunctorIsoPullback f₁).hom.app M₁ ≫ φ ≫ (restrictFunctorIsoPullback f₂).inv.app M₂) ≫
      (restrictFunctorComp e f₂).inv.app M₂).app U =
    ((restrictFunctorComp e f₁).hom.app M₁).app U ≫
      ((restrictFunctorIsoPullback f₁).hom.app M₁).app (e ''ᵁ U) ≫ φ.app (e ''ᵁ U) ≫
      ((restrictFunctorIsoPullback f₂).inv.app M₂).app (e ''ᵁ U) ≫
      ((restrictFunctorComp e f₂).inv.app M₂).app U := by
  rfl

end CruxApp

theorem restrictFunctorIsoPullback_conj_pullHom {Z' Z X₁ X₂ : Scheme.{u}} (e : Z' ⟶ Z) (f₁ : Z ⟶ X₁) (f₂ : Z ⟶ X₂)
    (gf₁ : Z' ⟶ X₁) (gf₂ : Z' ⟶ X₂) [IsOpenImmersion e] [IsOpenImmersion f₁] [IsOpenImmersion f₂]
    [IsOpenImmersion gf₁] [IsOpenImmersion gf₂] (h₁ : e ≫ f₁ = gf₁) (h₂ : e ≫ f₂ = gf₂)
    (M₁ : X₁.Modules) (M₂ : X₂.Modules) (φ : (pullback f₁).obj M₁ ⟶ (pullback f₂).obj M₂) :
    (restrictFunctorIsoPullback gf₁).hom.app M₁ ≫
      (Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := Mdl)
        (X₁ := X₁) (X₂ := X₂) (M₁ := M₁) (M₂ := M₂) (f₁ := f₁) (f₂ := f₂) φ e gf₁ gf₂ h₁ h₂ :
        (pullback gf₁).obj M₁ ⟶ (pullback gf₂).obj M₂) ≫
      (restrictFunctorIsoPullback gf₂).inv.app M₂ =
    (restrictFunctorCongr h₁.symm).hom.app M₁ ≫ (restrictFunctorComp e f₁).hom.app M₁ ≫
      (restrictFunctor e).map ((restrictFunctorIsoPullback f₁).hom.app M₁ ≫ φ ≫ (restrictFunctorIsoPullback f₂).inv.app M₂) ≫
      (restrictFunctorComp e f₂).inv.app M₂ ≫ (restrictFunctorCongr h₂).hom.app M₂ := by
  subst h₁ h₂
  rw [pullHom_eq, restrictFunctorCongr_rfl_hom_app, restrictFunctorCongr_rfl_hom_app, Category.id_comp,
    Category.comp_id]

  have D1 := restrictFunctorIsoPullback_comp_hom_app e f₁ M₁
  have D2' : (restrictFunctorIsoPullback (e ≫ f₂)).app M₂ = (restrictFunctorComp e f₂).app M₂ ≪≫
      (restrictFunctor e).mapIso ((restrictFunctorIsoPullback f₂).app M₂) ≪≫
      (restrictFunctorIsoPullback e).app ((pullback f₂).obj M₂) ≪≫ (pullbackComp e f₂).app M₂ :=
    Iso.ext (restrictFunctorIsoPullback_comp_hom_app e f₂ M₂)
  have D2 := congrArg Iso.inv D2'
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Iso.app_hom, Category.assoc] at D2
  rw [show (restrictFunctorIsoPullback (e ≫ f₁)).hom.app M₁ = _ from D1,
    show (restrictFunctorIsoPullback (e ≫ f₂)).inv.app M₂ = _ from D2]

  have c3 : (restrictFunctorIsoPullback e).hom.app ((pullback f₁).obj M₁) ≫ (pullback e).map φ ≫
      (restrictFunctorIsoPullback e).inv.app ((pullback f₂).obj M₂) = (restrictFunctor e).map φ := by
    rw [← (restrictFunctorIsoPullback e).hom.naturality_assoc φ, Iso.hom_inv_id_app, Category.comp_id]

  apply Scheme.Modules.hom_ext
  intro U
  refine (CRUX_LA e f₁ f₂ M₁ M₂ φ U).trans ?_
  refine Eq.trans ?_ (CRUX_RA e f₁ f₂ M₁ M₂ φ U).symm
  have c1U : ((pullbackComp e f₁).hom.app M₁).app U ≫ ((pullbackComp e f₁).inv.app M₁).app U = 𝟙 _ := by
    rw [← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id_app, Scheme.Modules.Hom.id_app]
  have c2U : ((pullbackComp e f₂).hom.app M₂).app U ≫ ((pullbackComp e f₂).inv.app M₂).app U = 𝟙 _ := by
    rw [← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id_app, Scheme.Modules.Hom.id_app]
  have c3U : ((restrictFunctorIsoPullback e).hom.app ((pullback f₁).obj M₁)).app U ≫ ((pullback e).map φ).app U ≫
      ((restrictFunctorIsoPullback e).inv.app ((pullback f₂).obj M₂)).app U = φ.app (e ''ᵁ U) :=
    congrArg (fun ψ => Scheme.Modules.Hom.app ψ U) c3

  refine (congrArg (fun t => ((restrictFunctorComp e f₁).hom.app M₁).app U ≫
      ((restrictFunctorIsoPullback f₁).hom.app M₁).app (e ''ᵁ U) ≫
      ((restrictFunctorIsoPullback e).hom.app ((pullback f₁).obj M₁)).app U ≫ t ≫
      ((pullback e).map φ).app U ≫ ((pullbackComp e f₂).hom.app M₂).app U ≫
      ((pullbackComp e f₂).inv.app M₂).app U ≫
      ((restrictFunctorIsoPullback e).inv.app ((pullback f₂).obj M₂)).app U ≫
      ((restrictFunctorIsoPullback f₂).inv.app M₂).app (e ''ᵁ U) ≫
      ((restrictFunctorComp e f₂).inv.app M₂).app U) c1U).trans ?_

  refine (congrArg (fun t => ((restrictFunctorComp e f₁).hom.app M₁).app U ≫
      ((restrictFunctorIsoPullback f₁).hom.app M₁).app (e ''ᵁ U) ≫
      ((restrictFunctorIsoPullback e).hom.app ((pullback f₁).obj M₁)).app U ≫ 𝟙 _ ≫
      ((pullback e).map φ).app U ≫ t ≫
      ((restrictFunctorIsoPullback e).inv.app ((pullback f₂).obj M₂)).app U ≫
      ((restrictFunctorIsoPullback f₂).inv.app M₂).app (e ''ᵁ U) ≫
      ((restrictFunctorComp e f₂).inv.app M₂).app U) c2U).trans ?_

  refine (congrArg (fun t => ((restrictFunctorComp e f₁).hom.app M₁).app U ≫
      ((restrictFunctorIsoPullback f₁).hom.app M₁).app (e ''ᵁ U) ≫ t ≫
      ((restrictFunctorIsoPullback f₂).inv.app M₂).app (e ''ᵁ U) ≫
      ((restrictFunctorComp e f₂).inv.app M₂).app U) c3U).trans ?_
  rfl

noncomputable def toRestrict {Y : Scheme.{u}} (L₁ L₂ : Y.Modules) {X' : Scheme.{u}} (g : X' ⟶ Y) [IsOpenImmersion g]
    (θ : (pullback g).obj L₁ ⟶ (pullback g).obj L₂) : L₁.restrict g ⟶ L₂.restrict g :=
  (restrictFunctorIsoPullback g).hom.app L₁ ≫ θ ≫ (restrictFunctorIsoPullback g).inv.app L₂

theorem toRestrict_injective {Y : Scheme.{u}} (L₁ L₂ : Y.Modules) {X' : Scheme.{u}} (g : X' ⟶ Y) [IsOpenImmersion g] :
    Function.Injective (toRestrict L₁ L₂ g) := by
  intro θ θ' h
  simpa [toRestrict, cancel_epi, cancel_mono] using h

theorem toRestrict_map {Y : Scheme.{u}} (L₁ L₂ : Y.Modules) {X' : Scheme.{u}} (g : X' ⟶ Y) [IsOpenImmersion g]
    (t : L₁ ⟶ L₂) : toRestrict L₁ L₂ g ((pullback g).map t) = (restrictFunctor g).map t := by
  simp [toRestrict]

theorem toRestrict_pullHom {Y : Scheme.{u}} (L₁ L₂ : Y.Modules) {X₀ X₁ : Scheme.{u}} (h : X₀ ⟶ X₁) (g : X₁ ⟶ Y)
    (k : X₀ ⟶ Y) [IsOpenImmersion h] [IsOpenImmersion g] [IsOpenImmersion k] (hk : h ≫ g = k)
    (θ : (pullback g).obj L₁ ⟶ (pullback g).obj L₂) :
    toRestrict L₁ L₂ k (Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := Mdl)
        (X₁ := Y) (X₂ := Y) (M₁ := L₁) (M₂ := L₂) (f₁ := g) (f₂ := g) θ h k k hk hk) =
      (restrictFunctorCongr hk.symm).hom.app L₁ ≫ (restrictFunctorComp h g).hom.app L₁ ≫
        (restrictFunctor h).map (toRestrict L₁ L₂ g θ) ≫
          (restrictFunctorComp h g).inv.app L₂ ≫ (restrictFunctorCongr hk).hom.app L₂ := by
  simp only [toRestrict, Category.assoc]
  exact restrictFunctorIsoPullback_conj_pullHom h g g k k hk hk L₁ L₂ θ

section Elementwise

variable {Y : Scheme.{u}}

theorem mapEq (L : Y.Modules) {A B : Y.Opens} (p q : op A ⟶ op B) (x : Γ(L, A)) :
    L.presheaf.map p x = L.presheaf.map q x := by
  rw [presheaf_map_eq L p q]

theorem map_map (L : Y.Modules) {A B C : Y.Opens} (p : op A ⟶ op B) (q : op B ⟶ op C) (x : Γ(L, A)) :
    L.presheaf.map q (L.presheaf.map p x) = L.presheaf.map (p ≫ q) x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]

theorem map_id' (L : Y.Modules) {A : Y.Opens} (p : op A ⟶ op A) (x : Γ(L, A)) : L.presheaf.map p x = x := by
  rw [mapEq L p (𝟙 _) x, CategoryTheory.Functor.map_id]; rfl

theorem app_naturality_apply {M N : Y.Modules} (φ : M ⟶ N) {U V : Y.Opens} (i : op U ⟶ op V) (x : Γ(M, U)) :
    φ.app V (M.presheaf.map i x) = N.presheaf.map i (φ.app U x) := by
  have := ConcreteCategory.congr_hom (app_naturality φ i) x
  simpa only [ConcreteCategory.comp_apply] using this

theorem restrict_naturality_apply {X' : Scheme.{u}} (f : X' ⟶ Y) [IsOpenImmersion f] {M N : Y.Modules}
    (φ : M.restrict f ⟶ N.restrict f) {V V' : X'.Opens} (ρ : V' ⟶ V) (m : Γ(M, f ''ᵁ V)) :
    φ.app V' (M.presheaf.map (f.opensFunctor.map ρ).op m) = N.presheaf.map (f.opensFunctor.map ρ).op (φ.app V m) :=
  app_naturality_apply φ ρ.op m

theorem restrict_app_smul {X' : Scheme.{u}} (f : X' ⟶ Y) [IsOpenImmersion f] {M N : Y.Modules}
    (φ : M.restrict f ⟶ N.restrict f) (V : X'.Opens) (r : Γ(Y, f ''ᵁ V)) (m : Γ(M, f ''ᵁ V)) :
    φ.app V (r • m) = HSMul.hSMul (α := Γ(Y, f ''ᵁ V)) (β := Γ(N, f ''ᵁ V)) r (φ.app V m) := by
  have h := Scheme.Modules.Hom.app_smul φ (U := V) ((f.appIso V).hom r) (show Γ(M.restrict f, V) from m)
  change φ.app V ((f.appIso V).inv ((f.appIso V).hom r) • m) =
    HSMul.hSMul (α := Γ(Y, f ''ᵁ V)) (β := Γ(N, f ''ᵁ V)) ((f.appIso V).inv ((f.appIso V).hom r)) (φ.app V m) at h
  rwa [Iso.hom_inv_id_apply] at h

end Elementwise

section Glue

variable {Y : Scheme.{u}} {ι : Type v} {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ Y) [∀ i, IsOpenImmersion (f i)]
  (L₁ L₂ : Y.Modules)

private def _root_.AlgebraicGeometry.Scheme.Modules.HomZar.Compatible (ψ : ∀ i, L₁.restrict (f i) ⟶ L₂.restrict (f i)) : Prop :=
  ∀ (i j : ι) (V : (X i).Opens) (W : (X j).Opens) (hVW : (f i) ''ᵁ V = (f j) ''ᵁ W),
    L₁.presheaf.map (eqToHom hVW).op ≫ (ψ i).app V = (ψ j).app W ≫ L₂.presheaf.map (eqToHom hVW).op

p2m_export "AlgebraicGeometry.Scheme.Modules.HomZar" "Compatible"
theorem image_preimage_eq_of_le (i : ι) (O : Y.Opens) (hO : O ≤ (f i).opensRange) : (f i) ''ᵁ (f i) ⁻¹ᵁ O = O := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hO]

noncomputable def Ψ (ψ : ∀ i, L₁.restrict (f i) ⟶ L₂.restrict (f i)) (i : ι) (O : Y.Opens)
    (hO : O ≤ (f i).opensRange) : Γ(L₁, O) ⟶ Γ(L₂, O) :=
  L₁.presheaf.map (eqToHom (image_preimage_eq_of_le f i O hO)).op ≫ (ψ i).app ((f i) ⁻¹ᵁ O) ≫
    L₂.presheaf.map (eqToHom (image_preimage_eq_of_le f i O hO).symm).op

variable {f L₁ L₂}

theorem Ψ_apply (ψ : ∀ i, L₁.restrict (f i) ⟶ L₂.restrict (f i)) (i : ι) (O : Y.Opens)
    (hO : O ≤ (f i).opensRange) (s : Γ(L₁, O)) :
    Ψ f L₁ L₂ ψ i O hO s = L₂.presheaf.map (eqToHom (image_preimage_eq_of_le f i O hO).symm).op
      ((ψ i).app ((f i) ⁻¹ᵁ O) (L₁.presheaf.map (eqToHom (image_preimage_eq_of_le f i O hO)).op s)) := by
  simp only [Ψ, ConcreteCategory.comp_apply]
  rfl

theorem Ψ_res (ψ : ∀ i, L₁.restrict (f i) ⟶ L₂.restrict (f i)) (i : ι) (O O' : Y.Opens)
    (hO : O ≤ (f i).opensRange) (hO' : O' ≤ (f i).opensRange) (hle : O' ≤ O) (s : Γ(L₁, O)) :
    L₂.presheaf.map (homOfLE hle).op (Ψ f L₁ L₂ ψ i O hO s) = Ψ f L₁ L₂ ψ i O' hO' (L₁.presheaf.map (homOfLE hle).op s) := by
  rw [Ψ_apply, Ψ_apply, map_map]
  have hρ : (f i) ⁻¹ᵁ O' ≤ (f i) ⁻¹ᵁ O := fun x hx => hle hx
  rw [mapEq L₂ _ (((f i).opensFunctor.map (homOfLE hρ)).op ≫
      (eqToHom (image_preimage_eq_of_le f i O' hO').symm).op), ← map_map, ← restrict_naturality_apply,
    map_map, map_map]
  exact congrArg (fun y => L₂.presheaf.map (eqToHom (image_preimage_eq_of_le f i O' hO').symm).op
    ((ψ i).app ((f i) ⁻¹ᵁ O') y)) (mapEq L₁ _ _ s)

theorem Ψ_compat (ψ : ∀ i, L₁.restrict (f i) ⟶ L₂.restrict (f i)) (hψ : Compatible f L₁ L₂ ψ) (i j : ι)
    (O : Y.Opens) (hOi : O ≤ (f i).opensRange) (hOj : O ≤ (f j).opensRange) (s : Γ(L₁, O)) :
    Ψ f L₁ L₂ ψ i O hOi s = Ψ f L₁ L₂ ψ j O hOj s := by
  have E : (f i) ''ᵁ (f i) ⁻¹ᵁ O = (f j) ''ᵁ (f j) ⁻¹ᵁ O :=
    (image_preimage_eq_of_le f i O hOi).trans (image_preimage_eq_of_le f j O hOj).symm
  have H : (ψ i).app ((f i) ⁻¹ᵁ O) (L₁.presheaf.map (eqToHom E).op
      (L₁.presheaf.map (eqToHom (image_preimage_eq_of_le f j O hOj)).op s)) =
      L₂.presheaf.map (eqToHom E).op ((ψ j).app ((f j) ⁻¹ᵁ O)
        (L₁.presheaf.map (eqToHom (image_preimage_eq_of_le f j O hOj)).op s)) :=
    DFunLike.congr_fun (congrArg ConcreteCategory.hom (hψ i j ((f i) ⁻¹ᵁ O) ((f j) ⁻¹ᵁ O) E))
      (L₁.presheaf.map (eqToHom (image_preimage_eq_of_le f j O hOj)).op s)
  rw [map_map] at H
  rw [Ψ_apply, Ψ_apply, mapEq L₁ _ ((eqToHom (image_preimage_eq_of_le f j O hOj)).op ≫ (eqToHom E).op) s]
  refine (congrArg (fun y => L₂.presheaf.map (eqToHom (image_preimage_eq_of_le f i O hOi).symm).op y) H).trans ?_
  rw [map_map]
  exact mapEq L₂ _ _ _

theorem Ψ_smul (ψ : ∀ i, L₁.restrict (f i) ⟶ L₂.restrict (f i)) (i : ι) (O : Y.Opens)
    (hO : O ≤ (f i).opensRange) (r : Γ(Y, O)) (s : Γ(L₁, O)) :
    Ψ f L₁ L₂ ψ i O hO (r • s) = r • Ψ f L₁ L₂ ψ i O hO s := by
  rw [Ψ_apply, Ψ_apply, Scheme.Modules.map_smul, restrict_app_smul, Scheme.Modules.map_smul]
  congr 1
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]

  have : ((eqToHom (image_preimage_eq_of_le f i O hO)).op ≫ (eqToHom (image_preimage_eq_of_le f i O hO).symm).op :
      op O ⟶ op O) = 𝟙 _ := Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id]
  rfl

variable (f L₁ L₂)

theorem restrictFunctor_map_injective (hf : ∀ y : Y, ∃ i, y ∈ Set.range (f i).base)
    (t t' : L₁ ⟶ L₂) (h : ∀ i, (restrictFunctor (f i)).map t = (restrictFunctor (f i)).map t') : t = t' := by
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨L₂.presheaf, L₂.isSheaf⟩ (fun i => (f i) ''ᵁ (f i) ⁻¹ᵁ W) W
    (fun i => homOfLE ((f i).image_preimage_le W)) ?_ _ _ (fun i => ?_)
  · intro y hy
    obtain ⟨i, x, rfl⟩ := hf y
    exact Opens.mem_iSup.mpr ⟨i, ⟨x, hy, rfl⟩⟩
  · change L₂.presheaf.map _ (t.app W s) = L₂.presheaf.map _ (t'.app W s)
    rw [← app_naturality_apply, ← app_naturality_apply]
    exact ConcreteCategory.congr_hom (congrArg (fun φ => Scheme.Modules.Hom.app φ ((f i) ⁻¹ᵁ W)) (h i)) _

end Glue

section Glue2

variable {Y : Scheme.{u}} {ι : Type v} {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ Y) [∀ i, IsOpenImmersion (f i)]
  (L₁ L₂ : Y.Modules)

noncomputable abbrev F₂ : TopCat.Sheaf Ab Y.carrier := ⟨L₂.presheaf, L₂.isSheaf⟩

theorem cover_le_iSup (hf : ∀ y : Y, ∃ i, y ∈ Set.range (f i).base) (W : Y.Opens) :
    W ≤ ⨆ i, (f i) ''ᵁ (f i) ⁻¹ᵁ W := by
  intro y hy
  obtain ⟨i, x, rfl⟩ := hf y
  exact Opens.mem_iSup.mpr ⟨i, ⟨x, hy, rfl⟩⟩

theorem image_preimage_le_opensRange (i : ι) (W : Y.Opens) : (f i) ''ᵁ (f i) ⁻¹ᵁ W ≤ (f i).opensRange := by
  rintro _ ⟨x, -, rfl⟩; exact ⟨x, rfl⟩

variable {f L₁ L₂}
variable (ψ : ∀ i, L₁.restrict (f i) ⟶ L₂.restrict (f i)) (hψ : Compatible f L₁ L₂ ψ)
  (hf : ∀ y : Y, ∃ i, y ∈ Set.range (f i).base)

noncomputable def locSec (W : Y.Opens) (s : Γ(L₁, W)) (i : ι) : Γ(L₂, (f i) ''ᵁ (f i) ⁻¹ᵁ W) :=
  Ψ f L₁ L₂ ψ i _ (image_preimage_le_opensRange f i W) (L₁.presheaf.map (homOfLE ((f i).image_preimage_le W)).op s)

include hψ in
theorem locSec_compatible (W : Y.Opens) (s : Γ(L₁, W)) :
    L₂.presheaf.IsCompatible (fun i => (f i) ''ᵁ (f i) ⁻¹ᵁ W) (locSec ψ W s) := by
  intro i j
  change L₂.presheaf.map _ (locSec ψ W s i) = L₂.presheaf.map _ (locSec ψ W s j)
  simp only [locSec]
  have hi : (f i) ''ᵁ (f i) ⁻¹ᵁ W ⊓ (f j) ''ᵁ (f j) ⁻¹ᵁ W ≤ (f i).opensRange :=
    inf_le_left.trans (image_preimage_le_opensRange f i W)
  have hj : (f i) ''ᵁ (f i) ⁻¹ᵁ W ⊓ (f j) ''ᵁ (f j) ⁻¹ᵁ W ≤ (f j).opensRange :=
    inf_le_right.trans (image_preimage_le_opensRange f j W)
  rw [mapEq L₂ _ (homOfLE inf_le_left).op, Ψ_res ψ i _ _ _ hi inf_le_left, map_map,
    mapEq L₂ _ (homOfLE inf_le_right).op (Ψ f L₁ L₂ ψ j _ _ _), Ψ_res ψ j _ _ _ hj inf_le_right, map_map,
    Ψ_compat ψ hψ i j _ hi hj]
  try exact congrArg (fun y => Ψ f L₁ L₂ ψ j _ hj y) (mapEq L₁ _ _ s)

noncomputable def glue (W : Y.Opens) (s : Γ(L₁, W)) : Γ(L₂, W) :=
  (TopCat.Sheaf.existsUnique_gluing' (F₂ L₂) (fun i => (f i) ''ᵁ (f i) ⁻¹ᵁ W) W (fun i => homOfLE ((f i).image_preimage_le W))
    (cover_le_iSup f hf W) (locSec ψ W s) (locSec_compatible ψ hψ W s)).choose

theorem glue_spec (W : Y.Opens) (s : Γ(L₁, W)) (i : ι) :
    L₂.presheaf.map (homOfLE ((f i).image_preimage_le W)).op (glue ψ hψ hf W s) = locSec ψ W s i :=
  (TopCat.Sheaf.existsUnique_gluing' (F₂ L₂) (fun i => (f i) ''ᵁ (f i) ⁻¹ᵁ W) W (fun i => homOfLE ((f i).image_preimage_le W))
    (cover_le_iSup f hf W) (locSec ψ W s) (locSec_compatible ψ hψ W s)).choose_spec.1 i

theorem glue_unique (W : Y.Opens) (s : Γ(L₁, W)) (y : Γ(L₂, W))
    (hy : ∀ i, L₂.presheaf.map (homOfLE ((f i).image_preimage_le W)).op y = locSec ψ W s i) :
    y = glue ψ hψ hf W s :=
  (TopCat.Sheaf.existsUnique_gluing' (F₂ L₂) (fun i => (f i) ''ᵁ (f i) ⁻¹ᵁ W) W (fun i => homOfLE ((f i).image_preimage_le W))
    (cover_le_iSup f hf W) (locSec ψ W s) (locSec_compatible ψ hψ W s)).choose_spec.2 y hy

theorem glue_add (W : Y.Opens) (s s' : Γ(L₁, W)) :
    glue ψ hψ hf W (s + s') = glue ψ hψ hf W s + glue ψ hψ hf W s' := by
  refine (glue_unique ψ hψ hf W (s + s') _ fun i => ?_).symm
  rw [map_add, glue_spec, glue_spec]
  simp only [locSec, map_add]

theorem glue_smul (W : Y.Opens) (r : Γ(Y, W)) (s : Γ(L₁, W)) :
    glue ψ hψ hf W (r • s) = r • glue ψ hψ hf W s := by
  refine (glue_unique ψ hψ hf W (r • s) _ fun i => ?_).symm
  rw [Scheme.Modules.map_smul, glue_spec]
  simp only [locSec, Scheme.Modules.map_smul, Ψ_smul]

theorem glue_res {W W' : Y.Opens} (hle : W' ≤ W) (s : Γ(L₁, W)) :
    L₂.presheaf.map (homOfLE hle).op (glue ψ hψ hf W s) = glue ψ hψ hf W' (L₁.presheaf.map (homOfLE hle).op s) := by
  refine glue_unique ψ hψ hf W' _ _ fun i => ?_
  have hle' : (f i) ''ᵁ (f i) ⁻¹ᵁ W' ≤ (f i) ''ᵁ (f i) ⁻¹ᵁ W := by
    rintro _ ⟨x, hx, rfl⟩; exact ⟨x, hle hx, rfl⟩
  rw [map_map, mapEq L₂ _ ((homOfLE ((f i).image_preimage_le W)).op ≫ (homOfLE hle').op), ← map_map, glue_spec]
  simp only [locSec]
  rw [Ψ_res ψ i _ _ _ (image_preimage_le_opensRange f i W') hle', map_map, map_map]
  try exact congrArg (fun y => Ψ f L₁ L₂ ψ i _ (image_preimage_le_opensRange f i W') y) (mapEq L₁ _ _ s)

noncomputable def gluePresheafHom : L₁.presheaf ⟶ L₂.presheaf where
  app W := AddCommGrpCat.ofHom
    { toFun := glue ψ hψ hf W.unop
      map_zero' := by
        have h0 := glue_add ψ hψ hf W.unop 0 0
        rw [add_zero] at h0
        exact left_eq_add.mp h0
      map_add' := glue_add ψ hψ hf W.unop }
  naturality {W W'} i := by
    ext s
    change glue ψ hψ hf W'.unop (L₁.presheaf.map i s) = L₂.presheaf.map i (glue ψ hψ hf W.unop s)
    rw [mapEq L₁ i (homOfLE i.unop.le).op, mapEq L₂ i (homOfLE i.unop.le).op, glue_res]

noncomputable def glueHom : L₁ ⟶ L₂ :=
  ⟨PresheafOfModules.homMk (gluePresheafHom ψ hψ hf) (fun W r m => glue_smul ψ hψ hf W.unop r m)⟩

theorem glueHom_app (W : Y.Opens) (s : Γ(L₁, W)) : (glueHom ψ hψ hf).app W s = glue ψ hψ hf W s := rfl

include hψ in

theorem glue_image (i : ι) (V : (X i).Opens) (m : Γ(L₁, (f i) ''ᵁ V)) :
    glue ψ hψ hf ((f i) ''ᵁ V) m = (ψ i).app V m := by
  symm
  have hO : (f i) ''ᵁ V ≤ (f i).opensRange := by rintro _ ⟨x, -, rfl⟩; exact ⟨x, rfl⟩

  have hΨ : (ψ i).app V m = Ψ f L₁ L₂ ψ i ((f i) ''ᵁ V) hO m := by
    rw [Ψ_apply]
    have hV : (f i) ⁻¹ᵁ (f i) ''ᵁ V = V := (f i).preimage_image_eq V

    have nat := restrict_naturality_apply (f i) (ψ i) (eqToHom hV) m
    rw [mapEq L₁ _ ((f i).opensFunctor.map (eqToHom hV)).op m, nat, map_map, map_id']
  rw [hΨ]
  refine glue_unique ψ hψ hf _ m _ fun j => ?_
  simp only [locSec]
  have hj : (f j) ''ᵁ (f j) ⁻¹ᵁ (f i) ''ᵁ V ≤ (f j).opensRange := image_preimage_le_opensRange f j _
  have hi : (f j) ''ᵁ (f j) ⁻¹ᵁ (f i) ''ᵁ V ≤ (f i).opensRange := ((f j).image_preimage_le _).trans hO
  rw [Ψ_res ψ i _ _ hO hi ((f j).image_preimage_le _), Ψ_compat ψ hψ i j _ hi hj]

variable (f L₁ L₂)

include hψ hf in

theorem exists_restrictFunctor_map_eq :
    ∃ t : L₁ ⟶ L₂, ∀ i, (restrictFunctor (f i)).map t = ψ i :=
  ⟨glueHom ψ hψ hf, fun i => Scheme.Modules.hom_ext _ _ fun V => by
    ext m
    exact glue_image ψ hψ hf i V m⟩

end Glue2

section Assembly

variable {Y : Scheme.{u}} {ι : Type v} {V : ι → Scheme.{u}} (g : ∀ i, V i ⟶ Y) [∀ i, IsOpenImmersion (g i)]
  (L₁ L₂ : Y.Modules)

theorem presheafHom_map_homMk (t : L₁ ⟶ L₂) (i : ι) :
    (Mdl.presheafHom L₁ L₂).map (Over.homMk (g i) : Over.mk (g i) ⟶ Over.mk (𝟙 Y)).op
        (Mdl.presheafHomObjHomEquiv t) = (pullback (g i)).map t := by
  have := congrArg (fun ξ => Pseudofunctor.DescentData.Hom.hom ξ i)
    (Pseudofunctor.DescentData.subtypeCompatibleHomEquiv_toCompatible_presheafHomObjHomEquiv (F := Mdl) g t)
  exact this

theorem image_top_lift {U Y : Scheme.{u}} (f : U ⟶ Y) [IsOpenImmersion f] (A : U.Opens) (O : Y.Opens)
    (hO : O = f ''ᵁ A) (H : Set.range ⇑O.ι ⊆ Set.range ⇑f) : IsOpenImmersion.lift f O.ι H ''ᵁ ⊤ = A := by
  subst hO
  have hfac : ∀ o, f ((IsOpenImmersion.lift f (f ''ᵁ A).ι H) o) = ((f ''ᵁ A).ι) o := fun o => by
    rw [← Scheme.Hom.comp_apply, IsOpenImmersion.lift_fac]
  apply TopologicalSpace.Opens.ext
  simp only [Scheme.Hom.coe_image, TopologicalSpace.Opens.coe_top, Set.image_univ]
  ext v
  constructor
  · rintro ⟨o, rfl⟩
    have ho : o.1 ∈ (f : U → Y) '' (A : Set U) := o.2
    obtain ⟨a, ha, hao⟩ := ho
    have : f a = f ((IsOpenImmersion.lift f (f ''ᵁ A).ι H) o) := by
      rw [hfac, Scheme.Opens.ι_apply]; exact hao
    change (IsOpenImmersion.lift f (f ''ᵁ A).ι H) o ∈ (A : Set U)
    rwa [← f.isOpenEmbedding.injective this]
  · intro hv
    refine ⟨⟨f v, ⟨v, hv, rfl⟩⟩, f.isOpenEmbedding.injective ?_⟩
    rw [hfac, Scheme.Opens.ι_apply]

set_option maxRecDepth 20000 in

theorem conj_apply {X₀ X₁ : Scheme.{u}} (h : X₀ ⟶ X₁) (g' : X₁ ⟶ Y) (k : X₀ ⟶ Y)
    [IsOpenImmersion h] [IsOpenImmersion g'] [IsOpenImmersion k] (hk : h ≫ g' = k)
    (ψ : L₁.restrict g' ⟶ L₂.restrict g') (U : X₀.Opens) (m : Γ(L₁, k ''ᵁ U)) :
    ((restrictFunctorCongr hk.symm).hom.app L₁ ≫ (restrictFunctorComp h g').hom.app L₁ ≫
        (restrictFunctor h).map ψ ≫ (restrictFunctorComp h g').inv.app L₂ ≫ (restrictFunctorCongr hk).hom.app L₂).app U m =
      L₂.presheaf.map (eqToHom (show k ''ᵁ U = (h ≫ g') ''ᵁ U by subst hk; rfl)).op
        (L₂.presheaf.map (eqToHom (Scheme.Hom.comp_image h g' U)).op
          (ψ.app (h ''ᵁ U) (L₁.presheaf.map (eqToHom (Scheme.Hom.comp_image h g' U).symm).op
            (L₁.presheaf.map (eqToHom (show (h ≫ g') ''ᵁ U = k ''ᵁ U by subst hk; rfl)).op m)))) := by
  rfl

set_option maxHeartbeats 3200000 in

theorem compatible_of_arrowsCompatible
    (x : ∀ i, (Mdl.presheafHom L₁ L₂).obj (op (Over.mk (g i))))
    (hx : Presieve.Arrows.Compatible (Mdl.presheafHom L₁ L₂) (B := Over.mk (𝟙 Y))
      (X := fun i => Over.mk (g i)) (fun i => Over.homMk (g i)) x) :
    Compatible g L₁ L₂ (fun i => toRestrict L₁ L₂ (g i) (x i)) := by
  intro i j A B hAB

  have hOi : Set.range ⇑((g i) ''ᵁ A).ι ⊆ Set.range ⇑(g i) := by
    rw [Scheme.Opens.range_ι]; rintro _ ⟨a, -, rfl⟩; exact ⟨a, rfl⟩
  have hOj : Set.range ⇑((g i) ''ᵁ A).ι ⊆ Set.range ⇑(g j) := by
    rw [Scheme.Opens.range_ι, hAB]; rintro _ ⟨b, -, rfl⟩; exact ⟨b, rfl⟩
  have he₁ : IsOpenImmersion.lift (g i) ((g i) ''ᵁ A).ι hOi ≫ g i = ((g i) ''ᵁ A).ι := IsOpenImmersion.lift_fac _ _ _
  have he₂ : IsOpenImmersion.lift (g j) ((g i) ''ᵁ A).ι hOj ≫ g j = ((g i) ''ᵁ A).ι := IsOpenImmersion.lift_fac _ _ _

  have hE₀ : ((g i) ''ᵁ A).ι ''ᵁ ⊤ = (g i) ''ᵁ A := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
  have EA : IsOpenImmersion.lift (g i) ((g i) ''ᵁ A).ι hOi ''ᵁ ⊤ = A :=
    image_top_lift (g i) A ((g i) ''ᵁ A) rfl hOi
  have EB : IsOpenImmersion.lift (g j) ((g i) ''ᵁ A).ι hOj ''ᵁ ⊤ = B :=
    image_top_lift (g j) B ((g i) ''ᵁ A) hAB hOj

  have H := hx i j (Over.mk ((g i) ''ᵁ A).ι) (Over.homMk _ he₁) (Over.homMk _ he₂) (by ext; simp [he₁, he₂])
  have H' := congrArg (toRestrict L₁ L₂ ((g i) ''ᵁ A).ι) H
  have H₁ := toRestrict_pullHom L₁ L₂ (IsOpenImmersion.lift (g i) ((g i) ''ᵁ A).ι hOi) (g i) ((g i) ''ᵁ A).ι
    he₁ (x i)
  have H₂ := toRestrict_pullHom L₁ L₂ (IsOpenImmersion.lift (g j) ((g i) ''ᵁ A).ι hOj) (g j) ((g i) ''ᵁ A).ι
    he₂ (x j)
  have Hc := H₁.symm.trans (H'.trans H₂)

  ext m
  change (toRestrict L₁ L₂ (g i) (x i)).app A (L₁.presheaf.map (eqToHom hAB).op m) =
    L₂.presheaf.map (eqToHom hAB).op ((toRestrict L₁ L₂ (g j) (x j)).app B m)
  have H'' := congrArg (fun χ => Scheme.Modules.Hom.app χ ⊤ (L₁.presheaf.map (eqToHom (hE₀.trans hAB)).op m)) Hc
  dsimp only at H''
  rw [conj_apply, conj_apply] at H''
  simp only [map_map] at H''

  rw [mapEq L₁ _ ((eqToHom hAB).op ≫ ((g i).opensFunctor.map (eqToHom EA)).op) m, ← map_map L₁,
    restrict_naturality_apply, map_map] at H''
  rw [mapEq L₁ _ ((g j).opensFunctor.map (eqToHom EB)).op m, restrict_naturality_apply, map_map] at H''

  have H3 := congrArg (fun y => L₂.presheaf.map (eqToHom (hE₀ : ((g i) ''ᵁ A).ι ''ᵁ ⊤ = (g i) ''ᵁ A).symm).op y) H''
  simp only [map_map] at H3
  rw [map_id'] at H3
  exact H3.trans (mapEq L₂ _ _ _)

theorem main (hg : ∀ y : Y, ∃ i, y ∈ Set.range (g i).base) :
    Function.Bijective ((Mdl.toDescentData g).map : (L₁ ⟶ L₂) → _) := by
  rw [Pseudofunctor.bijective_toDescentData_map_iff, Presieve.isSheafFor_arrows_iff]
  intro x hx
  have hψ := compatible_of_arrowsCompatible g L₁ L₂ x hx
  obtain ⟨t, ht⟩ := exists_restrictFunctor_map_eq g L₁ L₂ _ hψ hg
  have key : ∀ (t' : L₁ ⟶ L₂), (∀ i, (Mdl.presheafHom L₁ L₂).map
      (Over.homMk (g i) : Over.mk (g i) ⟶ Over.mk (𝟙 Y)).op (Mdl.presheafHomObjHomEquiv t') = x i) ↔
      ∀ i, (restrictFunctor (g i)).map t' = toRestrict L₁ L₂ (g i) (x i) := fun t' => by
    refine forall_congr' fun i => ?_
    rw [presheafHom_map_homMk, ← toRestrict_map]
    exact ⟨congrArg _, fun h => toRestrict_injective L₁ L₂ (g i) h⟩
  refine ⟨Mdl.presheafHomObjHomEquiv t, (key t).mpr ht, fun t' ht' => ?_⟩
  obtain ⟨t₀, rfl⟩ := (Mdl.presheafHomObjHomEquiv (M := L₁) (N := L₂)).surjective t'
  congr 1
  exact restrictFunctor_map_injective g L₁ L₂ hg _ _ fun i => ((key t₀).mp ht' i).trans (ht i).symm

end Assembly

end AlgebraicGeometry.Scheme.Modules.HomZar

theorem solution
    {Y : Scheme.{u}} {ι : Type v} {V : ι → Scheme.{u}} (g : ∀ i, V i ⟶ Y) [∀ i, IsOpenImmersion (g i)]
    (hg : ∀ y : Y, ∃ i, y ∈ Set.range (g i).base) (L₁ L₂ : Y.Modules) :
    Function.Bijective
      ((((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData g).map : (L₁ ⟶ L₂) → _) :=
  AlgebraicGeometry.Scheme.Modules.HomZar.main g L₁ L₂ hg

end S_AlgebraicGeometry_Scheme_Modules_toDescentData_map_bijective_of_openCover
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_toDescentData_map_bijective_of_openCover (solution)
