-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.toDescentData_essSurj_of_openCover
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/1f0ab9f3-f371-5857-9482-c408ab520ee1

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_toDescentData_essSurj_of_openCover

set_option autoImplicit false
set_option maxHeartbeats 1600000

universe v v' u

p2m_open "CategoryTheory P2MW.S_AlgebraicGeometry_Scheme_Modules_toDescentData_essSurj_of_openCover.CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_toDescentData_essSurj_of_openCover.AlgebraicGeometry Opposite TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.hom_ext Scheme.opensRange_homOfLE IsOpenImmersion.lift Scheme.Modules.pseudofunctor Surjective Scheme.Opens.range_ι Scheme.Hom Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Scheme.Hom.image_preimage_eq_opensRange_inf Scheme.Hom.image_preimage_le Scheme Scheme.Modules.Hom.id_app Scheme.Modules.Hom.app IsOpenImmersion Scheme.homOfLE_homOfLE Scheme.Modules.pullbackCongr Scheme.Modules Scheme.Opens Scheme.homOfLE_ι Scheme.Opens.ι_preimage_self IsOpenImmersion.lift_fac Scheme.Modules.pullbackComp"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.hom_ext opensRange_homOfLE forget Modules.pseudofunctor Hom.id_app Opens.range_ι Hom mk Γ Modules.Hom.comp_app Hom.app Modules.Hom Hom.image_preimage_eq_opensRange_inf Hom.image_preimage_le Modules.Hom.id_app Modules.Hom.app restrictFunctor homOfLE_homOfLE Hom.comp_app Modules.pullbackCongr Modules Opens homOfLE_ι Hom.opensFunctor grothendieckTopology Opens.ι_preimage_self restrict PresheafOfModules Modules.pullbackComp evaluation"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "hom_ext pushforwardCongr Hom.app_smul pseudofunctor pushforward pushforwardComp pullback presheaf restrictAdjunction_unit_app_app Hom.comp_app pushforwardComp_hom_app_app Hom pushforward_map_app restrictFunctorCongr restrictFunctor Hom.id_app Hom.app restrictFunctorIsoPullback restrictFunctorComp_hom_app_app restrict_map restrictFunctorComp_inv_app_app restrictAdjunction restrictFunctorCongr_hom_app_app pullbackCongr isSheaf Hom.isIso_iff_isIso_app pullbackPushforwardAdjunction restrictFunctorComp restrict conjugateEquiv_pullbackComp_inv map_smul pushforwardCongr_hom_app_app restrictAdjunction_counit_app_app pullbackComp"
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

end AlgebraicGeometry.Scheme.Modules.HomZar

namespace CategoryTheory
p2m_export "CategoryTheory" "Cat Category unit_conjugateEquiv Sieve.generate_le_iff eqToIso cancel_epi ConcreteCategory.congr_hom Category.comp_id Pseudofunctor.DescentData.exists_equivalence_of_sieve_eq isoMk Bicategory Iso.eq_comp_inv NatTrans inclusion Pseudofunctor.LocallyDiscreteOpToCat.pullHom Iso.hom_inv_id_app Functor.comp_obj hom_comp eqToIso.hom Pseudofunctor.DescentData.isoMk Injective Functor Pseudofunctor inv Functor.comp_map Functor.map_id Iso.app_inv Iso.inv eqToHom_trans_assoc Iso.app_hom over Presieve.ofArrows Presheaf.IsSheaf evaluation Sieve.ofArrows Functor.mapIso_hom Functor.map_comp Iso.trans_inv LocallyDiscrete Pseudofunctor.mapComp'_eq_mapComp isIso_iff_bijective IsIso eqToIso_refl Adjunction.homEquiv_unit eqToHom_app Sheaf Functor.essSurj_of_iso Functor.essSurj_comp Iso.hom_inv_id_app_assoc Iso.symm_hom Iso.ext Iso.inv_hom_id_app_assoc Iso.inv_hom_id_app isIso_of_reflects_iso Functor.id_obj Functor.mapIso_inv Category.id_comp Iso.trans_hom eqToHom_refl ConcreteCategory.comp_apply Functor.essSurj_of_comp_fully_faithful comp_apply NatTrans.id_app Bicategory.Adj Pseudofunctor.DescentData Sieve Adjunction.homEquiv_leftAdjointUniq_hom_app Presieve Bicategory.Adj.forget₁ Adjunction.comp_unit_app Adjunction.unit_leftAdjointUniq_hom_app cancel_mono ConcreteCategory homOfLE Iso Adjunction eqToHom Presieve.ofArrows.mk Iso.refl_hom forget Pseudofunctor.DescentData.iso_hom asIso Category.assoc"
namespace Pseudofunctor
p2m_export "CategoryTheory.Pseudofunctor" "DescentData.exists_equivalence_of_sieve_eq LocallyDiscreteOpToCat.pullHom DescentData.isoMk mapComp' id mapComp'_eq_mapComp mapComp comp mk DescentData toDescentData mapComp'_hom_naturality DescentData.iso_hom"
namespace LocallyDiscreteOpToCat
p2m_export "CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat" "pullHom"
p2m_open "CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat CategoryTheory.Pseudofunctor CategoryTheory"

variable {C : Type*} [Category C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}

set_option backward.isDefEq.respectTransparency false in
theorem pullHom_comp' ⦃X₁ X₂ X₃ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄ ⦃M₃ : F.obj (.mk (op X₃))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄ ⦃f₃ : Y ⟶ X₃⦄
    (a : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (b : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶ (F.map f₃.op.toLoc).toFunctor.obj M₃)
    ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (gf₃ : Y' ⟶ X₃)
    (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) (h₃ : g ≫ f₃ = gf₃) :
    pullHom (a ≫ b) g gf₁ gf₃ h₁ h₃ = pullHom a g gf₁ gf₂ h₁ h₂ ≫ pullHom b g gf₂ gf₃ h₂ h₃ := by
  simp [pullHom, Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
theorem map_map_eq_pullHom ⦃X Y : C⦄ (f : Y ⟶ X) ⦃M N : F.obj (.mk (op X))⦄ (ψ : M ⟶ N) ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gf : Y' ⟶ X) (hgf : g ≫ f = gf) :
    (F.map gf.op.toLoc).toFunctor.map ψ = pullHom ((F.map f.op.toLoc).toFunctor.map ψ) g gf gf hgf hgf := by
  dsimp only [pullHom]
  rw [← Category.assoc, ← F.mapComp'_hom_naturality f.op.toLoc g.op.toLoc gf.op.toLoc (by rw [← hgf]; rfl) ψ,
    Category.assoc]
  simp

end CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.hom_ext Scheme.opensRange_homOfLE IsOpenImmersion.lift Scheme.Modules.pseudofunctor Surjective Scheme.Opens.range_ι Scheme.Hom Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Scheme.Hom.image_preimage_eq_opensRange_inf Scheme.Hom.image_preimage_le Scheme Scheme.Modules.Hom.id_app Scheme.Modules.Hom.app IsOpenImmersion Scheme.homOfLE_homOfLE Scheme.Modules.pullbackCongr Scheme.Modules Scheme.Opens Scheme.homOfLE_ι Scheme.Opens.ι_preimage_self IsOpenImmersion.lift_fac Scheme.Modules.pullbackComp"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.hom_ext opensRange_homOfLE forget Modules.pseudofunctor Hom.id_app Opens.range_ι Hom mk Γ Modules.Hom.comp_app Hom.app Modules.Hom Hom.image_preimage_eq_opensRange_inf Hom.image_preimage_le Modules.Hom.id_app Modules.Hom.app restrictFunctor homOfLE_homOfLE Hom.comp_app Modules.pullbackCongr Modules Opens homOfLE_ι Hom.opensFunctor grothendieckTopology Opens.ι_preimage_self restrict PresheafOfModules Modules.pullbackComp evaluation"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "hom_ext pushforwardCongr Hom.app_smul pseudofunctor pushforward pushforwardComp pullback presheaf restrictAdjunction_unit_app_app Hom.comp_app pushforwardComp_hom_app_app Hom pushforward_map_app restrictFunctorCongr restrictFunctor Hom.id_app Hom.app restrictFunctorIsoPullback restrictFunctorComp_hom_app_app restrict_map restrictFunctorComp_inv_app_app restrictAdjunction restrictFunctorCongr_hom_app_app pullbackCongr isSheaf Hom.isIso_iff_isIso_app pullbackPushforwardAdjunction restrictFunctorComp restrict conjugateEquiv_pullbackComp_inv map_smul pushforwardCongr_hom_app_app restrictAdjunction_counit_app_app pullbackComp"
namespace ObjGlue
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

noncomputable abbrev MOD : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat :=
  (Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁

theorem keyMC {a b d : LocallyDiscrete Scheme.{u}ᵒᵖ} (u' : a ⟶ b) (v' : b ⟶ d) (M : MOD.obj a) :
    (MOD.mapComp' u' v' (u' ≫ v') rfl).hom.toNatTrans.app M = (MOD.mapComp u' v').hom.toNatTrans.app M := by
  rw [Pseudofunctor.mapComp'_eq_mapComp]

theorem mapComp'_hom_app_eq {X X' Z : Scheme.{u}} (f : X ⟶ X') (g : X' ⟶ Z) (L : Z.Modules) (fg : X ⟶ Z) (h : f ≫ g = fg) :
    (MOD.mapComp' g.op.toLoc f.op.toLoc fg.op.toLoc (by rw [← h]; rfl)).hom.toNatTrans.app L =
    (Scheme.Modules.pullbackCongr h.symm).hom.app L ≫ (Scheme.Modules.pullbackComp f g).inv.app L := by
  subst h
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  exact keyMC g.op.toLoc f.op.toLoc L

set_option maxHeartbeats 3200000 in

theorem crux_MOD {Z' Z X₁ X₂ : Scheme.{u}} (e : Z' ⟶ Z) (f₁ : Z ⟶ X₁) (f₂ : Z ⟶ X₂)
    (gf₁ : Z' ⟶ X₁) (gf₂ : Z' ⟶ X₂) [IsOpenImmersion e] [IsOpenImmersion f₁] [IsOpenImmersion f₂]
    [IsOpenImmersion gf₁] [IsOpenImmersion gf₂] (h₁ : e ≫ f₁ = gf₁) (h₂ : e ≫ f₂ = gf₂)
    (M₁ : X₁.Modules) (M₂ : X₂.Modules)
    (φ : (MOD.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (MOD.map f₂.op.toLoc).toFunctor.obj M₂) :
    (restrictFunctorIsoPullback gf₁).hom.app M₁ ≫
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := MOD) φ e gf₁ gf₂ h₁ h₂ ≫
        (restrictFunctorIsoPullback gf₂).inv.app M₂ =
      (restrictFunctorCongr h₁.symm).hom.app M₁ ≫ (restrictFunctorComp e f₁).hom.app M₁ ≫
        (restrictFunctor e).map ((restrictFunctorIsoPullback f₁).hom.app M₁ ≫ φ ≫
          (restrictFunctorIsoPullback f₂).inv.app M₂) ≫
        (restrictFunctorComp e f₂).inv.app M₂ ≫ (restrictFunctorCongr h₂).hom.app M₂ :=
  HomZar.restrictFunctorIsoPullback_conj_pullHom e f₁ f₂ gf₁ gf₂ h₁ h₂ M₁ M₂ φ

section WLOG
variable {Y : Scheme.{u}} {ι : Type v} {V : ι → Scheme.{u}} (g : ∀ i, V i ⟶ Y) [∀ i, IsOpenImmersion (g i)]

abbrev Ranges : Type u := {O : Y.Opens // ∃ i, (g i).opensRange = O}

theorem sieve_ofArrows_eq_opensRange :
    Sieve.ofArrows _ g = Sieve.ofArrows (fun O : Ranges g => ((O.1 : Y.Opens) : Scheme.{u})) (fun O => O.1.ι) := by
  apply le_antisymm
  · rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro Z _ ⟨i⟩
    exact ⟨_, (g i).isoOpensRange.hom, (⟨(g i).opensRange, i, rfl⟩ : Ranges g).1.ι,
      Presieve.ofArrows.mk (⟨(g i).opensRange, i, rfl⟩ : Ranges g), (g i).isoOpensRange_hom_ι⟩
  · rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro Z _ ⟨O⟩
    obtain ⟨O, i, rfl⟩ := O
    exact ⟨_, (g i).isoOpensRange.inv, g i, Presieve.ofArrows.mk i, (g i).isoOpensRange_inv_comp⟩

omit [∀ i, IsOpenImmersion (g i)] in

theorem essSurj_iff_of_sieve_eq {ι' : Type v'} {V' : ι' → Scheme.{u}} (g' : ∀ i, V' i ⟶ Y)
    (h : Sieve.ofArrows _ g = Sieve.ofArrows _ g') :
    (MOD.toDescentData g).EssSurj ↔ (MOD.toDescentData g').EssSurj := by
  obtain ⟨e, ⟨iso⟩⟩ := Pseudofunctor.DescentData.exists_equivalence_of_sieve_eq MOD g g' h
  constructor
  · intro _
    haveI : (MOD.toDescentData g ⋙ e.functor).EssSurj := Functor.essSurj_comp _ _
    exact Functor.essSurj_of_iso iso
  · intro _
    haveI : (MOD.toDescentData g ⋙ e.functor).EssSurj := Functor.essSurj_of_iso iso.symm
    exact Functor.essSurj_of_comp_fully_faithful _ e.functor

end WLOG

section Opens
variable {Y : Scheme.{u}} {ι : Type u} (U : ι → Y.Opens)

abbrev incl (i : ι) : (U i : Scheme.{u}) ⟶ Y := (U i).ι

noncomputable abbrev p₁ (i j : ι) : ((U i ⊓ U j : Y.Opens) : Scheme.{u}) ⟶ (U i : Scheme.{u}) := Y.homOfLE inf_le_left
noncomputable abbrev p₂ (i j : ι) : ((U i ⊓ U j : Y.Opens) : Scheme.{u}) ⟶ (U j : Scheme.{u}) := Y.homOfLE inf_le_right

variable (D : (MOD.{u}).DescentData (incl U))

noncomputable abbrev Dobj (i : ι) : ((U i : Y.Opens) : Scheme.{u}).Modules := D.obj i

theorem D_pullHom ⦃Z Z' : Scheme.{u}⦄ (φ : Z' ⟶ Z) (q : Z ⟶ Y) (q' : Z' ⟶ Y) (hq : φ ≫ q = q') ⦃i j : ι⦄
    (f₁ : Z ⟶ (U i : Scheme.{u})) (f₂ : Z ⟶ (U j : Scheme.{u})) (hf₁ : f₁ ≫ incl U i = q) (hf₂ : f₂ ≫ incl U j = q)
    (g₁ : Z' ⟶ (U i : Scheme.{u})) (g₂ : Z' ⟶ (U j : Scheme.{u})) (hg₁ : φ ≫ f₁ = g₁) (hg₂ : φ ≫ f₂ = g₂)
    (hg₁' : g₁ ≫ incl U i = q') (hg₂' : g₂ ≫ incl U j = q') :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (D.hom q f₁ f₂ hf₁ hf₂) φ g₁ g₂ hg₁ hg₂ =
      D.hom q' g₁ g₂ hg₁' hg₂' :=
  D.pullHom_hom φ q q' hq f₁ f₂ hf₁ hf₂ g₁ g₂ hg₁ hg₂

theorem ofObj_pullHom (M : Y.Modules) ⦃Z Z' : Scheme.{u}⦄ (φ : Z' ⟶ Z) (q : Z ⟶ Y) (q' : Z' ⟶ Y) (hq : φ ≫ q = q')
    ⦃i j : ι⦄ (f₁ : Z ⟶ (U i : Scheme.{u})) (f₂ : Z ⟶ (U j : Scheme.{u})) (hf₁ : f₁ ≫ incl U i = q)
    (hf₂ : f₂ ≫ incl U j = q) (g₁ : Z' ⟶ (U i : Scheme.{u})) (g₂ : Z' ⟶ (U j : Scheme.{u})) (hg₁ : φ ≫ f₁ = g₁)
    (hg₂ : φ ≫ f₂ = g₂) (hg₁' : g₁ ≫ incl U i = q') (hg₂' : g₂ ≫ incl U j = q') :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (((MOD.toDescentData (incl U)).obj M).hom q f₁ f₂ hf₁ hf₂) φ g₁ g₂
        hg₁ hg₂ = ((MOD.toDescentData (incl U)).obj M).hom q' g₁ g₂ hg₁' hg₂' :=
  ((MOD.toDescentData (incl U)).obj M).pullHom_hom φ q q' hq f₁ f₂ hf₁ hf₂ g₁ g₂ hg₁ hg₂

theorem ofObj_hom_eq (M : Y.Modules) ⦃Z : Scheme.{u}⦄ (q : Z ⟶ Y) ⦃i j : ι⦄ (f₁ : Z ⟶ (U i : Scheme.{u}))
    (f₂ : Z ⟶ (U j : Scheme.{u})) (hf₁ : f₁ ≫ incl U i = q) (hf₂ : f₂ ≫ incl U j = q) :
    ((MOD.toDescentData (incl U)).obj M).hom q f₁ f₂ hf₁ hf₂ =
      ((Scheme.Modules.pullbackComp f₁ (incl U i)).hom.app M ≫ (Scheme.Modules.pullbackCongr hf₁).hom.app M) ≫
        (Scheme.Modules.pullbackCongr hf₂.symm).hom.app M ≫ (Scheme.Modules.pullbackComp f₂ (incl U j)).inv.app M := by
  rw [← HomZar.Mdl_mapComp'_inv_app f₁ (incl U i) M q hf₁, ← HomZar.Mdl_mapComp'_hom_app f₂ (incl U j) M q hf₂]
  rfl

noncomputable abbrev incO (i : ι) (O : Y.Opens) (h : O ≤ U i) : (O : Scheme.{u}) ⟶ (U i : Scheme.{u}) := Y.homOfLE h

theorem incO_comp (i : ι) {O O' : Y.Opens} (hO' : O' ≤ O) (hi : O ≤ U i) :
    Y.homOfLE hO' ≫ incO U i O hi = incO U i O' (hO'.trans hi) :=
  Scheme.homOfLE_homOfLE Y hO' hi

noncomputable def τ (i j : ι) (O : Y.Opens) (hi : O ≤ U i) (hj : O ≤ U j) :
    (Dobj U D i).restrict (incO U i O hi) ≅ (Dobj U D j).restrict (incO U j O hj) :=
  (restrictFunctorIsoPullback (incO U i O hi)).app (Dobj U D i) ≪≫
    D.iso O.ι (incO U i O hi) (incO U j O hj) (Y.homOfLE_ι hi) (Y.homOfLE_ι hj) ≪≫
    ((restrictFunctorIsoPullback (incO U j O hj)).app (Dobj U D j)).symm

noncomputable abbrev ρ (i j : ι) : (Dobj U D i).restrict (p₁ U i j) ≅ (Dobj U D j).restrict (p₂ U i j) :=
  τ U D i j (U i ⊓ U j) inf_le_left inf_le_right

theorem τ_self (i : ι) (O : Y.Opens) (hi : O ≤ U i) :
    (τ U D i i O hi hi).hom = 𝟙 ((Dobj U D i).restrict (incO U i O hi)) := by
  have h := D.hom_self O.ι (incO U i O hi) (Y.homOfLE_ι hi)
  simp only [τ, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv, Pseudofunctor.DescentData.iso_hom]
  erw [h, Category.id_comp]
  exact (restrictFunctorIsoPullback (incO U i O hi)).hom_inv_id_app (Dobj U D i)

theorem ρ_self (i : ι) : (ρ U D i i).hom = 𝟙 ((Dobj U D i).restrict (p₁ U i i)) := τ_self U D i _ _

theorem τ_comp (i j k : ι) (O : Y.Opens) (hi : O ≤ U i) (hj : O ≤ U j) (hk : O ≤ U k) :
    (τ U D i j O hi hj).hom ≫ (τ U D j k O hj hk).hom = (τ U D i k O hi hk).hom := by
  have h := D.hom_comp O.ι (incO U i O hi) (incO U j O hj) (incO U k O hk) (Y.homOfLE_ι hi) (Y.homOfLE_ι hj) (Y.homOfLE_ι hk)
  simp only [τ, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv, Pseudofunctor.DescentData.iso_hom,
    Category.assoc]
  erw [(restrictFunctorIsoPullback (incO U j O hj)).inv_hom_id_app_assoc (Dobj U D j)]
  erw [reassoc_of% h]
  rfl

noncomputable abbrev P (i : ι) : Y.Modules := (pushforward (incl U i)).obj (Dobj U D i)
noncomputable abbrev Q (i j : ι) : Y.Modules := (pushforward (U i ⊓ U j).ι).obj ((Dobj U D j).restrict (p₂ U i j))

noncomputable def β (i j : ι) : P U D j ⟶ Q U D i j :=
  (pushforward (incl U j)).map ((restrictAdjunction (p₂ U i j)).unit.app (Dobj U D j)) ≫
    (pushforwardComp (p₂ U i j) (incl U j)).hom.app _ ≫
    (pushforwardCongr (Y.homOfLE_ι inf_le_right)).hom.app _

noncomputable def α (i j : ι) : P U D i ⟶ Q U D i j :=
  ((pushforward (incl U i)).map ((restrictAdjunction (p₁ U i j)).unit.app (Dobj U D i)) ≫
    (pushforwardComp (p₁ U i j) (incl U i)).hom.app _ ≫
    (pushforwardCongr (Y.homOfLE_ι inf_le_left)).hom.app _) ≫
    (pushforward (U i ⊓ U j).ι).map (ρ U D i j).hom

noncomputable def compatible (W : Y.Opens) : Submodule Γ(Y, W) (∀ i, Γ(P U D i, W)) where
  carrier := {s | ∀ i j, (α U D i j).app W (s i) = (β U D i j).app W (s j)}
  add_mem' := by
    intro s t hs ht i j
    simp only [Pi.add_apply, map_add, hs i j, ht i j]
  zero_mem' := by intro i j; simp only [Pi.zero_apply, map_zero]
  smul_mem' := by
    intro r s hs i j
    simp only [Pi.smul_apply, Hom.app_smul, hs i j]

theorem app_presheaf_map {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) {W W' : X.Opens} (h : W' ⟶ W) (x : Γ(M, W)) :
    φ.app W' (M.presheaf.map h.op x) = N.presheaf.map h.op (φ.app W x) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality h.op) x

theorem compatible_map {W W' : Y.Opens} (h : W' ⟶ W) (s : ∀ i, Γ(P U D i, W)) (hs : s ∈ compatible U D W) :
    (fun i => (P U D i).presheaf.map h.op (s i)) ∈ compatible U D W' := by
  intro i j
  show (α U D i j).app W' ((P U D i).presheaf.map h.op (s i)) = (β U D i j).app W' ((P U D j).presheaf.map h.op (s j))
  rw [app_presheaf_map, app_presheaf_map, hs i j]

noncomputable def gluedAb : (Opens Y)ᵒᵖ ⥤ Ab where
  obj W := AddCommGrpCat.of (compatible U D W.unop)
  map {W W'} h := AddCommGrpCat.ofHom
    { toFun := fun s => ⟨fun i => (P U D i).presheaf.map h (s.1 i), compatible_map U D h.unop s.1 s.2⟩
      map_zero' := by apply Subtype.ext; funext i; simp
      map_add' := by intro s t; apply Subtype.ext; funext i; simp }
  map_id W := by
    apply AddCommGrpCat.ext; intro s; apply Subtype.ext; funext i
    simp
  map_comp {W W' W''} h h' := by
    apply AddCommGrpCat.ext; intro s; apply Subtype.ext; funext i
    simp

theorem gluedAb_map_apply_coe {W W' : (Opens Y)ᵒᵖ} (h : W ⟶ W') (s : compatible U D W.unop) (i : ι) :
    ((gluedAb U D).map h s).1 i = (P U D i).presheaf.map h (s.1 i) := rfl

noncomputable def gluedPresheaf : Y.PresheafOfModules :=
  @PresheafOfModules.ofPresheaf _ _ _ (gluedAb U D)
    (fun W => show Module Γ(Y, W.unop) (compatible U D W.unop) from inferInstance)
    (by
      intro W W' h r s
      apply Subtype.ext; funext i
      exact (P U D i).map_smul h.unop r (s.1 i))

noncomputable abbrev abSheaf (M : Y.Modules) : TopCat.Sheaf Ab Y.toTopCat := ⟨M.presheaf, M.isSheaf⟩

theorem isSheaf_gluedPresheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology Y) (gluedPresheaf U D).presheaf := by
  rw [gluedPresheaf, PresheafOfModules.ofPresheaf_presheaf]
  change TopCat.Presheaf.IsSheaf (gluedAb U D)
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro κ W sf hsf

  have hc : ∀ i, TopCat.Presheaf.IsCompatible (P U D i).presheaf W (fun a => (sf a).1 i) :=
    fun i a b => congrArg (fun s : compatible U D _ => s.1 i) (hsf a b)
  choose t ht huniq using fun i => (abSheaf (P U D i)).existsUnique_gluing W (fun a => (sf a).1 i) (hc i)

  have hmem : t ∈ compatible U D (iSup W) := by
    intro i j
    apply (abSheaf (Q U D i j)).eq_of_locally_eq W
    intro a
    show (Q U D i j).presheaf.map (Opens.leSupr W a).op ((α U D i j).app (iSup W) (t i)) =
      (Q U D i j).presheaf.map (Opens.leSupr W a).op ((β U D i j).app (iSup W) (t j))
    rw [← app_presheaf_map, ← app_presheaf_map]
    erw [ht i a, ht j a]
    exact (sf a).2 i j
  refine ⟨⟨t, hmem⟩, fun a => ?_, fun y hy => ?_⟩
  · apply Subtype.ext; funext i; exact ht i a
  · apply Subtype.ext; funext i
    exact huniq i _ (fun a => congrArg (fun s : compatible U D _ => s.1 i) (hy a))

noncomputable def glued : Y.Modules := ⟨gluedPresheaf U D, isSheaf_gluedPresheaf U D⟩

theorem glued_presheaf_obj (W : Y.Opens) : ((glued U D).presheaf.obj (op W) : Type u) = compatible U D W := rfl

noncomputable def projAb (k : ι) : gluedAb U D ⟶ (P U D k).presheaf where
  app W := AddCommGrpCat.ofHom
    { toFun := fun s => s.1 k, map_zero' := rfl, map_add' := fun _ _ => rfl }
  naturality {W W'} h := by apply AddCommGrpCat.ext; intro s; rfl

noncomputable def proj (k : ι) : glued U D ⟶ P U D k :=
  ⟨PresheafOfModules.homMk (M₁ := (glued U D).val) (M₂ := (P U D k).val) (projAb U D k) (fun W r s => rfl)⟩

theorem proj_app (k : ι) (W : Y.Opens) (s : compatible U D W) :
    (proj U D k).app W (show Γ(glued U D, W) from s) = s.1 k := rfl

theorem presheaf_map_congr {X : Scheme.{u}} (M : X.Modules) {V V' : X.Opens} (f g : V' ⟶ V) (x : Γ(M, V)) :
    M.presheaf.map f.op x = M.presheaf.map g.op x := by rw [Subsingleton.elim f g]

theorem preimage_comp' {X X' X'' : Scheme.{u}} (f : X ⟶ X') (g : X' ⟶ X'') (W : X''.Opens) :
    (f ≫ g) ⁻¹ᵁ W = f ⁻¹ᵁ (g ⁻¹ᵁ W) := rfl

theorem preimage_ι_inf_right (i j : ι) (W : Y.Opens) :
    (U i ⊓ U j).ι ⁻¹ᵁ W = (p₂ U i j) ⁻¹ᵁ ((U j).ι ⁻¹ᵁ W) := by
  rw [← preimage_comp', Scheme.homOfLE_ι]

theorem preimage_ι_inf_left (i j : ι) (W : Y.Opens) :
    (U i ⊓ U j).ι ⁻¹ᵁ W = (p₁ U i j) ⁻¹ᵁ ((U i).ι ⁻¹ᵁ W) := by
  rw [← preimage_comp', Scheme.homOfLE_ι]

theorem β_le (i j : ι) (W : Y.Opens) : (p₂ U i j) ''ᵁ ((U i ⊓ U j).ι ⁻¹ᵁ W) ≤ (U j).ι ⁻¹ᵁ W := by
  rw [preimage_ι_inf_right]; exact Scheme.Hom.image_preimage_le _ _

theorem α_le (i j : ι) (W : Y.Opens) : (p₁ U i j) ''ᵁ ((U i ⊓ U j).ι ⁻¹ᵁ W) ≤ (U i).ι ⁻¹ᵁ W := by
  rw [preimage_ι_inf_left]; exact Scheme.Hom.image_preimage_le _ _

theorem β_eq_of_le {i j : ι} {W : Y.Opens} (hW : W ≤ U i) :
    (p₂ U i j) ''ᵁ ((U i ⊓ U j).ι ⁻¹ᵁ W) = (U j).ι ⁻¹ᵁ W := by
  rw [preimage_ι_inf_right, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.opensRange_homOfLE]
  refine inf_eq_right.mpr ?_
  show (U j).ι ⁻¹ᵁ W ≤ (U j).ι ⁻¹ᵁ (U i ⊓ U j)
  have h1 : (U j).ι ⁻¹ᵁ (U i ⊓ U j) = (U j).ι ⁻¹ᵁ (U i) ⊓ (U j).ι ⁻¹ᵁ (U j) := rfl
  rw [h1, Scheme.Opens.ι_preimage_self, inf_top_eq]
  exact fun y hy => hW hy

theorem β_app_hom (i j : ι) (W : Y.Opens) :
    (β U D i j).app W = (Dobj U D j).presheaf.map (homOfLE (β_le U i j W)).op := by
  have h1 := restrictAdjunction_unit_app_app (p₂ U i j) (Dobj U D j) ((U j).ι ⁻¹ᵁ W)
  have h2 := pushforwardComp_hom_app_app (M := (Dobj U D j).restrict (p₂ U i j)) (p₂ U i j) (incl U j) W
  have h3 := pushforwardCongr_hom_app_app (M := (Dobj U D j).restrict (p₂ U i j))
    (Y.homOfLE_ι (inf_le_right : U i ⊓ U j ≤ U j)) W
  rw [β, Hom.comp_app, Hom.comp_app, pushforward_map_app]
  erw [h1, h2, h3, Category.id_comp]
  rw [restrict_map]
  refine ((Dobj U D j).presheaf.map_comp _ _).symm.trans ?_
  congr 1

theorem β_app (i j : ι) (W : Y.Opens) (x : Γ(P U D j, W)) :
    (β U D i j).app W x = ((Dobj U D j).presheaf.map (homOfLE (β_le U i j W)).op x :) :=
  ConcreteCategory.congr_hom (β_app_hom U D i j W) x

theorem α_app_hom (i j : ι) (W : Y.Opens) :
    (α U D i j).app W = (Dobj U D i).presheaf.map (homOfLE (α_le U i j W)).op ≫
      (ρ U D i j).hom.app ((U i ⊓ U j).ι ⁻¹ᵁ W) := by
  have h1 := restrictAdjunction_unit_app_app (p₁ U i j) (Dobj U D i) ((U i).ι ⁻¹ᵁ W)
  have h2 := pushforwardComp_hom_app_app (M := (Dobj U D i).restrict (p₁ U i j)) (p₁ U i j) (incl U i) W
  have h3 := pushforwardCongr_hom_app_app (M := (Dobj U D i).restrict (p₁ U i j))
    (Y.homOfLE_ι (inf_le_left : U i ⊓ U j ≤ U i)) W
  rw [α, Hom.comp_app, Hom.comp_app, Hom.comp_app, pushforward_map_app, pushforward_map_app]
  erw [h1, h2, h3, Category.id_comp]
  rw [restrict_map]
  refine congrArg (fun t => t ≫ Hom.app (ρ U D i j).hom ((U i ⊓ U j).ι ⁻¹ᵁ W)) ?_
  refine ((Dobj U D i).presheaf.map_comp _ _).symm.trans ?_
  congr 1

theorem α_app (i j : ι) (W : Y.Opens) (x : Γ(P U D i, W)) :
    (α U D i j).app W x =
      (ρ U D i j).hom.app ((U i ⊓ U j).ι ⁻¹ᵁ W) ((Dobj U D i).presheaf.map (homOfLE (α_le U i j W)).op x) :=
  ConcreteCategory.congr_hom (α_app_hom U D i j W) x

theorem restrictFunctor_map_app {X : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {M N : Y.Modules} (t : M ⟶ N)
    (V : X.Opens) : ((restrictFunctor f).map t).app V = t.app (f ''ᵁ V) := rfl

theorem presheaf_map_injective_of_eq {X : Scheme.{u}} (M : X.Modules) {V V' : X.Opens} (e : V' = V) (h : V' ≤ V) :
    Function.Injective (M.presheaf.map (homOfLE h).op) := by
  subst e
  intro x y hxy
  simpa using hxy

theorem compatible_ext_of_le {k : ι} {W : Y.Opens} (hW : W ≤ U k) {s s' : compatible U D W}
    (h : s.1 k = s'.1 k) : s = s' := by
  apply Subtype.ext; funext i
  have hs := s.2 k i
  have hs' := s'.2 k i
  rw [h, hs'] at hs
  rw [β_app, β_app] at hs
  exact (presheaf_map_injective_of_eq (Dobj U D i) (β_eq_of_le U hW) (β_le U k i W) hs).symm

theorem map_map {X : Scheme.{u}} (M : X.Modules) {V₁ V₂ V₃ : X.Opens} (f : V₂ ⟶ V₁) (g : V₃ ⟶ V₂) (x : Γ(M, V₁)) :
    M.presheaf.map g.op (M.presheaf.map f.op x) = M.presheaf.map (g ≫ f).op x :=
  (ConcreteCategory.congr_hom (M.presheaf.map_comp f.op g.op) x).symm

theorem map_self {X : Scheme.{u}} (M : X.Modules) {V : X.Opens} (f : V ⟶ V) (x : Γ(M, V)) :
    M.presheaf.map f.op x = x := by
  rw [Subsingleton.elim f (𝟙 V)]
  simp

theorem map_map_self {X : Scheme.{u}} (M : X.Modules) {V₁ V₂ : X.Opens} (f : V₂ ⟶ V₁) (g : V₁ ⟶ V₂) (x : Γ(M, V₁)) :
    M.presheaf.map g.op (M.presheaf.map f.op x) = x := by
  rw [map_map, map_self]

theorem preimage_ι_eq_incO (i : ι) (O : Y.Opens) (hi : O ≤ U i) (V : Y.Opens) :
    O.ι ⁻¹ᵁ V = (incO U i O hi) ⁻¹ᵁ ((U i).ι ⁻¹ᵁ V) := by
  rw [← preimage_comp', Scheme.homOfLE_ι]

theorem T_le_in (i : ι) (O : Y.Opens) (hi : O ≤ U i) (V : Y.Opens) :
    (incO U i O hi) ''ᵁ (O.ι ⁻¹ᵁ V) ≤ (U i).ι ⁻¹ᵁ V := by
  rw [preimage_ι_eq_incO U i O hi]; exact Scheme.Hom.image_preimage_le _ _

theorem T_eq (i : ι) (O : Y.Opens) (hi : O ≤ U i) (V : Y.Opens) (hV : V ≤ O) :
    (incO U i O hi) ''ᵁ (O.ι ⁻¹ᵁ V) = (U i).ι ⁻¹ᵁ V := by
  rw [preimage_ι_eq_incO U i O hi, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.opensRange_homOfLE]
  refine inf_eq_right.mpr ?_
  exact fun y hy => hV hy

theorem T_le_out (i : ι) (O : Y.Opens) (hi : O ≤ U i) (V : Y.Opens) (hV : V ≤ O) :
    (U i).ι ⁻¹ᵁ V ≤ (incO U i O hi) ''ᵁ (O.ι ⁻¹ᵁ V) :=
  (T_eq U i O hi V hV).symm.le

noncomputable def T (i j : ι) (O : Y.Opens) (hi : O ≤ U i) (hj : O ≤ U j) (V : Y.Opens) (hV : V ≤ O)
    (x : Γ(Dobj U D i, (U i).ι ⁻¹ᵁ V)) : Γ(Dobj U D j, (U j).ι ⁻¹ᵁ V) :=
  (Dobj U D j).presheaf.map (homOfLE (T_le_out U j O hj V hV)).op
    ((τ U D i j O hi hj).hom.app (O.ι ⁻¹ᵁ V)
      ((Dobj U D i).presheaf.map (homOfLE (T_le_in U i O hi V)).op x))

theorem T_self (i : ι) (O : Y.Opens) (hi : O ≤ U i) (V : Y.Opens) (hV : V ≤ O)
    (x : Γ(Dobj U D i, (U i).ι ⁻¹ᵁ V)) : T U D i i O hi hi V hV x = x := by
  simp only [T, τ_self, Hom.id_app]
  exact map_map_self _ _ _ x

theorem T_comp (i j k : ι) (O : Y.Opens) (hi : O ≤ U i) (hj : O ≤ U j) (hk : O ≤ U k) (V : Y.Opens) (hV : V ≤ O)
    (x : Γ(Dobj U D i, (U i).ι ⁻¹ᵁ V)) :
    T U D j k O hj hk V hV (T U D i j O hi hj V hV x) = T U D i k O hi hk V hV x := by
  simp only [T]
  rw [map_map_self]
  rw [← τ_comp U D i j k O hi hj hk, Hom.comp_app]
  rfl

theorem T_res (i j : ι) (O : Y.Opens) (hi : O ≤ U i) (hj : O ≤ U j) {V V' : Y.Opens} (hV : V ≤ O) (hV' : V' ≤ V)
    (x : Γ(Dobj U D i, (U i).ι ⁻¹ᵁ V)) :
    T U D i j O hi hj V' (hV'.trans hV) ((Dobj U D i).presheaf.map (homOfLE ((U i).ι.preimage_mono hV')).op x) =
      (Dobj U D j).presheaf.map (homOfLE ((U j).ι.preimage_mono hV')).op (T U D i j O hi hj V hV x) := by
  simp only [T]
  rw [map_map, map_map]
  have nat := app_presheaf_map (τ U D i j O hi hj).hom (homOfLE (O.ι.preimage_mono hV'))
    ((Dobj U D i).presheaf.map (homOfLE (T_le_in U i O hi V)).op x)
  rw [restrict_map, restrict_map] at nat
  have step1 : (Dobj U D i).presheaf.map (homOfLE (T_le_in U i O hi V') ≫ homOfLE ((U i).ι.preimage_mono hV')).op x =
      (Dobj U D i).presheaf.map ((Hom.opensFunctor (incO U i O hi)).map (homOfLE (O.ι.preimage_mono hV'))).op
        ((Dobj U D i).presheaf.map (homOfLE (T_le_in U i O hi V)).op x) := by
    rw [map_map]; exact presheaf_map_congr _ _ _ _
  rw [step1]
  erw [nat]
  exact (map_map _ _ _ _).trans (presheaf_map_congr _ _ _ _)

noncomputable def Φ {X₀ X₁ X₂ : Scheme.{u}} (e : X₀ ⟶ X₁) (a : X₁ ⟶ X₂) (a' : X₀ ⟶ X₂) [IsOpenImmersion e]
    [IsOpenImmersion a] [IsOpenImmersion a'] (w : e ≫ a = a') (M : X₂.Modules) :
    (restrictFunctor a').obj M ⟶ (restrictFunctor e).obj ((restrictFunctor a).obj M) :=
  (restrictFunctorIsoPullback a').hom.app M ≫
    (MOD.mapComp' a.op.toLoc e.op.toLoc a'.op.toLoc (by rw [← w]; rfl)).hom.toNatTrans.app M ≫
    (restrictFunctorIsoPullback e).inv.app ((pullback a).obj M) ≫
    (restrictFunctor e).map ((restrictFunctorIsoPullback a).inv.app M)

theorem Φ_eq_congr_comp {X₀ X₁ X₂ : Scheme.{u}} (e : X₀ ⟶ X₁) (a : X₁ ⟶ X₂) (a' : X₀ ⟶ X₂) [IsOpenImmersion e]
    [IsOpenImmersion a] [IsOpenImmersion a'] (w : e ≫ a = a') (M : X₂.Modules) :
    Φ e a a' w M = (restrictFunctorCongr w.symm).hom.app M ≫ (restrictFunctorComp e a).hom.app M := by
  subst w
  have hc : (restrictFunctorCongr (rfl : e ≫ a = e ≫ a)).hom.app M = 𝟙 _ := by
    apply Scheme.Modules.hom_ext; intro V
    erw [restrictFunctorCongr_hom_app_app]
    simp
    rfl
  rw [hc, Category.id_comp, Φ]
  erw [HomZar.restrictFunctorIsoPullback_comp_hom_app e a M, mapComp'_hom_app_eq e a M (e ≫ a) rfl]
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    Category.assoc]
  have c1 : (restrictFunctorIsoPullback e).hom.app ((pullback a).obj M) ≫
      (restrictFunctorIsoPullback e).inv.app ((pullback a).obj M) = 𝟙 _ := Iso.hom_inv_id_app _ _
  have c2 : (restrictFunctor e).map ((restrictFunctorIsoPullback a).hom.app M) ≫
      (restrictFunctor e).map ((restrictFunctorIsoPullback a).inv.app M) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  have c0 : (pullbackComp e a).hom.app M ≫ (pullbackComp e a).inv.app M = 𝟙 _ := Iso.hom_inv_id_app _ _
  erw [reassoc_of% c0, reassoc_of% c1, c2]
  erw [Category.comp_id]

theorem image_comp_of_eq {X₀ X₁ X₂ : Scheme.{u}} (e : X₀ ⟶ X₁) (a : X₁ ⟶ X₂) (a' : X₀ ⟶ X₂) [IsOpenImmersion e]
    [IsOpenImmersion a] [IsOpenImmersion a'] (w : e ≫ a = a') (V : X₀.Opens) : a ''ᵁ (e ''ᵁ V) = a' ''ᵁ V := by
  subst w
  apply TopologicalSpace.Opens.ext
  first
    | exact (Set.image_comp _ _ _).symm
    | exact Set.image_image _ _ _
    | (ext x; constructor
       · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩; exact ⟨z, hz, rfl⟩
       · rintro ⟨z, hz, rfl⟩; exact ⟨e.base z, ⟨z, hz, rfl⟩, rfl⟩)

theorem Φ_app {X₀ X₁ X₂ : Scheme.{u}} (e : X₀ ⟶ X₁) (a : X₁ ⟶ X₂) (a' : X₀ ⟶ X₂) [IsOpenImmersion e]
    [IsOpenImmersion a] [IsOpenImmersion a'] (w : e ≫ a = a') (M : X₂.Modules) (V : X₀.Opens)
    (x : Γ(M, a' ''ᵁ V)) :
    (Φ e a a' w M).app V x = (M.presheaf.map (eqToHom (image_comp_of_eq e a a' w V)).op x :
      Γ(M, a ''ᵁ (e ''ᵁ V))) := by
  have h1 := restrictFunctorCongr_hom_app_app (U := V) w.symm M
  have h2 := restrictFunctorComp_hom_app_app (U := V) e a M
  rw [Φ_eq_congr_comp]
  refine (show _ = (Hom.app ((restrictFunctorComp e a).hom.app M) V)
    ((Hom.app ((restrictFunctorCongr w.symm).hom.app M) V) x) from rfl).trans ?_
  refine (congrArg _ (ConcreteCategory.congr_hom h1 x)).trans ?_
  refine (ConcreteCategory.congr_hom h2 _).trans ?_
  exact (map_map _ _ _ _).trans (presheaf_map_congr _ _ _ _)

noncomputable def castComp {X₀ X₁ X₂ : Scheme.{u}} (e : X₀ ⟶ X₁) (a : X₁ ⟶ X₂) (a' : X₀ ⟶ X₂) [IsOpenImmersion e]
    [IsOpenImmersion a] [IsOpenImmersion a'] (w : e ≫ a = a') (M : X₂.Modules) :
    (restrictFunctor a').obj M ⟶ (restrictFunctor e).obj ((restrictFunctor a).obj M) :=
  (restrictFunctorCongr w.symm).hom.app M ≫ (restrictFunctorComp e a).hom.app M

noncomputable def castComp' {X₀ X₁ X₂ : Scheme.{u}} (e : X₀ ⟶ X₁) (a : X₁ ⟶ X₂) (a' : X₀ ⟶ X₂) [IsOpenImmersion e]
    [IsOpenImmersion a] [IsOpenImmersion a'] (w : e ≫ a = a') (M : X₂.Modules) :
    (restrictFunctor e).obj ((restrictFunctor a).obj M) ⟶ (restrictFunctor a').obj M :=
  (restrictFunctorComp e a).inv.app M ≫ (restrictFunctorCongr w).hom.app M

theorem castComp_app {X₀ X₁ X₂ : Scheme.{u}} (e : X₀ ⟶ X₁) (a : X₁ ⟶ X₂) (a' : X₀ ⟶ X₂) [IsOpenImmersion e]
    [IsOpenImmersion a] [IsOpenImmersion a'] (w : e ≫ a = a') (M : X₂.Modules) (V : X₀.Opens)
    (x : Γ(M, a' ''ᵁ V)) :
    (castComp e a a' w M).app V x = (M.presheaf.map (eqToHom (image_comp_of_eq e a a' w V)).op x :
      Γ(M, a ''ᵁ (e ''ᵁ V))) := by
  have h := Φ_app e a a' w M V x
  rw [Φ_eq_congr_comp] at h
  exact h

theorem castComp'_app {X₀ X₁ X₂ : Scheme.{u}} (e : X₀ ⟶ X₁) (a : X₁ ⟶ X₂) (a' : X₀ ⟶ X₂) [IsOpenImmersion e]
    [IsOpenImmersion a] [IsOpenImmersion a'] (w : e ≫ a = a') (M : X₂.Modules) (V : X₀.Opens)
    (x : Γ(M, a ''ᵁ (e ''ᵁ V))) :
    (castComp' e a a' w M).app V x = (M.presheaf.map (eqToHom (image_comp_of_eq e a a' w V).symm).op x :
      Γ(M, a' ''ᵁ V)) := by
  have h1 := restrictFunctorComp_inv_app_app (U := V) e a M
  have h2 := restrictFunctorCongr_hom_app_app (U := V) w M
  refine (show _ = (Hom.app ((restrictFunctorCongr w).hom.app M) V)
    ((Hom.app ((restrictFunctorComp e a).inv.app M) V) x) from rfl).trans ?_
  refine (congrArg _ (ConcreteCategory.congr_hom h1 x)).trans ?_
  refine (ConcreteCategory.congr_hom h2 _).trans ?_
  exact (map_map _ _ _ _).trans (presheaf_map_congr _ _ _ _)

theorem τ_hom_eq (i j : ι) (O : Y.Opens) (hi : O ≤ U i) (hj : O ≤ U j) : (τ U D i j O hi hj).hom =
    (restrictFunctorIsoPullback (incO U i O hi)).hom.app (Dobj U D i) ≫
      D.hom O.ι (incO U i O hi) (incO U j O hj) (Y.homOfLE_ι hi) (Y.homOfLE_ι hj) ≫
      (restrictFunctorIsoPullback (incO U j O hj)).inv.app (Dobj U D j) := by
  simp only [τ, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv, Pseudofunctor.DescentData.iso_hom,
    Category.assoc]

theorem τ_locality (i j : ι) {O O' : Y.Opens} (hO' : O' ≤ O) (hi : O ≤ U i) (hj : O ≤ U j) :
    (restrictFunctorIsoPullback (incO U i O' (hO'.trans hi))).hom.app (D.obj i) ≫
      D.hom O'.ι (incO U i O' (hO'.trans hi)) (incO U j O' (hO'.trans hj))
        (Y.homOfLE_ι (hO'.trans hi)) (Y.homOfLE_ι (hO'.trans hj)) ≫
      (restrictFunctorIsoPullback (incO U j O' (hO'.trans hj))).inv.app (D.obj j) =
    (restrictFunctorCongr (incO_comp U i hO' hi).symm).hom.app (D.obj i) ≫
      (restrictFunctorComp (Y.homOfLE hO') (incO U i O hi)).hom.app (D.obj i) ≫
      (restrictFunctor (Y.homOfLE hO')).map
        ((restrictFunctorIsoPullback (incO U i O hi)).hom.app (D.obj i) ≫
          D.hom O.ι (incO U i O hi) (incO U j O hj) (Y.homOfLE_ι hi) (Y.homOfLE_ι hj) ≫
          (restrictFunctorIsoPullback (incO U j O hj)).inv.app (D.obj j)) ≫
      (restrictFunctorComp (Y.homOfLE hO') (incO U j O hj)).inv.app (D.obj j) ≫
      (restrictFunctorCongr (incO_comp U j hO' hj)).hom.app (D.obj j) := by
  have hh := crux_MOD (Y.homOfLE hO') (incO U i O hi) (incO U j O hj)
    (incO U i O' (hO'.trans hi)) (incO U j O' (hO'.trans hj)) (incO_comp U i hO' hi) (incO_comp U j hO' hj)
    (D.obj i) (D.obj j) (D.hom O.ι (incO U i O hi) (incO U j O hj) (Y.homOfLE_ι hi) (Y.homOfLE_ι hj))
  rw [D_pullHom U D (Y.homOfLE hO') O.ι O'.ι (Y.homOfLE_ι hO') (incO U i O hi) (incO U j O hj)
    (Y.homOfLE_ι hi) (Y.homOfLE_ι hj) (incO U i O' (hO'.trans hi)) (incO U j O' (hO'.trans hj))
    (incO_comp U i hO' hi) (incO_comp U j hO' hj) (Y.homOfLE_ι _) (Y.homOfLE_ι _)] at hh
  exact hh

theorem T_indep (i j : ι) (O : Y.Opens) (hi : O ≤ U i) (hj : O ≤ U j) (V : Y.Opens) (hV : V ≤ O)
    (x : Γ(Dobj U D i, (U i).ι ⁻¹ᵁ V)) :
    T U D i j O hi hj V hV x = T U D i j V (hV.trans hi) (hV.trans hj) V le_rfl x := by
  symm
  simp only [T]
  have loc := τ_locality U D i j hV hi hj
  have hsub : (Y.homOfLE hV) ''ᵁ (V.ι ⁻¹ᵁ V) ≤ O.ι ⁻¹ᵁ V :=
    ((Y.homOfLE hV).image_le_opensRange _).trans (by rw [Scheme.opensRange_homOfLE])

  have ev : ∀ y, (τ U D i j V (hV.trans hi) (hV.trans hj)).hom.app (V.ι ⁻¹ᵁ V) y =
      ((restrictFunctorCongr (Scheme.homOfLE_homOfLE Y hV hj)).hom.app (Dobj U D j)).app (V.ι ⁻¹ᵁ V)
      (((restrictFunctorComp (Y.homOfLE hV) (incO U j O hj)).inv.app (Dobj U D j)).app (V.ι ⁻¹ᵁ V)
      (((restrictFunctorIsoPullback (incO U i O hi)).hom.app (Dobj U D i) ≫
          D.hom O.ι (incO U i O hi) (incO U j O hj) (Y.homOfLE_ι hi) (Y.homOfLE_ι hj) ≫
          (restrictFunctorIsoPullback (incO U j O hj)).inv.app (Dobj U D j)).app ((Y.homOfLE hV) ''ᵁ (V.ι ⁻¹ᵁ V))
      (((restrictFunctorComp (Y.homOfLE hV) (incO U i O hi)).hom.app (Dobj U D i)).app (V.ι ⁻¹ᵁ V)
      (((restrictFunctorCongr (Scheme.homOfLE_homOfLE Y hV hi).symm).hom.app (Dobj U D i)).app (V.ι ⁻¹ᵁ V) y)))) := by
    intro y; rw [τ_hom_eq, loc]; rfl
  have c1 := restrictFunctorCongr_hom_app_app (U := V.ι ⁻¹ᵁ V) (Scheme.homOfLE_homOfLE Y hV hi).symm (Dobj U D i)
  have c2 := restrictFunctorComp_hom_app_app (U := V.ι ⁻¹ᵁ V) (Y.homOfLE hV) (incO U i O hi) (Dobj U D i)
  have c3 := restrictFunctorComp_inv_app_app (U := V.ι ⁻¹ᵁ V) (Y.homOfLE hV) (incO U j O hj) (Dobj U D j)
  have c4 := restrictFunctorCongr_hom_app_app (U := V.ι ⁻¹ᵁ V) (Scheme.homOfLE_homOfLE Y hV hj) (Dobj U D j)
  rw [ev]
  erw [c1, c2, c3, c4, ← τ_hom_eq]
  refine (map_map _ _ _ _).trans ((map_map _ _ _ _).trans ?_)
  erw [map_map (Dobj U D i), map_map (Dobj U D i)]
  erw [presheaf_map_congr (Dobj U D i) _
    ((Hom.opensFunctor (incO U i O hi)).map (homOfLE hsub) ≫ homOfLE (T_le_in U i O hi V)) x]
  erw [← map_map (Dobj U D i) (homOfLE (T_le_in U i O hi V)) ((Hom.opensFunctor (incO U i O hi)).map (homOfLE hsub)) x]
  have nat := app_presheaf_map (τ U D i j O hi hj).hom (homOfLE hsub)
    ((Dobj U D i).presheaf.map (homOfLE (T_le_in U i O hi V)).op x)
  rw [restrict_map, restrict_map] at nat
  erw [nat]
  exact (map_map _ _ _ _).trans (presheaf_map_congr _ _ _ _)

theorem presheaf_map_injective_of_eq' {X : Scheme.{u}} (M : X.Modules) {V V' : X.Opens} (e : V' = V) (f : V' ⟶ V) :
    Function.Injective (M.presheaf.map f.op) := by
  subst e
  intro x y hxy
  rwa [map_self, map_self] at hxy

theorem preimage_ι_inf_self (O W : Y.Opens) : O.ι ⁻¹ᵁ (W ⊓ O) = O.ι ⁻¹ᵁ W := by
  show O.ι ⁻¹ᵁ W ⊓ O.ι ⁻¹ᵁ O = _
  rw [Scheme.Opens.ι_preimage_self, inf_top_eq]

theorem compat_of_T (W : Y.Opens) (s : ∀ i, Γ(P U D i, W)) (i j : ι)
    (h : T U D i j (U i ⊓ U j) inf_le_left inf_le_right (W ⊓ (U i ⊓ U j)) inf_le_right
        ((Dobj U D i).presheaf.map (homOfLE ((U i).ι.preimage_mono inf_le_left)).op (s i)) =
      (Dobj U D j).presheaf.map (homOfLE ((U j).ι.preimage_mono inf_le_left)).op (s j)) :
    (α U D i j).app W (s i) = (β U D i j).app W (s j) := by
  rw [α_app, β_app]

  have hm : (U i ⊓ U j).ι ⁻¹ᵁ (W ⊓ (U i ⊓ U j)) ≤ (U i ⊓ U j).ι ⁻¹ᵁ W := (U i ⊓ U j).ι.preimage_mono inf_le_left
  have he : (p₂ U i j) ''ᵁ ((U i ⊓ U j).ι ⁻¹ᵁ (W ⊓ (U i ⊓ U j))) = (p₂ U i j) ''ᵁ ((U i ⊓ U j).ι ⁻¹ᵁ W) := by
    rw [preimage_ι_inf_self]
  apply presheaf_map_injective_of_eq' (Dobj U D j) he ((Hom.opensFunctor (p₂ U i j)).map (homOfLE hm))
  have nat := app_presheaf_map (ρ U D i j).hom (homOfLE hm)
    ((Dobj U D i).presheaf.map (homOfLE (α_le U i j W)).op (s i))
  rw [restrict_map, restrict_map] at nat
  erw [← nat]
  rw [map_map]
  have eL : (Dobj U D i).presheaf.map ((Hom.opensFunctor (p₁ U i j)).map (homOfLE hm)).op
      ((Dobj U D i).presheaf.map (homOfLE (α_le U i j W)).op (s i)) =
      (Dobj U D i).presheaf.map (homOfLE (T_le_in U i (U i ⊓ U j) inf_le_left (W ⊓ (U i ⊓ U j)))).op
        ((Dobj U D i).presheaf.map (homOfLE ((U i).ι.preimage_mono inf_le_left)).op (s i)) :=
    (map_map _ _ _ _).trans ((presheaf_map_congr _ _ _ _).trans (map_map _ _ _ _).symm)
  erw [eL]

  simp only [T] at h
  have h' := congrArg ((Dobj U D j).presheaf.map
    (homOfLE (T_le_in U j (U i ⊓ U j) inf_le_right (W ⊓ (U i ⊓ U j)))).op) h
  have h'' := (map_map_self _ _ _ _).symm.trans (h'.trans (map_map _ _ _ _))
  erw [h'']
  exact presheaf_map_congr _ _ _ _

noncomputable def restrictGluedHom (k : ι) : (glued U D).restrict (incl U k) ⟶ Dobj U D k :=
  (restrictFunctor (incl U k)).map (proj U D k) ≫ (restrictAdjunction (incl U k)).counit.app (Dobj U D k)

theorem restrictGluedHom_app (k : ι) (V : ((U k : Y.Opens) : Scheme.{u}).Opens)
    (s : compatible U D ((incl U k) ''ᵁ V)) :
    (restrictGluedHom U D k).app V (show Γ((glued U D).restrict (incl U k), V) from s) =
      (Dobj U D k).presheaf.map (eqToHom ((incl U k).preimage_image_eq V).symm).op (s.1 k) := by
  have h := restrictAdjunction_counit_app_app (incl U k) (Dobj U D k) V
  rw [restrictGluedHom, Hom.comp_app]
  erw [h]
  rfl

theorem restrictGluedHom_app_injective (k : ι) (V : ((U k : Y.Opens) : Scheme.{u}).Opens) :
    Function.Injective ((restrictGluedHom U D k).app V) := by
  intro s s' h
  change compatible U D ((incl U k) ''ᵁ V) at s s'
  rw [restrictGluedHom_app, restrictGluedHom_app] at h
  have hinj : Function.Injective ((Dobj U D k).presheaf.map (eqToHom ((incl U k).preimage_image_eq V).symm).op) := by
    intro x y hxy
    simpa using congrArg ((Dobj U D k).presheaf.map (eqToHom ((incl U k).preimage_image_eq V)).op) hxy
  exact compatible_ext_of_le U D ((incl U k).image_le_opensRange V |>.trans (by simp)) (hinj h)

theorem preimage_incl_inf_self (i : ι) (W : Y.Opens) : (U i).ι ⁻¹ᵁ (W ⊓ U i) = (U i).ι ⁻¹ᵁ W := by
  show (U i).ι ⁻¹ᵁ W ⊓ (U i).ι ⁻¹ᵁ (U i) = _
  rw [Scheme.Opens.ι_preimage_self, inf_top_eq]

theorem restrictGluedHom_app_surjective (k : ι) (V : ((U k : Y.Opens) : Scheme.{u}).Opens) :
    Function.Surjective ((restrictGluedHom U D k).app V) := by
  intro y
  have hW : (incl U k) ''ᵁ V ≤ U k := ((incl U k).image_le_opensRange V).trans (by simp)

  let t : Γ(P U D k, (incl U k) ''ᵁ V) :=
    (Dobj U D k).presheaf.map (eqToHom ((incl U k).preimage_image_eq V)).op y

  let s : ∀ i, Γ(P U D i, (incl U k) ''ᵁ V) := fun i =>
    (Dobj U D i).presheaf.map (homOfLE (preimage_incl_inf_self U i _).symm.le).op
      (T U D k i (U k ⊓ U i) inf_le_left inf_le_right ((incl U k) ''ᵁ V ⊓ U i) (inf_le_inf_right (U i) hW)
        ((Dobj U D k).presheaf.map (homOfLE ((U k).ι.preimage_mono inf_le_left)).op t))

  have step : ∀ (i : ι) (V' : Y.Opens) (hV'W : V' ≤ (incl U k) ''ᵁ V) (hV'i : V' ≤ U i),
      (Dobj U D i).presheaf.map (homOfLE ((U i).ι.preimage_mono hV'W)).op (s i) =
        T U D k i V' (hV'W.trans hW) hV'i V' le_rfl
          ((Dobj U D k).presheaf.map (homOfLE ((U k).ι.preimage_mono hV'W)).op t) := by
    intro i V' hV'W hV'i
    have hle : V' ≤ (incl U k) ''ᵁ V ⊓ U i := le_inf hV'W hV'i
    refine (map_map _ _ _ _).trans ?_
    refine (presheaf_map_congr _ _ (homOfLE ((U i).ι.preimage_mono hle)) _).trans ?_
    refine (T_res U D k i (U k ⊓ U i) inf_le_left inf_le_right (inf_le_inf_right (U i) hW) hle _).symm.trans ?_
    refine (congrArg (T U D k i (U k ⊓ U i) inf_le_left inf_le_right _ (hle.trans (inf_le_inf_right (U i) hW)))
      ((map_map _ _ _ _).trans (presheaf_map_congr _ _ (homOfLE ((U k).ι.preimage_mono hV'W)) _))).trans ?_
    exact T_indep U D k i _ _ _ _ _ _
  have mem : s ∈ compatible U D ((incl U k) ''ᵁ V) := by
    intro i j
    apply compat_of_T
    rw [step i _ inf_le_left (inf_le_right.trans inf_le_left), step j _ inf_le_left (inf_le_right.trans inf_le_right),
      T_indep, T_comp]
  refine ⟨⟨s, mem⟩, ?_⟩
  rw [restrictGluedHom_app]
  have hk : s k = t :=
    (congrArg ((Dobj U D k).presheaf.map (homOfLE (preimage_incl_inf_self U k _).symm.le).op)
      (T_self U D k (U k ⊓ U k) inf_le_left ((incl U k) ''ᵁ V ⊓ U k) (inf_le_inf_right (U k) hW) _)).trans
      (map_map_self _ _ _ _)
  exact (congrArg ((Dobj U D k).presheaf.map (eqToHom ((incl U k).preimage_image_eq V).symm).op) hk).trans
    (map_map_self _ _ _ _)

theorem isIso_restrictGluedHom (k : ι) : IsIso (restrictGluedHom U D k) := by
  refine Hom.isIso_iff_isIso_app.mpr fun V => ?_
  haveI : IsIso ((CategoryTheory.forget Ab).map ((restrictGluedHom U D k).app V)) :=
    (isIso_iff_bijective _).mpr ⟨restrictGluedHom_app_injective U D k V, restrictGluedHom_app_surjective U D k V⟩
  exact isIso_of_reflects_iso _ (CategoryTheory.forget Ab)

noncomputable def gluedIso (k : ι) : (pullback (incl U k)).obj (glued U D) ≅ Dobj U D k :=
  ((restrictFunctorIsoPullback (incl U k)).app (glued U D)).symm ≪≫
    @asIso _ _ _ _ (restrictGluedHom U D k) (isIso_restrictGluedHom U D k)

theorem image_mono' {X X' : Scheme.{u}} (f : X ⟶ X') [IsOpenImmersion f] {A B : X.Opens} (h : A ≤ B) :
    f ''ᵁ A ≤ f ''ᵁ B := fun _ ⟨z, hz, e⟩ => ⟨z, h hz, e⟩

theorem cs_le (i j : ι) (V : ((U i ⊓ U j : Y.Opens) : Scheme.{u}).Opens) :
    (p₁ U i j) ''ᵁ V ≤ (U i).ι ⁻¹ᵁ ((U i ⊓ U j).ι ''ᵁ V) :=
  (image_mono' (p₁ U i j) (((U i ⊓ U j).ι.preimage_image_eq V).symm.le)).trans (α_le U i j _)

theorem cs_le' (i j : ι) (V : ((U i ⊓ U j : Y.Opens) : Scheme.{u}).Opens) :
    (p₂ U i j) ''ᵁ V ≤ (U j).ι ⁻¹ᵁ ((U i ⊓ U j).ι ''ᵁ V) :=
  (image_mono' (p₂ U i j) (((U i ⊓ U j).ι.preimage_image_eq V).symm.le)).trans (β_le U i j _)

set_option maxHeartbeats 3200000 in

theorem comm_sections (i j : ι) :
    castComp (p₁ U i j) (incl U i) (U i ⊓ U j).ι (Y.homOfLE_ι inf_le_left) (glued U D) ≫
        (restrictFunctor (p₁ U i j)).map (restrictGluedHom U D i) ≫ (ρ U D i j).hom =
      castComp (p₂ U i j) (incl U j) (U i ⊓ U j).ι (Y.homOfLE_ι inf_le_right) (glued U D) ≫
        (restrictFunctor (p₂ U i j)).map (restrictGluedHom U D j) := by
  apply Scheme.Modules.hom_ext; intro V
  apply AddCommGrpCat.ext; intro s
  change compatible U D ((U i ⊓ U j).ι ''ᵁ V) at s
  simp only [Hom.comp_app, ConcreteCategory.comp_apply]
  have E₁ : (incl U i) ''ᵁ ((p₁ U i j) ''ᵁ V) = (U i ⊓ U j).ι ''ᵁ V :=
    image_comp_of_eq (p₁ U i j) (incl U i) ((U i ⊓ U j).ι) (Y.homOfLE_ι inf_le_left) V
  have E₂ : (incl U j) ''ᵁ ((p₂ U i j) ''ᵁ V) = (U i ⊓ U j).ι ''ᵁ V :=
    image_comp_of_eq (p₂ U i j) (incl U j) ((U i ⊓ U j).ι) (Y.homOfLE_ι inf_le_right) V
  have m1 : Hom.app ((restrictFunctor (p₁ U i j)).map (restrictGluedHom U D i)) V =
      (restrictGluedHom U D i).app ((p₁ U i j) ''ᵁ V) := rfl
  have m2 : Hom.app ((restrictFunctor (p₂ U i j)).map (restrictGluedHom U D j)) V =
      (restrictGluedHom U D j).app ((p₂ U i j) ''ᵁ V) := rfl
  have k1 := castComp_app (p₁ U i j) (incl U i) (U i ⊓ U j).ι (Y.homOfLE_ι inf_le_left) (glued U D) V s
  have k2 := castComp_app (p₂ U i j) (incl U j) (U i ⊓ U j).ι (Y.homOfLE_ι inf_le_right) (glued U D) V s
  erw [m1, m2, k1, k2]
  have r1 := restrictGluedHom_app U D i ((p₁ U i j) ''ᵁ V)
    (show compatible U D ((incl U i) ''ᵁ ((p₁ U i j) ''ᵁ V)) from (glued U D).presheaf.map (eqToHom E₁).op s)
  have r2 := restrictGluedHom_app U D j ((p₂ U i j) ''ᵁ V)
    (show compatible U D ((incl U j) ''ᵁ ((p₂ U i j) ''ᵁ V)) from (glued U D).presheaf.map (eqToHom E₂).op s)
  erw [r1, r2]

  have g1 : (show compatible U D ((incl U i) ''ᵁ ((p₁ U i j) ''ᵁ V)) from (glued U D).presheaf.map (eqToHom E₁).op s).1 i =
      (Dobj U D i).presheaf.map ((Opens.map (incl U i).base).map (eqToHom E₁)).op (s.1 i) := rfl
  have g2 : (show compatible U D ((incl U j) ''ᵁ ((p₂ U i j) ''ᵁ V)) from (glued U D).presheaf.map (eqToHom E₂).op s).1 j =
      (Dobj U D j).presheaf.map ((Opens.map (incl U j).base).map (eqToHom E₂)).op (s.1 j) := rfl
  erw [g1, g2]
  erw [map_map (Dobj U D i), map_map (Dobj U D j)]
  erw [presheaf_map_congr (Dobj U D i) _ (homOfLE (cs_le U i j V)) (s.1 i),
    presheaf_map_congr (Dobj U D j) _ (homOfLE (cs_le' U i j V)) (s.1 j)]

  have hc := s.2 i j
  rw [α_app, β_app] at hc
  have nat := app_presheaf_map (ρ U D i j).hom (eqToHom (((U i ⊓ U j).ι.preimage_image_eq V).symm))
    ((Dobj U D i).presheaf.map (homOfLE (α_le U i j _)).op (s.1 i))
  rw [restrict_map, restrict_map] at nat
  erw [hc] at nat
  erw [presheaf_map_congr (Dobj U D i) (homOfLE (cs_le U i j V))
    ((Hom.opensFunctor (p₁ U i j)).map (eqToHom (((U i ⊓ U j).ι.preimage_image_eq V).symm)) ≫
      homOfLE (α_le U i j _)) (s.1 i)]
  erw [← map_map (Dobj U D i) (homOfLE (α_le U i j ((U i ⊓ U j).ι ''ᵁ V)))
    ((Hom.opensFunctor (p₁ U i j)).map (eqToHom (((U i ⊓ U j).ι.preimage_image_eq V).symm))) (s.1 i)]
  erw [nat]
  exact (map_map _ _ _ _).trans (presheaf_map_congr _ _ _ _)

theorem pseudo_map_map {X X' : Scheme.{u}} (f : X ⟶ X') {M N : MOD.obj (.mk (op X'))} (ψ : M ⟶ N) :
    (MOD.map f.op.toLoc).toFunctor.map ψ = (pullback f).map ψ := rfl

theorem pullback_map_eq {X X' : Scheme.{u}} (f : X ⟶ X') [IsOpenImmersion f] {M N : X'.Modules} (ψ : M ⟶ N) :
    (pullback f).map ψ = (restrictFunctorIsoPullback f).inv.app M ≫ (restrictFunctor f).map ψ ≫
      (restrictFunctorIsoPullback f).hom.app N := by
  rw [← Category.assoc, ← (restrictFunctorIsoPullback f).inv.naturality ψ, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id]

theorem dictM {X₀ X₁ X₂ : Scheme.{u}} (e : X₀ ⟶ X₁) (a : X₁ ⟶ X₂) (a' : X₀ ⟶ X₂) [IsOpenImmersion e]
    [IsOpenImmersion a] [IsOpenImmersion a'] (w : e ≫ a = a') (M : X₂.Modules) :
    (restrictFunctorIsoPullback a').hom.app M ≫
      ((Scheme.Modules.pullbackCongr w.symm).hom.app M ≫ (Scheme.Modules.pullbackComp e a).inv.app M) ≫
      (restrictFunctorIsoPullback e).inv.app ((pullback a).obj M) ≫
      (restrictFunctor e).map ((restrictFunctorIsoPullback a).inv.app M) = castComp e a a' w M := by
  rw [← HomZar.Mdl_mapComp'_hom_app e a M a' w]
  exact Φ_eq_congr_comp e a a' w M

set_option maxHeartbeats 3200000 in

theorem commZ₀_formal {X₀ X₁ X₂ S : Scheme.{u}} (p₁ : X₀ ⟶ X₁) (p₂ : X₀ ⟶ X₂) (ι₁ : X₁ ⟶ S) (ι₂ : X₂ ⟶ S)
    (q₀ : X₀ ⟶ S) [IsOpenImmersion p₁] [IsOpenImmersion p₂] [IsOpenImmersion ι₁] [IsOpenImmersion ι₂]
    [IsOpenImmersion q₀] (w₁ : p₁ ≫ ι₁ = q₀) (w₂ : p₂ ≫ ι₂ = q₀) (G : S.Modules) (M₁ : X₁.Modules)
    (M₂ : X₂.Modules) (r₁ : (restrictFunctor ι₁).obj G ⟶ M₁) (r₂ : (restrictFunctor ι₂).obj G ⟶ M₂)
    (ρ₀ : (restrictFunctor p₁).obj M₁ ⟶ (restrictFunctor p₂).obj M₂)
    (φ₀ : (pullback p₁).obj M₁ ⟶ (pullback p₂).obj M₂)
    (hφ₀ : (restrictFunctorIsoPullback p₁).hom.app M₁ ≫ φ₀ ≫ (restrictFunctorIsoPullback p₂).inv.app M₂ = ρ₀)
    (cs : castComp p₁ ι₁ q₀ w₁ G ≫ (restrictFunctor p₁).map r₁ ≫ ρ₀ =
      castComp p₂ ι₂ q₀ w₂ G ≫ (restrictFunctor p₂).map r₂) :
    (pullback p₁).map ((restrictFunctorIsoPullback ι₁).inv.app G ≫ r₁) ≫ φ₀ =
      (((Scheme.Modules.pullbackComp p₁ ι₁).hom.app G ≫ (Scheme.Modules.pullbackCongr w₁).hom.app G) ≫
        (Scheme.Modules.pullbackCongr w₂.symm).hom.app G ≫ (Scheme.Modules.pullbackComp p₂ ι₂).inv.app G) ≫
      (pullback p₂).map ((restrictFunctorIsoPullback ι₂).inv.app G ≫ r₂) := by
  rw [← hφ₀, ← dictM p₁ ι₁ q₀ w₁ G, ← dictM p₂ ι₂ q₀ w₂ G] at cs
  have c0 : (Scheme.Modules.pullbackComp p₁ ι₁).inv.app G ≫ (Scheme.Modules.pullbackComp p₁ ι₁).hom.app G = 𝟙 _ :=
    Iso.inv_hom_id_app _ _
  refine (cancel_epi ((restrictFunctorIsoPullback q₀).hom.app G ≫
      ((Scheme.Modules.pullbackCongr w₁.symm).hom.app G ≫ (Scheme.Modules.pullbackComp p₁ ι₁).inv.app G))).mp ?_
  refine (cancel_mono ((restrictFunctorIsoPullback p₂).inv.app M₂)).mp ?_
  simp only [Functor.comp_obj, Functor.map_comp, pullback_map_eq,
    Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app,
    Category.comp_id, Scheme.Modules.pullbackCongr, eqToIso.hom, eqToHom_app, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, reassoc_of% c0] at cs ⊢
  exact cs

theorem gluedIso_hom (k : ι) : (gluedIso U D k).hom =
    (restrictFunctorIsoPullback (incl U k)).inv.app (glued U D) ≫ restrictGluedHom U D k := rfl

theorem commZ₀ (i j : ι) :
    (MOD.map (p₁ U i j).op.toLoc).toFunctor.map (gluedIso U D i).hom ≫
        D.hom (U i ⊓ U j).ι (p₁ U i j) (p₂ U i j) (Y.homOfLE_ι inf_le_left) (Y.homOfLE_ι inf_le_right) =
      ((MOD.toDescentData (incl U)).obj (glued U D)).hom (U i ⊓ U j).ι (p₁ U i j) (p₂ U i j)
          (Y.homOfLE_ι inf_le_left) (Y.homOfLE_ι inf_le_right) ≫
        (MOD.map (p₂ U i j).op.toLoc).toFunctor.map (gluedIso U D j).hom := by
  rw [ofObj_hom_eq U (glued U D) (U i ⊓ U j).ι (p₁ U i j) (p₂ U i j) (Y.homOfLE_ι inf_le_left) (Y.homOfLE_ι inf_le_right)]
  rw [pseudo_map_map, pseudo_map_map, gluedIso_hom, gluedIso_hom]
  generalize hφ : (D.hom (U i ⊓ U j).ι (p₁ U i j) (p₂ U i j) (Y.homOfLE_ι inf_le_left) (Y.homOfLE_ι inf_le_right) :
      (pullback (p₁ U i j)).obj (Dobj U D i) ⟶ (pullback (p₂ U i j)).obj (Dobj U D j)) = φ₀
  have hφ₀ : (restrictFunctorIsoPullback (p₁ U i j)).hom.app (Dobj U D i) ≫ φ₀ ≫
      (restrictFunctorIsoPullback (p₂ U i j)).inv.app (Dobj U D j) = (ρ U D i j).hom := by
    rw [← hφ]; exact (τ_hom_eq U D i j _ _ _).symm
  exact commZ₀_formal (p₁ U i j) (p₂ U i j) (incl U i) (incl U j) (U i ⊓ U j).ι (Y.homOfLE_ι inf_le_left)
    (Y.homOfLE_ι inf_le_right) (glued U D) (Dobj U D i) (Dobj U D j) (restrictGluedHom U D i) (restrictGluedHom U D j)
    (ρ U D i j).hom φ₀ hφ₀ (comm_sections U D i j)

theorem gluedIso_comm ⦃Z : Scheme.{u}⦄ (q : Z ⟶ Y) ⦃i j : ι⦄ (f₁ : Z ⟶ (U i : Scheme.{u})) (f₂ : Z ⟶ (U j : Scheme.{u}))
    (h₁ : f₁ ≫ incl U i = q) (h₂ : f₂ ≫ incl U j = q) :
    (MOD.map f₁.op.toLoc).toFunctor.map (gluedIso U D i).hom ≫ D.hom q f₁ f₂ h₁ h₂ =
      ((MOD.toDescentData (incl U)).obj (glued U D)).hom q f₁ f₂ h₁ h₂ ≫
        (MOD.map f₂.op.toLoc).toFunctor.map (gluedIso U D j).hom := by

  have H : Set.range q.base ⊆ Set.range (U i ⊓ U j).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← h₁, ← Scheme.Opens.range_ι (U i)]
      exact ⟨f₁.base z, by first | rfl | simp⟩
    · rw [← h₂, ← Scheme.Opens.range_ι (U j)]
      exact ⟨f₂.base z, by first | rfl | simp⟩
  let φ := IsOpenImmersion.lift (U i ⊓ U j).ι q H
  have hφ : φ ≫ (U i ⊓ U j).ι = q := IsOpenImmersion.lift_fac _ _ _
  have hφ₁ : φ ≫ p₁ U i j = f₁ := by
    rw [← cancel_mono (U i).ι, Category.assoc, Scheme.homOfLE_ι, hφ]; exact h₁.symm
  have hφ₂ : φ ≫ p₂ U i j = f₂ := by
    rw [← cancel_mono (U j).ι, Category.assoc, Scheme.homOfLE_ι, hφ]; exact h₂.symm
  rw [← D_pullHom U D φ (U i ⊓ U j).ι q hφ (p₁ U i j) (p₂ U i j) (Y.homOfLE_ι inf_le_left) (Y.homOfLE_ι inf_le_right)
      f₁ f₂ hφ₁ hφ₂ h₁ h₂,
    ← ofObj_pullHom U (glued U D) φ (U i ⊓ U j).ι q hφ (p₁ U i j) (p₂ U i j) (Y.homOfLE_ι inf_le_left)
      (Y.homOfLE_ι inf_le_right) f₁ f₂ hφ₁ hφ₂ h₁ h₂,
    Pseudofunctor.LocallyDiscreteOpToCat.map_map_eq_pullHom (F := MOD) (p₁ U i j) (gluedIso U D i).hom φ f₁ hφ₁]
  erw [Pseudofunctor.LocallyDiscreteOpToCat.map_map_eq_pullHom (F := MOD) (p₂ U i j) (gluedIso U D j).hom φ f₂ hφ₂]
  erw [← Pseudofunctor.LocallyDiscreteOpToCat.pullHom_comp', ← Pseudofunctor.LocallyDiscreteOpToCat.pullHom_comp',
    commZ₀ U D i j]
  rfl

noncomputable def isoDescentData : (MOD.toDescentData (incl U)).obj (glued U D) ≅ D :=
  Pseudofunctor.DescentData.isoMk (fun k => gluedIso U D k) (fun Z q i j f₁ f₂ h₁ h₂ => gluedIso_comm U D q f₁ f₂ h₁ h₂)

theorem essSurj_incl : (MOD.toDescentData (incl U)).EssSurj :=
  ⟨fun D => ⟨glued U D, ⟨isoDescentData U D⟩⟩⟩

end Opens

theorem toDescentData_essSurj_of_openCover'
    {Y : Scheme.{u}} {ι : Type v} {V : ι → Scheme.{u}} (g : ∀ i, V i ⟶ Y) [∀ i, IsOpenImmersion (g i)]
    (hg : ∀ y : Y, ∃ i, y ∈ Set.range (g i).base) :
    (MOD.toDescentData g).EssSurj :=
  (essSurj_iff_of_sieve_eq g (fun O : Ranges g => O.1.ι) (sieve_ofArrows_eq_opensRange g)).mpr
    (essSurj_incl (fun O : Ranges g => O.1))

end AlgebraicGeometry.Scheme.Modules.ObjGlue

open _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_toDescentData_essSurj_of_openCover.AlgebraicGeometry.Scheme.Modules in
theorem solution
    {Y : Scheme.{u}} {ι : Type v} {V : ι → Scheme.{u}} (g : ∀ i, V i ⟶ Y) [∀ i, IsOpenImmersion (g i)]
    (hg : ∀ y : Y, ∃ i, y ∈ Set.range (g i).base) :
    (((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData g).EssSurj :=
  ObjGlue.toDescentData_essSurj_of_openCover' g hg

end S_AlgebraicGeometry_Scheme_Modules_toDescentData_essSurj_of_openCover
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_toDescentData_essSurj_of_openCover (solution)
