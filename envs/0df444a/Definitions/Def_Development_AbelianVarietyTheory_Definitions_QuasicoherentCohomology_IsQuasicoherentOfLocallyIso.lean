-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasicoherentOfLocallyIso
-- name    : Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasicoherentOfLocallyIso
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T13:57:22.916427+00:00
-- url     : https://prove2.me/theorems/eff16b1b-1dce-54f1-b3e2-8bf0604bde51
-- title:
--   Is Quasicoherent Of Locally Iso
-- statement:
--   Definitions and structural lemmas for Is Quasicoherent Of Locally Iso, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasicoherentOfLocallyIso.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_res_res
import Theorems.Thm_GlobalTheory_QCoh_res_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_res
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG resG_self val_res le_iSup_inf unitMod homOfLinear isoOfLinear toMod)
namespace GlobalTheory
namespace Twist
variable {X Y : Scheme.{0}}
abbrev resM (F : X.Modules) {U V : X.Opens} (h : V ≤ U) : Γ(F, U) →+ Γ(F, V) :=
  ConcreteCategory.hom (F.presheaf.map (homOfLE h).op)
variable {F G : X.Modules}
@[simp] theorem resM_resM {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(F, U)) :
    resM F h₂ (resM F h₁ s) = resM F (h₂.trans h₁) s :=
  QCoh.res_res F h₁ h₂ s
@[simp] theorem resM_self {U : X.Opens} (h : U ≤ U) (s : Γ(F, U)) : resM F h s = s :=
  QCoh.res_self F h s
@[simp] theorem resM_smul {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) (s : Γ(F, U)) :
    resM F h (a • s) = resG X h a • resM F h s :=
  F.map_smul (homOfLE h) a s
abbrev abSheaf (F : X.Modules) : TopCat.Sheaf Ab X := ⟨F.presheaf, F.isSheaf⟩
def restrictIsoOfLinear {U : X.Opens}
    (φ : ∀ V : X.Opens, V ≤ U → (Γ(F, V) ≃ₗ[Γ(X, V)] Γ(G, V)))
    (hφ : ∀ {V W : X.Opens} (hV : V ≤ U) (h : W ≤ V) (s : Γ(F, V)),
      φ W (h.trans hV) (resM F h s) = resM G h (φ V hV s))
    (g : Y ⟶ X) [IsOpenImmersion g] (hg : g.opensRange ≤ U) : F.restrict g ≅ G.restrict g :=
  isoOfLinear (F := F.restrict g) (G := G.restrict g)
    (fun W =>
      { toFun := φ (g ''ᵁ W) ((g.image_le_opensRange W).trans hg)
        invFun := (φ (g ''ᵁ W) ((g.image_le_opensRange W).trans hg)).symm
        map_add' := map_add _
        map_smul' := fun a s =>
          (φ (g ''ᵁ W) ((g.image_le_opensRange W).trans hg)).map_smul ((g.appIso W).inv a) s
        left_inv := LinearEquiv.symm_apply_apply _
        right_inv := LinearEquiv.apply_symm_apply _ })
    fun {V W} h s => hφ _ (g.image_mono h) s
set_option backward.isDefEq.respectTransparency false in

def overIsoOfRestrictIso {U : X.Opens} (e : F.restrict U.ι ≅ G.restrict U.ι) :
    F.over U ≅ G.over U :=
  (Scheme.Modules.overEquiv U).fullyFaithfulFunctor.preimageIso
    ((Scheme.Modules.overFunctorEquiv U).app F ≪≫ e ≪≫
      ((Scheme.Modules.overFunctorEquiv U).app G).symm)
set_option backward.isDefEq.respectTransparency false in

def generatorsOver {U V : X.Opens} (h : V ≤ U) (σ : (F.over U).GeneratingSections) :
    (F.over V).GeneratingSections :=
  (σ.map (SheafOfModules.overMap X.ringCatSheaf (homOfLE h))
    (SheafOfModules.overMapUnitIso (homOfLE h)).symm).ofEpi
    ((SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE h)).app F).hom
set_option backward.isDefEq.respectTransparency false in

def generatorsOfLocallyIso {ι : Type} {U : ι → X.Opens} (hU : ⨆ k, U k = ⊤)
    (e : ∀ (k : ι) (W : X.Opens), W ≤ U k → (F.restrict W.ι ≅ G.restrict W.ι))
    (σ : SheafOfModules.LocalGeneratorsData.{0} F) : SheafOfModules.LocalGeneratorsData.{0} G where
  I := σ.I × ι
  X p := σ.X p.1 ⊓ U p.2
  coversTop := by
    have hc : ⨆ k, σ.X k = ⊤ := (Opens.coversTop_iff _ _).1 σ.coversTop
    rw [Opens.coversTop_iff]
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (hc.ge (Set.mem_univ x))
    obtain ⟨l, hl⟩ := Opens.mem_iSup.1 (hU.ge (Set.mem_univ x))
    exact Opens.mem_iSup.2 ⟨(k, l), hk, hl⟩
  generators p := (generatorsOver inf_le_left (σ.generators p.1)).ofEpi
    (overIsoOfRestrictIso (e p.2 _ inf_le_right)).hom
section Stalk
variable {U : X.Opens} (φ : ∀ V : X.Opens, V ≤ U → (Γ(F, V) ≃ₗ[Γ(X, V)] Γ(G, V)))
  (hφ : ∀ {V W : X.Opens} (hV : V ≤ U) (h : W ≤ V) (s : Γ(F, V)),
    φ W (h.trans hV) (resM F h s) = resM G h (φ V hV s)) {x : X} (hx : x ∈ U)
theorem germ_resM {V W : X.Opens} (h : W ≤ V) {x : X} (hx : x ∈ W) (s : Γ(F, V)) :
    F.presheaf.germ W x hx (resM F h s) = F.presheaf.germ V x (h hx) s :=
  F.presheaf.germ_res_apply (homOfLE h) x hx s
def stalkHomOfLinear : F.presheaf.stalk x ⟶ G.presheaf.stalk x :=
  Limits.colimit.desc ((OpenNhds.inclusion x).op ⋙ F.presheaf)
    { pt := G.presheaf.stalk x
      ι :=
        { app := fun W => F.presheaf.map (homOfLE (inf_le_left : W.unop.1 ⊓ U ≤ W.unop.1)).op ≫
            AddCommGrpCat.ofHom (φ (W.unop.1 ⊓ U) inf_le_right).toLinearMap.toAddMonoidHom ≫
              G.presheaf.germ (W.unop.1 ⊓ U) x ⟨W.unop.2, hx⟩
          naturality := fun W W' f => by
            ext (s : Γ(F, W.unop.1))
            have h : W'.unop.1 ≤ W.unop.1 := leOfHom f.unop
            change G.presheaf.germ (W'.unop.1 ⊓ U) x ⟨W'.unop.2, hx⟩
              (φ _ inf_le_right (resM F inf_le_left (resM F h s))) =
              G.presheaf.germ (W.unop.1 ⊓ U) x ⟨W.unop.2, hx⟩
                (φ _ inf_le_right (resM F inf_le_left s))
            rw [← germ_resM (inf_le_inf_right U h) ⟨W'.unop.2, hx⟩, ← hφ, resM_resM,
              resM_resM] } }
theorem stalkHomOfLinear_germ {V : X.Opens} (hV : V ≤ U) (hxV : x ∈ V) (s : Γ(F, V)) :
    stalkHomOfLinear φ hφ hx (F.presheaf.germ V x hxV s) = G.presheaf.germ V x hxV (φ V hV s) := by
  have e : stalkHomOfLinear φ hφ hx (F.presheaf.germ V x hxV s) =
      G.presheaf.germ (V ⊓ U) x ⟨hxV, hx⟩ (φ _ inf_le_right (resM F inf_le_left s)) :=
    ConcreteCategory.congr_hom (Limits.colimit.ι_desc
      (F := (OpenNhds.inclusion x).op ⋙ F.presheaf) _ (op ⟨V, hxV⟩)) s
  rw [e, hφ hV]
  exact germ_resM _ _ _
include hx in

theorem exists_germ_eq_of_mem (t : (F.presheaf.stalk x :)) :
    ∃ (V : X.Opens) (_ : V ≤ U) (hxV : x ∈ V) (s : Γ(F, V)), F.presheaf.germ V x hxV s = t := by
  obtain ⟨V, hV, s, rfl⟩ := F.presheaf.exists_germ_eq t
  exact ⟨V ⊓ U, inf_le_right, ⟨hV, hx⟩, resM F inf_le_left s, germ_resM _ _ _⟩
include hφ in

theorem symm_resM {V W : X.Opens} (hV : V ≤ U) (h : W ≤ V) (s : Γ(G, V)) :
    (φ W (h.trans hV)).symm (resM G h s) = resM F h ((φ V hV).symm s) := by
  rw [LinearEquiv.symm_apply_eq, hφ hV, LinearEquiv.apply_symm_apply]
def stalkEquivOfLinear :
    (F.presheaf.stalk x :) ≃ₗ[X.presheaf.stalk x] (G.presheaf.stalk x :) where
  toFun := stalkHomOfLinear φ hφ hx
  invFun := stalkHomOfLinear (fun V hV => (φ V hV).symm) (symm_resM φ hφ) hx
  map_add' := map_add _
  map_smul' r t := by
    obtain ⟨V, hV, hxV, s, rfl⟩ := exists_germ_eq_of_mem hx t
    obtain ⟨W, hxW, a, rfl⟩ := X.presheaf.exists_germ_eq r
    have hxVW : x ∈ V ⊓ W := ⟨hxV, hxW⟩
    rw [RingHom.id_apply, ← germ_resM (inf_le_left : V ⊓ W ≤ V) hxVW,
      ← X.presheaf.germ_res_apply (homOfLE (inf_le_right : V ⊓ W ≤ W)) x hxVW,
      ← QCoh.germ_smul, stalkHomOfLinear_germ φ hφ hx (inf_le_left.trans hV),
      stalkHomOfLinear_germ φ hφ hx (inf_le_left.trans hV), map_smul, QCoh.germ_smul]
  left_inv t := by
    obtain ⟨V, hV, hxV, s, rfl⟩ := exists_germ_eq_of_mem hx t
    rw [stalkHomOfLinear_germ φ hφ hx hV, stalkHomOfLinear_germ _ _ hx hV,
      LinearEquiv.symm_apply_apply]
  right_inv t := by
    obtain ⟨V, hV, hxV, s, rfl⟩ := exists_germ_eq_of_mem hx t
    rw [stalkHomOfLinear_germ _ _ hx hV, stalkHomOfLinear_germ φ hφ hx hV,
      LinearEquiv.apply_symm_apply]
end Stalk
section Mate
variable {C D : Type*} [Category C] [Category D] {P : C ⥤ D} {Q : D ⥤ C} (adj : P ⊣ Q)
  (S : C ⥤ C) (T : D ⥤ D) (e : Q ⋙ S ≅ T ⋙ Q)
def mateHom (A : C) : P.obj (S.obj A) ⟶ T.obj (P.obj A) :=
  (adj.homEquiv _ _).symm (S.map (adj.unit.app A) ≫ e.hom.app (P.obj A))
end Mate
end Twist
end GlobalTheory


