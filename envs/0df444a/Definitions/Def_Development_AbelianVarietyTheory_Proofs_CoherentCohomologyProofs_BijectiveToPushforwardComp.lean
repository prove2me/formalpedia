-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_BijectiveToPushforwardComp
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_BijectiveToPushforwardComp
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T15:00:55.834643+00:00
-- url     : https://prove2.me/theorems/5f721737-3718-4fa4-93be-07b9f7ab8eaa
-- title:
--   Bijective To Pushforward Comp
-- statement:
--   Definitions and structural lemmas for Bijective To Pushforward Comp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/BijectiveToPushforwardComp.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_LB_chartEquiv_symm_apply
import Theorems.Thm_GlobalTheory_LB_pullSec_chartSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isLB_pull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory
namespace LB
variable {X Y : Scheme.{0}}
section Modules
variable {F G : X.Modules}
theorem modRes_modRes {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(F, U)) :
    F.presheaf.map (homOfLE h₂).op (F.presheaf.map (homOfLE h₁).op s) =
      F.presheaf.map (homOfLE (h₂.trans h₁)).op s := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl
theorem modRes_self {U : X.Opens} (h : U ≤ U) (s : Γ(F, U)) :
    F.presheaf.map (homOfLE h).op s = s := by
  have : (homOfLE h).op = 𝟙 (op U) := rfl
  rw [this, F.presheaf.map_id]; rfl
theorem modRes_smul {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) (s : Γ(F, U)) :
    F.presheaf.map (homOfLE h).op (a • s) = resG X h a • F.presheaf.map (homOfLE h).op s :=
  Scheme.Modules.map_smul F _ a s
theorem app_modRes (φ : F ⟶ G) {U V : X.Opens} (h : V ≤ U) (s : Γ(F, U)) :
    φ.app V (F.presheaf.map (homOfLE h).op s) = G.presheaf.map (homOfLE h).op (φ.app U s) :=
  ConcreteCategory.congr_hom ((Scheme.Modules.Hom.mapPresheaf φ).naturality (homOfLE h).op) s
theorem modSec_ext_of_cover {ι : Type} {V : X.Opens} (W : ι → X.Opens) (hW : ∀ k, W k ≤ V)
    (hc : V ≤ iSup W) {a b : Γ(F, V)}
    (h : ∀ k, F.presheaf.map (homOfLE (hW k)).op a = F.presheaf.map (homOfLE (hW k)).op b) :
    a = b :=
  TopCat.Sheaf.eq_of_locally_eq' ⟨F.presheaf, F.isSheaf⟩ W V (fun k => homOfLE (hW k)) hc a b h
theorem exists_modSec_of_cover {ι : Type} {V : X.Opens} (W : ι → X.Opens) (hW : ∀ k, W k ≤ V)
    (hc : V ≤ iSup W) (a : ∀ k, Γ(F, W k))
    (h : ∀ k l, F.presheaf.map (homOfLE (inf_le_left : W k ⊓ W l ≤ W k)).op (a k) =
      F.presheaf.map (homOfLE (inf_le_right : W k ⊓ W l ≤ W l)).op (a l)) :
    ∃ b : Γ(F, V), ∀ k, F.presheaf.map (homOfLE (hW k)).op b = a k := by
  obtain ⟨b, hb, -⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨F.presheaf, F.isSheaf⟩ W V
    (fun k => homOfLE (hW k)) hc a fun k l => h k l
  exact ⟨b, hb⟩
end Modules
variable {L : LB X}
def IsFrameFamily (L : LB X) {F : X.Modules} (σ : ∀ i, Γ(F, L.U i)) : Prop :=
  ∀ i j, F.presheaf.map (homOfLE (inf_le_right : L.U j ⊓ L.U i ≤ L.U i)).op (σ i) =
    (L.g j i : Γ(X, L.U j ⊓ L.U i)) •
      F.presheaf.map (homOfLE (inf_le_left : L.U j ⊓ L.U i ≤ L.U j)).op (σ j)
theorem IsFrameFamily.rel {F : X.Modules} {σ : ∀ i, Γ(F, L.U i)} (hσ : IsFrameFamily L σ)
    (i j : L.ι) {W : X.Opens} (hi : W ≤ L.U i) (hj : W ≤ L.U j) (h : W ≤ L.U j ⊓ L.U i) :
    F.presheaf.map (homOfLE hi).op (σ i) =
      resG X h (L.g j i : Γ(X, L.U j ⊓ L.U i)) • F.presheaf.map (homOfLE hj).op (σ j) := by
  have := congrArg (F.presheaf.map (homOfLE h).op) (hσ i j)
  rwa [modRes_smul, modRes_modRes, modRes_modRes] at this
theorem isFrameFamily_chartSec (hL : L.IsLB) : IsFrameFamily L (chartSec hL) := fun i j =>
  sec_ext fun k => by
    simp only [coord_map, coord_smul, coord_chartSec, resG_resG]
    rw [mul_comm]
    exact (resG_cocycle hL k j i _ _ _).symm
theorem IsFrameFamily.map {F G : X.Modules} {σ : ∀ i, Γ(F, L.U i)} (hσ : IsFrameFamily L σ)
    (φ : F ⟶ G) : IsFrameFamily L fun i => φ.app (L.U i) (σ i) := fun i j => by
  rw [← app_modRes, ← app_modRes, hσ i j, Scheme.Modules.Hom.app_smul]
theorem app_eq_smul (hL : L.IsLB) {F : X.Modules} (φ : toMod L ⟶ F) (i : L.ι) {V : X.Opens}
    (h : V ≤ L.U i) (s : Γ(toMod L, V)) :
    φ.app V s = chartEquiv hL i h s •
      F.presheaf.map (homOfLE h).op (φ.app (L.U i) (chartSec hL i)) := by
  rw [← app_modRes, ← Scheme.Modules.Hom.app_smul, ← chartEquiv_symm_apply,
    LinearEquiv.symm_apply_apply]
theorem hom_ext_chartSec (hL : L.IsLB) {F : X.Modules} {φ ψ : toMod L ⟶ F}
    (h : ∀ i, φ.app (L.U i) (chartSec hL i) = ψ.app (L.U i) (chartSec hL i)) : φ = ψ := by
  ext V s
  refine modSec_ext_of_cover (fun i => V ⊓ L.U i) (fun _ => inf_le_left)
    (le_iSup_inf hL.cover V) fun i => ?_
  change F.presheaf.map _ (φ.app V s) = F.presheaf.map _ (ψ.app V s)
  rw [← app_modRes, ← app_modRes, app_eq_smul hL φ i inf_le_right,
    app_eq_smul hL ψ i inf_le_right, h]
theorem exists_frame_glue (hL : L.IsLB) {F : X.Modules} {σ : ∀ i, Γ(F, L.U i)}
    (hσ : IsFrameFamily L σ) {V : X.Opens} (s : Γ(toMod L, V)) :
    ∃ t : Γ(F, V), ∀ i, F.presheaf.map (homOfLE (inf_le_left : V ⊓ L.U i ≤ V)).op t =
      coord s i • F.presheaf.map (homOfLE (inf_le_right : V ⊓ L.U i ≤ L.U i)).op (σ i) := by
  refine exists_modSec_of_cover (fun i => V ⊓ L.U i) (fun _ => inf_le_left)
    (le_iSup_inf hL.cover V) _ fun i j => ?_
  have l : V ⊓ L.U i ⊓ (V ⊓ L.U j) ≤ L.U i ⊓ L.U j := inf_le_inf inf_le_right inf_le_right
  rw [modRes_smul, modRes_smul, modRes_modRes, modRes_modRes,
    coord_rel s i j _ inf_le_right l, hσ.rel j i _ (l.trans inf_le_left) l, mul_comm, mul_smul]
def frameFun (hL : L.IsLB) {F : X.Modules} {σ : ∀ i, Γ(F, L.U i)}
    (hσ : IsFrameFamily L σ) {V : X.Opens} (s : Γ(toMod L, V)) : Γ(F, V) :=
  (exists_frame_glue hL hσ s).choose
theorem modRes_frameFun (hL : L.IsLB) {F : X.Modules} {σ : ∀ i, Γ(F, L.U i)}
    (hσ : IsFrameFamily L σ) {V : X.Opens} (s : Γ(toMod L, V)) (i : L.ι) {W : X.Opens}
    (hV : W ≤ V) (hi : W ≤ L.U i) :
    F.presheaf.map (homOfLE hV).op (frameFun hL hσ s) =
      resG X (le_inf hV hi) (coord s i) • F.presheaf.map (homOfLE hi).op (σ i) := by
  have := congrArg (F.presheaf.map (homOfLE (le_inf hV hi)).op)
    ((exists_frame_glue hL hσ s).choose_spec i)
  rwa [modRes_smul, modRes_modRes, modRes_modRes] at this
def homOfFrames (hL : L.IsLB) {F : X.Modules} {σ : ∀ i, Γ(F, L.U i)}
    (hσ : IsFrameFamily L σ) : toMod L ⟶ F :=
  homOfLinear (fun V =>
    { toFun := frameFun hL hσ
      map_add' := fun s t => modSec_ext_of_cover (fun i => V ⊓ L.U i) (fun _ => inf_le_left)
        (le_iSup_inf hL.cover V) fun i => by
          rw [map_add, modRes_frameFun hL hσ _ i _ inf_le_right,
            modRes_frameFun hL hσ _ i _ inf_le_right, modRes_frameFun hL hσ _ i _ inf_le_right,
            coord_add, map_add, add_smul]
      map_smul' := fun a s => modSec_ext_of_cover (fun i => V ⊓ L.U i) (fun _ => inf_le_left)
        (le_iSup_inf hL.cover V) fun i => by
          rw [RingHom.id_apply, modRes_smul, modRes_frameFun hL hσ _ i _ inf_le_right,
            modRes_frameFun hL hσ _ i _ inf_le_right, coord_smul, map_mul, resG_resG,
            mul_smul] })
    fun {V W} h s => modSec_ext_of_cover (fun i => W ⊓ L.U i) (fun _ => inf_le_left)
      (le_iSup_inf hL.cover W) fun i => by
        change F.presheaf.map _ (frameFun hL hσ _) =
          F.presheaf.map _ (F.presheaf.map _ (frameFun hL hσ s))
        rw [modRes_modRes, modRes_frameFun hL hσ _ i _ inf_le_right,
          modRes_frameFun hL hσ _ i _ inf_le_right, coord_map, resG_resG]
theorem homOfFrames_app_chartSec (hL : L.IsLB) {F : X.Modules} {σ : ∀ i, Γ(F, L.U i)}
    (hσ : IsFrameFamily L σ) (i : L.ι) :
    (homOfFrames hL hσ).app (L.U i) (chartSec hL i) = σ i := by
  have := modRes_frameFun hL hσ (chartSec hL i) i le_rfl le_rfl
  rw [modRes_self, modRes_self, coord_chartSec, resG_resG, resG_g_self hL, one_smul] at this
  exact this
def homEquivFrames (hL : L.IsLB) (F : X.Modules) :
    (toMod L ⟶ F) ≃ {σ : ∀ i, Γ(F, L.U i) // IsFrameFamily L σ} where
  toFun φ := ⟨fun i => φ.app (L.U i) (chartSec hL i), (isFrameFamily_chartSec hL).map φ⟩
  invFun σ := homOfFrames hL σ.2
  left_inv φ := hom_ext_chartSec hL fun i =>
    homOfFrames_app_chartSec hL ((isFrameFamily_chartSec hL).map φ) i
  right_inv σ := Subtype.ext (funext fun i => homOfFrames_app_chartSec hL σ.2 i)
theorem bijective_toPushforward_comp (hL : L.IsLB) (f : Y ⟶ X) (G : Y.Modules) :
    Function.Bijective fun ψ : toMod (L.pull f) ⟶ G =>
      toPushforward L f ≫ (Scheme.Modules.pushforward f).map ψ := by
  have hL' := Semi.LB.isLB_pull hL f
  have key (ψ : toMod (L.pull f) ⟶ G) (j : (L.pull f).ι) :
      ((toPushforward L f ≫ (Scheme.Modules.pushforward f).map ψ).app (L.U (j PUnit.unit))
        (chartSec hL (j PUnit.unit)) : Γ(G, f ⁻¹ᵁ L.U (j PUnit.unit))) =
      G.presheaf.map (homOfLE (pull_U f j).ge).op (ψ.app _ (chartSec hL' j)) := by
    rw [← app_modRes, ← pullSec_chartSec f hL j]
    rfl
  constructor
  · intro ψ ψ' h
    refine hom_ext_chartSec hL' fun j => ?_
    have e := key ψ j
    rw [show toPushforward L f ≫ (Scheme.Modules.pushforward f).map ψ = _ from h, key ψ' j] at e
    have := congrArg (G.presheaf.map (homOfLE (pull_U_le f j)).op) e
    rw [modRes_modRes, modRes_modRes, modRes_self, modRes_self] at this
    exact this.symm
  · intro φ
    let τ : ∀ i, Γ(G, f ⁻¹ᵁ L.U i) := fun i => φ.app (L.U i) (chartSec hL i)
    have hτ (i j : L.ι) : G.presheaf.map (homOfLE (f.preimage_mono
          (inf_le_right : L.U j ⊓ L.U i ≤ L.U i))).op (τ i) =
        (f.app _).hom (L.g j i : Γ(X, L.U j ⊓ L.U i)) • G.presheaf.map (homOfLE (f.preimage_mono
          (inf_le_left : L.U j ⊓ L.U i ≤ L.U j))).op (τ j) :=
      (isFrameFamily_chartSec hL).map φ i j
    let σ : ∀ j, Γ(G, (L.pull f).U j) := fun j =>
      G.presheaf.map (homOfLE (pull_U_le f j)).op (τ (j PUnit.unit))
    have hσ : IsFrameFamily (L.pull f) σ := fun i j => by
      have l : (L.pull f).U j ⊓ (L.pull f).U i ≤
          f ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U (i PUnit.unit)) :=
        inf_le_inf (pull_U_le f j) (pull_U_le f i)
      have := congrArg (G.presheaf.map (homOfLE l).op) (hτ (i PUnit.unit) (j PUnit.unit))
      rw [modRes_smul, modRes_modRes, modRes_modRes, resG_app] at this
      have e := resG_pull_g f j i le_rfl
      rw [resG_self] at e
      simp only [σ]
      rw [modRes_modRes, modRes_modRes, e]
      exact this
    refine ⟨homOfFrames hL' hσ, hom_ext_chartSec hL fun i => ?_⟩
    have H (j : (L.pull f).ι) : G.presheaf.map (homOfLE (pull_U f j).ge).op
        ((homOfFrames hL' hσ).app _ (chartSec hL' j)) = τ (j PUnit.unit) := by
      rw [homOfFrames_app_chartSec]
      simp only [σ]
      rw [modRes_modRes, modRes_self]
    exact (key _ (fun _ => i)).trans (H fun _ => i)
theorem isIso_pullbackHom {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) :
    IsIso (GlobalTheory.LB.pullbackHom L f) := by
  refine isIso_of_coyoneda_map_bijective _ fun G => ?_
  have e : (fun ψ : toMod (L.pull f) ⟶ G => pullbackHom L f ≫ ψ) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm ∘
        fun ψ : toMod (L.pull f) ⟶ G =>
          toPushforward L f ≫ (Scheme.Modules.pushforward f).map ψ := by
    funext ψ
    exact ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_right_symm
      _ _).symm
  exact e ▸ (Equiv.bijective _).comp (bijective_toPushforward_comp hL f G)
def pullbackIso (hL : L.IsLB) (f : Y ⟶ X) :
    (Scheme.Modules.pullback f).obj (toMod L) ≅ toMod (L.pull f) :=
  haveI := isIso_pullbackHom hL f
  asIso (pullbackHom L f)
end LB
end GlobalTheory


