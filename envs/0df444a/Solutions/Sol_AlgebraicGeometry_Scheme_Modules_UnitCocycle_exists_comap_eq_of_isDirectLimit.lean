-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.UnitCocycle.exists_comap_eq_of_isDirectLimit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/8c29931f-cecb-55e0-9a27-cc15c0521e32

import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_app_eq_of_isCompact_of_isDirectLimit
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_app_eq_app_of_isCompact_of_isDirectLimit
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_iSup_preimage_eq_top_of_isDirectLimit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_UnitCocycle_exists_comap_eq_of_isDirectLimit
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_UnitCocycle_exists_comap_eq_of_isDirectLimit.AlgebraicGeometry TopologicalSpace Opposite"

universe u

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.congr_app quasiSeparatedSpace_of_quasiSeparated Scheme.Hom QuasiCompact Spec Spec.map Scheme Scheme.Hom.preimage_mono Scheme.Hom.comp_app Scheme.Modules QuasiSeparated Scheme.Hom.comp_preimage Scheme.Modules.UnitCocycle Scheme.exists_app_eq_of_isCompact_of_isDirectLimit Scheme.exists_app_eq_app_of_isCompact_of_isDirectLimit Scheme.exists_iSup_preimage_eq_top_of_isDirectLimit"
namespace CocycleFil
p2m_open "AlgebraicGeometry"

p2m_open "AlgebraicGeometry.Scheme.Modules"

section Setup

variable {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
  {G : ι → Type u} [∀ i, CommRing (G i)] (φ : ∀ i j : ι, i ≤ j → G i →+* G j)
  [DirectedSystem G fun i j h => ⇑(φ i j h)]
  {R : Type u} [CommRing R] (g : ∀ i, G i →+* R)
  (hR : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i))
  (i : ι) {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of (G i)))

include hR

theorem comp_eq (a b : ι) (h : a ≤ b) : (g b).comp (φ a b h) = g a :=
  RingHom.ext fun x => hR.compatibility a b h x

omit hR in
theorem comp_eq' (a b c : ι) (hab : a ≤ b) (hbc : b ≤ c) : (φ b c hbc).comp (φ a b hab) = φ a c (hab.trans hbc) :=
  RingHom.ext fun x => DirectedSystem.map_map' (f := φ) hab hbc x

theorem spec_comp (a b : ι) (h : a ≤ b) :
    Spec.map (CommRingCat.ofHom (g b)) ≫ Spec.map (CommRingCat.ofHom (φ a b h)) = Spec.map (CommRingCat.ofHom (g a)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, comp_eq φ g hR]

omit hR in
theorem spec_comp' (a b c : ι) (hab : a ≤ b) (hbc : b ≤ c) :
    Spec.map (CommRingCat.ofHom (φ b c hbc)) ≫ Spec.map (CommRingCat.ofHom (φ a b hab)) =
      Spec.map (CommRingCat.ofHom (φ a c (hab.trans hbc))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, comp_eq' φ]

abbrev XR : Scheme.{u} := Limits.pullback fX (Spec.map (CommRingCat.ofHom (g i)))

abbrev XS (j : ι) (h : i ≤ j) : Scheme.{u} := Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j h)))
abbrev prR : XR g i fX ⟶ X := Limits.pullback.fst _ _
abbrev prS (j : ι) (h : i ≤ j) : XS φ i fX j h ⟶ X := Limits.pullback.fst _ _

def cc (j : ι) (h : i ≤ j) : XR g i fX ⟶ XS φ i fX j h :=
  Limits.pullback.lift (Limits.pullback.fst _ _) (Limits.pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (g j)))
    (by rw [Category.assoc, spec_comp φ g hR, Limits.pullback.condition])

theorem cc_fst (j : ι) (h : i ≤ j) : cc φ g hR i fX j h ≫ Limits.pullback.fst _ _ = Limits.pullback.fst _ _ :=
  Limits.pullback.lift_fst _ _ _
theorem cc_snd (j : ι) (h : i ≤ j) :
    cc φ g hR i fX j h ≫ Limits.pullback.snd _ _ = Limits.pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (g j)) :=
  Limits.pullback.lift_snd _ _ _

theorem cc_unique (j : ι) (h : i ≤ j) (c : XR g i fX ⟶ XS φ i fX j h)
    (h1 : c ≫ Limits.pullback.fst _ _ = Limits.pullback.fst _ _)
    (h2 : c ≫ Limits.pullback.snd _ _ = Limits.pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (g j))) :
    c = cc φ g hR i fX j h := by
  apply Limits.pullback.hom_ext
  · rw [h1, cc_fst]
  · rw [h2, cc_snd]

omit hR in

def dd (k l : ι) (hk : i ≤ k) (hkl : k ≤ l) : XS φ i fX l (hk.trans hkl) ⟶ XS φ i fX k hk :=
  Limits.pullback.lift (Limits.pullback.fst _ _) (Limits.pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (φ k l hkl)))
    (by rw [Category.assoc, spec_comp' φ, Limits.pullback.condition])

omit hR in
theorem dd_fst (k l : ι) (hk : i ≤ k) (hkl : k ≤ l) : dd φ i fX k l hk hkl ≫ Limits.pullback.fst _ _ = Limits.pullback.fst _ _ :=
  Limits.pullback.lift_fst _ _ _
omit hR in
theorem dd_snd (k l : ι) (hk : i ≤ k) (hkl : k ≤ l) :
    dd φ i fX k l hk hkl ≫ Limits.pullback.snd _ _ = Limits.pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (φ k l hkl)) :=
  Limits.pullback.lift_snd _ _ _

theorem cc_dd (k l : ι) (hk : i ≤ k) (hkl : k ≤ l) :
    cc φ g hR i fX l (hk.trans hkl) ≫ dd φ i fX k l hk hkl = cc φ g hR i fX k hk := by
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, dd_fst, cc_fst, cc_fst]
  · rw [Category.assoc, dd_snd, ← Category.assoc, cc_snd, Category.assoc, spec_comp φ g hR, cc_snd]

omit hR in
theorem dd_dd (k l m : ι) (hk : i ≤ k) (hkl : k ≤ l) (hlm : l ≤ m) :
    dd φ i fX l m (hk.trans hkl) hlm ≫ dd φ i fX k l hk hkl = dd φ i fX k m hk (hkl.trans hlm) := by
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, dd_fst, dd_fst, dd_fst]
  · rw [Category.assoc, dd_snd, ← Category.assoc, dd_snd, Category.assoc, spec_comp' φ, dd_snd]

abbrev castO {Y : Scheme.{u}} {U V : Y.Opens} (e : U = V) : Γ(Y, V) →+* Γ(Y, U) :=
  (Y.presheaf.map (eqToHom e).op).hom

omit hR in
theorem castO_castO {Y : Scheme.{u}} {U V W : Y.Opens} (e : U = V) (e' : V = W) (x : Γ(Y, W)) :
    castO e (castO e' x) = castO (e.trans e') x := by
  change (Y.presheaf.map (eqToHom e').op ≫ Y.presheaf.map (eqToHom e).op) x = _
  rw [← Functor.map_comp, ← op_comp, eqToHom_trans]

omit hR in
theorem castO_rfl {Y : Scheme.{u}} {U : Y.Opens} (x : Γ(Y, U)) : castO (rfl : U = U) x = x := by
  change (Y.presheaf.map (eqToHom rfl).op) x = x
  rw [eqToHom_refl, op_id, Y.presheaf.map_id]; rfl

theorem pre_cc (j : ι) (h : i ≤ j) (V : X.Opens) :
    prR g i fX ⁻¹ᵁ V = cc φ g hR i fX j h ⁻¹ᵁ (prS φ i fX j h ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage]; exact congrArg (· ⁻¹ᵁ V) (cc_fst φ g hR i fX j h).symm

omit hR in
theorem pre_dd (k l : ι) (hk : i ≤ k) (hkl : k ≤ l) (V : X.Opens) :
    prS φ i fX l (hk.trans hkl) ⁻¹ᵁ V = dd φ i fX k l hk hkl ⁻¹ᵁ (prS φ i fX k hk ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage]; exact congrArg (· ⁻¹ᵁ V) (dd_fst φ i fX k l hk hkl).symm

omit hR in
theorem app_castO {Y Z : Scheme.{u}} (f : Y ⟶ Z) {U V : Z.Opens} (e : U = V) (y : Γ(Z, V)) :
    f.app U (castO e y) = castO (show f ⁻¹ᵁ U = f ⁻¹ᵁ V by rw [e]) (f.app V y) := by
  subst e
  rw [castO_rfl, castO_rfl]

omit hR in
theorem comp_app_apply {Y Z T : Scheme.{u}} (f : Y ⟶ Z) (h : Z ⟶ T) (U : T.Opens) (y : Γ(T, U)) :
    (f ≫ h).app U y = f.app (h ⁻¹ᵁ U) (h.app U y) := by
  rw [Scheme.Hom.comp_app]; rfl

def val (k : ι) (hk : i ≤ k) (V : X.Opens) : Γ(XS φ i fX k hk, prS φ i fX k hk ⁻¹ᵁ V) →+* Γ(XR g i fX, prR g i fX ⁻¹ᵁ V) :=
  (castO (pre_cc φ g hR i fX k hk V)).comp ((cc φ g hR i fX k hk).app (prS φ i fX k hk ⁻¹ᵁ V)).hom

omit hR in

def push (k l : ι) (hk : i ≤ k) (hkl : k ≤ l) (V : X.Opens) :
    Γ(XS φ i fX k hk, prS φ i fX k hk ⁻¹ᵁ V) →+* Γ(XS φ i fX l (hk.trans hkl), prS φ i fX l (hk.trans hkl) ⁻¹ᵁ V) :=
  (castO (pre_dd φ i fX k l hk hkl V)).comp ((dd φ i fX k l hk hkl).app (prS φ i fX k hk ⁻¹ᵁ V)).hom

theorem val_push (k l : ι) (hk : i ≤ k) (hkl : k ≤ l) (V : X.Opens) (t : Γ(XS φ i fX k hk, prS φ i fX k hk ⁻¹ᵁ V)) :
    val φ g hR i fX l (hk.trans hkl) V (push φ i fX k l hk hkl V t) = val φ g hR i fX k hk V t := by

  have h := congrArg (fun φ' => (ConcreteCategory.hom φ') t)
    (Scheme.Hom.congr_app (cc_dd φ g hR i fX k l hk hkl) (prS φ i fX k hk ⁻¹ᵁ V))
  simp only [CategoryTheory.comp_apply] at h
  rw [comp_app_apply] at h
  change castO _ ((cc φ g hR i fX l (hk.trans hkl)).app _ (castO _ ((dd φ i fX k l hk hkl).app _ t))) =
    castO _ ((cc φ g hR i fX k hk).app _ t)
  rw [app_castO, h]
  change castO _ (castO _ (castO _ _)) = _
  rw [castO_castO, castO_castO]

omit hR in
theorem app_rO {Y Z : Scheme.{u}} (f : Y ⟶ Z) {U U' : Z.Opens} (hU : U' ≤ U) (y : Γ(Z, U)) :
    GlueOfCocycle.rO (Scheme.Hom.preimage_mono f hU) (f.app U y) = f.app U' (GlueOfCocycle.rO hU y) := by
  have := congrArg (fun k => (ConcreteCategory.hom k) y) (f.naturality (homOfLE hU).op)
  simp only [CategoryTheory.comp_apply] at this
  exact this.symm

omit hR in
theorem rO_castO {Y : Scheme.{u}} {U V U' V' : Y.Opens} (e : U = V) (e' : U' = V') (hU : U' ≤ U) (hV : V' ≤ V)
    (y : Γ(Y, V)) : GlueOfCocycle.rO hU (castO e y) = castO e' (GlueOfCocycle.rO hV y) := by
  subst e e'
  rw [castO_rfl, castO_rfl]

theorem val_rO (k : ι) (hk : i ≤ k) {V V' : X.Opens} (hV : V' ≤ V) (t : Γ(XS φ i fX k hk, prS φ i fX k hk ⁻¹ᵁ V)) :
    val φ g hR i fX k hk V' (GlueOfCocycle.rO (Scheme.Hom.preimage_mono _ hV) t) =
      GlueOfCocycle.rO (Scheme.Hom.preimage_mono _ hV) (val φ g hR i fX k hk V t) := by
  change castO _ ((cc φ g hR i fX k hk).app _ (GlueOfCocycle.rO _ t)) = GlueOfCocycle.rO _ (castO _ ((cc φ g hR i fX k hk).app _ t))
  rw [← app_rO, rO_castO]

omit hR in
theorem push_rO (k l : ι) (hk : i ≤ k) (hkl : k ≤ l) {V V' : X.Opens} (hV : V' ≤ V)
    (t : Γ(XS φ i fX k hk, prS φ i fX k hk ⁻¹ᵁ V)) :
    push φ i fX k l hk hkl V' (GlueOfCocycle.rO (Scheme.Hom.preimage_mono _ hV) t) =
      GlueOfCocycle.rO (Scheme.Hom.preimage_mono _ hV) (push φ i fX k l hk hkl V t) := by
  change castO _ ((dd φ i fX k l hk hkl).app _ (GlueOfCocycle.rO _ t)) = GlueOfCocycle.rO _ (castO _ ((dd φ i fX k l hk hkl).app _ t))
  rw [← app_rO, rO_castO]

omit hR in
theorem push_push (k l m : ι) (hk : i ≤ k) (hkl : k ≤ l) (hlm : l ≤ m) (V : X.Opens)
    (t : Γ(XS φ i fX k hk, prS φ i fX k hk ⁻¹ᵁ V)) :
    push φ i fX l m (hk.trans hkl) hlm V (push φ i fX k l hk hkl V t) = push φ i fX k m hk (hkl.trans hlm) V t := by
  have h := congrArg (fun φ' => (ConcreteCategory.hom φ') t)
    (Scheme.Hom.congr_app (dd_dd φ i fX k l m hk hkl hlm) (prS φ i fX k hk ⁻¹ᵁ V))
  simp only [CategoryTheory.comp_apply] at h
  rw [comp_app_apply] at h
  change castO _ ((dd φ i fX l m (hk.trans hkl) hlm).app _ (castO _ ((dd φ i fX k l hk hkl).app _ t))) =
    castO _ ((dd φ i fX k m hk (hkl.trans hlm)).app _ t)
  rw [app_castO, h]
  change castO _ (castO _ (castO _ _)) = _
  rw [castO_castO, castO_castO]

omit hR in
theorem castO_injective {Y : Scheme.{u}} {U V : Y.Opens} (e : U = V) : Function.Injective (castO e) := by
  subst e; intro a b h; rwa [castO_rfl, castO_rfl] at h

theorem exists_val_eq [QuasiCompact fX] [QuasiSeparated fX] (V : X.Opens) (hV : IsCompact (V : Set X))
    (s : Γ(XR g i fX, prR g i fX ⁻¹ᵁ V)) :
    ∃ (k : ι) (hk : i ≤ k) (t : Γ(XS φ i fX k hk, prS φ i fX k hk ⁻¹ᵁ V)), val φ g hR i fX k hk V t = s := by
  obtain ⟨k, hk, t, H⟩ := AlgebraicGeometry.Scheme.exists_app_eq_of_isCompact_of_isDirectLimit φ g hR i fX V hV s
  exact ⟨k, hk, t, H (cc φ g hR i fX k hk) (cc_fst φ g hR i fX k hk) (cc_snd φ g hR i fX k hk) _⟩

theorem exists_push_eq [QuasiCompact fX] [QuasiSeparated fX] (V : X.Opens) (hV : IsCompact (V : Set X))
    (k : ι) (hk : i ≤ k) (t t' : Γ(XS φ i fX k hk, prS φ i fX k hk ⁻¹ᵁ V))
    (h : val φ g hR i fX k hk V t = val φ g hR i fX k hk V t') :
    ∃ (l : ι) (hkl : k ≤ l), push φ i fX k l hk hkl V t = push φ i fX k l hk hkl V t' := by
  obtain ⟨l, hkl, H⟩ := AlgebraicGeometry.Scheme.exists_app_eq_app_of_isCompact_of_isDirectLimit φ g hR i fX V hV k hk t t'
    (by
      intro c h1 h2
      obtain rfl := cc_unique φ g hR i fX k hk c h1 h2
      exact castO_injective (pre_cc φ g hR i fX k hk V) h)
  exact ⟨l, hkl, congrArg (castO (pre_dd φ i fX k l hk hkl V))
    (H (dd φ i fX k l hk hkl) (dd_fst φ i fX k l hk hkl) (dd_snd φ i fX k l hk hkl))⟩

theorem exists_cover [QuasiCompact fX] [QuasiSeparated fX] {κ : Type u} (W : κ → X.Opens)
    (hcov : (⨆ k, prR g i fX ⁻¹ᵁ W k) = ⊤) :
    ∃ (k : ι) (hk : i ≤ k), ∀ (l : ι) (hkl : k ≤ l), (⨆ q, prS φ i fX l (hk.trans hkl) ⁻¹ᵁ W q) = ⊤ := by
  obtain ⟨k, hk, H⟩ := AlgebraicGeometry.Scheme.exists_iSup_preimage_eq_top_of_isDirectLimit φ g hR i fX W hcov
  refine ⟨k, hk, fun l hkl => ?_⟩
  rw [show (fun q => prS φ i fX l (hk.trans hkl) ⁻¹ᵁ W q) = fun q => dd φ i fX k l hk hkl ⁻¹ᵁ (prS φ i fX k hk ⁻¹ᵁ W q) from
    funext fun q => pre_dd φ i fX k l hk hkl (W q)]
  exact (dd φ i fX k l hk hkl).iSup_preimage_eq_top H

end Setup

section Main

variable {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
  {G : ι → Type u} [∀ i, CommRing (G i)] (φ : ∀ i j : ι, i ≤ j → G i →+* G j)
  [DirectedSystem G fun i j h => ⇑(φ i j h)]
  {R : Type u} [CommRing R] (g : ∀ i, G i →+* R)
  (hR : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i))
  (i : ι) {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of (G i))) [QuasiCompact fX] [QuasiSeparated fX]

abbrev l12 {κ : Type u} (W : κ → X.Opens) (a b c : κ) : W a ⊓ W b ⊓ W c ≤ W a ⊓ W b :=
  le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)
abbrev l23 {κ : Type u} (W : κ → X.Opens) (a b c : κ) : W a ⊓ W b ⊓ W c ≤ W b ⊓ W c :=
  le_inf (inf_le_left.trans inf_le_right) inf_le_right
abbrev l13 {κ : Type u} (W : κ → X.Opens) (a b c : κ) : W a ⊓ W b ⊓ W c ≤ W a ⊓ W c :=
  le_inf (inf_le_left.trans inf_le_left) inf_le_right

include hR in
theorem main {κ : Type u} [Finite κ] (W : κ → X.Opens) (hW : ∀ k, IsCompact (W k : Set X))
    (hcov : (⨆ k, prR g i fX ⁻¹ᵁ W k) = ⊤)
    (gc : UnitCocycle fun k => prR g i fX ⁻¹ᵁ W k) :
    ∃ (j : ι) (hij : i ≤ j) (cu : ∀ a b, Γ(XS φ i fX j hij, prS φ i fX j hij ⁻¹ᵁ (W a ⊓ W b))),
      (∀ a, cu a a = 1) ∧
      (∀ a b c, GlueOfCocycle.rO (Scheme.Hom.preimage_mono _ (l12 W a b c)) (cu a b) *
          GlueOfCocycle.rO (Scheme.Hom.preimage_mono _ (l23 W a b c)) (cu b c) =
        GlueOfCocycle.rO (Scheme.Hom.preimage_mono _ (l13 W a b c)) (cu a c)) ∧
      (⨆ k, prS φ i fX j hij ⁻¹ᵁ W k) = ⊤ ∧
      ∀ a b, val φ g hR i fX j hij (W a ⊓ W b) (cu a b) =
        (show Γ(XR g i fX, prR g i fX ⁻¹ᵁ (W a ⊓ W b)) from gc.u a b) := by
  classical
  haveI : Fintype κ := Fintype.ofFinite κ
  haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated fX
  have hW2 : ∀ a b, IsCompact ((W a ⊓ W b : X.Opens) : Set X) := fun a b =>
    (hW a).inter_of_isOpen (hW b) (W a).isOpen (W b).isOpen
  have hW3 : ∀ a b c, IsCompact ((W a ⊓ W b ⊓ W c : X.Opens) : Set X) := fun a b c =>
    (hW2 a b).inter_of_isOpen (hW c) (W a ⊓ W b).isOpen (W c).isOpen

  have A : ∀ a b, ∃ (k : ι) (hk : i ≤ k) (t : Γ(XS φ i fX k hk, prS φ i fX k hk ⁻¹ᵁ (W a ⊓ W b))),
      val φ g hR i fX k hk (W a ⊓ W b) t = (show Γ(XR g i fX, prR g i fX ⁻¹ᵁ (W a ⊓ W b)) from gc.u a b) :=
    fun a b => exists_val_eq φ g hR i fX (W a ⊓ W b) (hW2 a b) _
  choose jab hjab t ht using A

  obtain ⟨j₁, hj₁⟩ := Finset.exists_le (insert i (Finset.univ.image fun p : κ × κ => jab p.1 p.2))
  have hij₁ : i ≤ j₁ := hj₁ i (Finset.mem_insert_self _ _)
  have hjab₁ : ∀ a b, jab a b ≤ j₁ := fun a b =>
    hj₁ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem (fun p : κ × κ => jab p.1 p.2) (Finset.mem_univ (a, b))))
  let u : ∀ a b, Γ(XS φ i fX j₁ hij₁, prS φ i fX j₁ hij₁ ⁻¹ᵁ (W a ⊓ W b)) := fun a b =>
    push φ i fX (jab a b) j₁ (hjab a b) (hjab₁ a b) (W a ⊓ W b) (t a b)
  have hu : ∀ a b, val φ g hR i fX j₁ hij₁ (W a ⊓ W b) (u a b) =
      (show Γ(XR g i fX, prR g i fX ⁻¹ᵁ (W a ⊓ W b)) from gc.u a b) := fun a b =>
    (val_push φ g hR i fX (jab a b) j₁ (hjab a b) (hjab₁ a b) (W a ⊓ W b) (t a b)).trans (ht a b)

  have B : ∀ a, ∃ (l : ι) (hl : j₁ ≤ l), push φ i fX j₁ l hij₁ hl (W a ⊓ W a) (u a a) = 1 := by
    intro a
    obtain ⟨l, hl, h⟩ := exists_push_eq φ g hR i fX (W a ⊓ W a) (hW2 a a) j₁ hij₁ (u a a) 1 (by
      rw [hu, map_one]; exact gc.refl a)
    exact ⟨l, hl, by rw [h, map_one]⟩
  choose la hla hB using B

  have C : ∀ a b c, ∃ (l : ι) (hl : j₁ ≤ l),
      push φ i fX j₁ l hij₁ hl (W a ⊓ W b ⊓ W c)
        (GlueOfCocycle.rO (Scheme.Hom.preimage_mono _ (l12 W a b c)) (u a b) *
          GlueOfCocycle.rO (Scheme.Hom.preimage_mono _ (l23 W a b c)) (u b c)) =
      push φ i fX j₁ l hij₁ hl (W a ⊓ W b ⊓ W c)
        (GlueOfCocycle.rO (Scheme.Hom.preimage_mono _ (l13 W a b c)) (u a c)) := by
    intro a b c
    apply exists_push_eq φ g hR i fX (W a ⊓ W b ⊓ W c) (hW3 a b c)
    rw [map_mul, val_rO, val_rO, val_rO, hu, hu, hu]
    · exact gc.cocycle a b c
    all_goals first
      | exact l12 W a b c
      | exact l23 W a b c
      | exact l13 W a b c
  choose labc hlabc hC using C

  obtain ⟨jc, hijc, hcovS⟩ := exists_cover φ g hR i fX W hcov
  obtain ⟨j₂, hj₂⟩ := Finset.exists_le ({j₁, jc} : Finset ι)
  have hj₁₂ : j₁ ≤ j₂ := hj₂ _ (by simp)
  have hjc₂ : jc ≤ j₂ := hj₂ _ (by simp)

  obtain ⟨js, hjs⟩ := Finset.exists_le (insert j₂ ((Finset.univ.image la) ∪ (Finset.univ.image fun p : κ × κ × κ => labc p.1 p.2.1 p.2.2)))
  have hj₂s : j₂ ≤ js := hjs _ (Finset.mem_insert_self _ _)
  have hj₁s : j₁ ≤ js := hj₁₂.trans hj₂s
  have hlas : ∀ a, la a ≤ js := fun a =>
    hjs _ (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem la (Finset.mem_univ a))))
  have hlabcs : ∀ a b c, labc a b c ≤ js := fun a b c =>
    hjs _ (Finset.mem_insert_of_mem (Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun p : κ × κ × κ => labc p.1 p.2.1 p.2.2) (Finset.mem_univ (a, b, c)))))
  let cu : ∀ a b, Γ(XS φ i fX js (hij₁.trans hj₁s), prS φ i fX js (hij₁.trans hj₁s) ⁻¹ᵁ (W a ⊓ W b)) := fun a b =>
    push φ i fX j₁ js hij₁ hj₁s (W a ⊓ W b) (u a b)
  refine ⟨js, hij₁.trans hj₁s, cu, fun a => ?_, fun a b c => ?_, hcovS js (hjc₂.trans hj₂s), fun a b => ?_⟩
  · change push φ i fX j₁ js hij₁ hj₁s (W a ⊓ W a) (u a a) = 1
    rw [← push_push φ i fX j₁ (la a) js hij₁ (hla a) (hlas a), hB a, map_one]
  · change GlueOfCocycle.rO _ (push φ i fX j₁ js hij₁ hj₁s _ (u a b)) * GlueOfCocycle.rO _ (push φ i fX j₁ js hij₁ hj₁s _ (u b c)) =
      GlueOfCocycle.rO _ (push φ i fX j₁ js hij₁ hj₁s _ (u a c))
    rw [← push_rO φ i fX j₁ js hij₁ hj₁s (l12 W a b c), ← push_rO φ i fX j₁ js hij₁ hj₁s (l23 W a b c),
      ← push_rO φ i fX j₁ js hij₁ hj₁s (l13 W a b c), ← map_mul,
      ← push_push φ i fX j₁ (labc a b c) js hij₁ (hlabc a b c) (hlabcs a b c), hC a b c, push_push]
  · exact (val_push φ g hR i fX j₁ js hij₁ hj₁s (W a ⊓ W b) (u a b)).trans (hu a b)

end Main

end AlgebraicGeometry.CocycleFil

end

open AlgebraicGeometry.CocycleFil _root_.AlgebraicGeometry.Scheme.Modules in
theorem solution
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {G : ι → Type u} [∀ i, CommRing (G i)] (φ : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(φ i j h)]
    {R : Type u} [CommRing R] (g : ∀ i, G i →+* R)
    (hR : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i))
    (i : ι) {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of (G i))) [QuasiCompact fX] [QuasiSeparated fX]
    {κ : Type u} [Finite κ] (W : κ → X.Opens) (hW : ∀ k, IsCompact (W k : Set X))
    (hcov : (⨆ k, (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (g i)))) ⁻¹ᵁ W k) = ⊤)
    (gc : Scheme.Modules.UnitCocycle fun k => (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (g i)))) ⁻¹ᵁ W k) :
    ∃ (j : ι) (hij : i ≤ j) (c : Scheme.Modules.UnitCocycle fun k => (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ W k),
      (⨆ k, (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ W k) = ⊤ ∧
      ∀ (cX : Limits.pullback fX (Spec.map (CommRingCat.ofHom (g i))) ⟶ Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j hij)))),
        cX ≫ Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij))) = Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (g i))) →
        cX ≫ Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i j hij))) = Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (g i))) ≫ Spec.map (CommRingCat.ofHom (g j)) →
        ∀ (a b : κ)
          (e : (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (g i)))) ⁻¹ᵁ W a ⊓ (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (g i)))) ⁻¹ᵁ W b =
            cX ⁻¹ᵁ ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ W a) ⊓ cX ⁻¹ᵁ ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ W b)),
          (Limits.pullback fX (Spec.map (CommRingCat.ofHom (g i)))).presheaf.map (eqToHom e).op ((c.comap cX).u a b) = gc.u a b := by
  obtain ⟨j, hij, cu, hrefl, hcoc, hcovj, hval⟩ := AlgebraicGeometry.CocycleFil.main φ g hR i fX W hW hcov gc
  refine ⟨j, hij, { u := fun a b => cu a b, refl := hrefl, cocycle := hcoc }, hcovj, fun cX h1 h2 a b e => ?_⟩
  obtain rfl := AlgebraicGeometry.CocycleFil.cc_unique φ g hR i fX j hij cX h1 h2
  exact hval a b

end S_AlgebraicGeometry_Scheme_Modules_UnitCocycle_exists_comap_eq_of_isDirectLimit
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_UnitCocycle_exists_comap_eq_of_isDirectLimit (solution)
