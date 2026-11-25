-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
-- name    : Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T14:01:00.719699+00:00
-- url     : https://prove2.me/theorems/9e461985-5180-4869-aa55-bac723831466
-- title:
--   Coe Nonzero Locus Canonical Eq Compl Range
-- statement:
--   Definitions and structural lemmas for Coe Nonzero Locus Canonical Eq Compl Range, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_app_of_flat
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_mul
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_mul_right_cancel
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_ne_zero
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_of_isUnit
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_pow
import Theorems.Thm_GlobalTheory_Cartier_comap_le_iff
import Theorems.Thm_GlobalTheory_Cartier_exists_germK_eq_of_stalk
import Theorems.Thm_GlobalTheory_Cartier_isRegularFn_iff_germ
import Theorems.Thm_GlobalTheory_Cartier_isRegularFn_iff_of_isAffineOpen
import Theorems.Thm_GlobalTheory_Cartier_mem_nonzeroLocus_iff
import Theorems.Thm_GlobalTheory_Cartier_mem_ratSecs_iff_stalk
import Theorems.Thm_GlobalTheory_Cartier_resG_self
import Theorems.Thm_ReciprocityTheory_AnForm_R_dsJ_basicOpen
import Theorems.Thm_ReciprocityTheory_AnForm_R_dsK_eq
import Theorems.Thm_ReciprocityTheory_AnForm_R_ds_stalkId_eq_map
import Theorems.Thm_ReciprocityTheory_AnForm_R_mem_dsJ
import Theorems.Thm_ReciprocityTheory_AnForm_R_mem_support_iff_stalkId
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isLB_linComb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace GlobalTheory
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open Cartier
namespace Cartier
variable {X : Scheme.{0}}
def secOnOf {L : LB X} (t : L.Sec) (V : X.Opens) : ∀ i, Γ(X, V ⊓ L.U i) :=
  fun i => resG X inf_le_right (t.f i)
instance nonempty_top [IsIntegral X] : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
end Cartier
structure EffCartierData (X : Scheme.{0}) where

  ι : Type

  U : ι → X.Opens

  f : ∀ i, Γ(X, U i)

  cover : ⨆ i, U i = ⊤

  regular : ∀ i, IsRegularFn (f i)

  assoc : ∀ i j, Associated (resG X (inf_le_left : U i ⊓ U j ≤ U i) (f i))
    (resG X (inf_le_right : U i ⊓ U j ≤ U j) (f j))
namespace EffCartierData
variable {X Y Z : Scheme.{0}}
def principal (a : Γ(X, ⊤)) (ha : IsRegularFn a) : EffCartierData X where
  ι := PUnit
  U _ := ⊤
  f _ := a
  cover := iSup_const
  regular _ := ha
  assoc _ _ := Associated.refl _
theorem isRegularFn_spec {R : Type} [CommRing R] {r : R} (hr : r ∈ nonZeroDivisors R) :
    IsRegularFn (X := Sp R) (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
  refine (isRegularFn_iff_of_isAffineOpen (isAffineOpen_top _)).2 ?_
  refine mem_nonZeroDivisors_iff_right.2 fun t ht => ?_
  have e := congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ht
  rw [map_mul, map_zero, Iso.inv_hom_id_apply] at e
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    (mem_nonZeroDivisors_iff_right.1 hr _ e)
  rwa [Iso.hom_inv_id_apply, map_zero] at this
def ofElement {R : Type} [CommRing R] (r : R) (hr : r ∈ nonZeroDivisors R) :
    EffCartierData (Sp R) :=
  principal _ (isRegularFn_spec hr)
def lineOrigin : EffCartierData (Sp (Polynomial ℤ)) :=
  ofElement Polynomial.X (mem_nonZeroDivisors_of_ne_zero Polynomial.X_ne_zero)
def principalTwist (a : Γ(X, ⊤)) (ha : IsRegularFn a) (u : Γ(X, ⊤)ˣ) : EffCartierData X where
  ι := Bool
  U _ := ⊤
  f b := cond b (u * a) a
  cover := iSup_const
  regular b := by
    cases b
    exacts [ha, (IsRegularFn.of_isUnit u.isUnit).mul ha]
  assoc b c := by
    refine Associated.map _ ?_
    cases b <;> cases c
    exacts [Associated.refl _, associated_unit_mul_right _ _ u.isUnit,
      associated_unit_mul_left _ _ u.isUnit, Associated.refl _]
def zero (X : Scheme.{0}) : EffCartierData X := principal 1 (IsRegularFn.of_isUnit isUnit_one)
variable (D D' : EffCartierData X)
theorem exists_mem (x : X) : ∃ i, x ∈ D.U i :=
  Opens.mem_iSup.1 (D.cover.ge (Set.mem_univ x))
def trans (i j : D.ι) : Γ(X, D.U i ⊓ D.U j)ˣ := (D.assoc i j).symm.choose
theorem trans_spec (i j : D.ι) :
    resG X (inf_le_left : D.U i ⊓ D.U j ≤ D.U i) (D.f i) =
      (D.trans i j : Γ(X, D.U i ⊓ D.U j)) * resG X (inf_le_right : D.U i ⊓ D.U j ≤ D.U j) (D.f j) :=
  ((mul_comm _ _).trans (D.assoc i j).symm.choose_spec).symm
theorem trans_spec_on (i j : D.ι) {W : X.Opens} (hi : W ≤ D.U i) (hj : W ≤ D.U j) :
    resG X hi (D.f i) =
      resG X (le_inf hi hj) (D.trans i j : Γ(X, D.U i ⊓ D.U j)) * resG X hj (D.f j) := by
  have := congrArg (resG X (le_inf hi hj)) (D.trans_spec i j)
  rwa [map_mul, resG_resG, resG_resG] at this
theorem eq_trans_on (i j : D.ι) {W : X.Opens} (hi : W ≤ D.U i) (hj : W ≤ D.U j) {c : Γ(X, W)}
    (hc : resG X hi (D.f i) = c * resG X hj (D.f j)) :
    c = resG X (le_inf hi hj) (D.trans i j : Γ(X, D.U i ⊓ D.U j)) :=
  ((D.regular j).resG hj).mul_right_cancel (hc.symm.trans (D.trans_spec_on i j hi hj))
theorem eq_trans (i j : D.ι) {u : Γ(X, D.U i ⊓ D.U j)ˣ}
    (hu : resG X (inf_le_left : D.U i ⊓ D.U j ≤ D.U i) (D.f i) =
      (u : Γ(X, D.U i ⊓ D.U j)) * resG X (inf_le_right : D.U i ⊓ D.U j ≤ D.U j) (D.f j)) :
    u = D.trans i j :=
  Units.ext (((D.regular j).resG _).mul_right_cancel (hu.symm.trans (D.trans_spec i j)))
def lb : LB X where
  ι := D.ι
  U := D.U
  g := D.trans
theorem isLB_lb : D.lb.IsLB where
  cover := D.cover
  g_self i := Units.ext (D.eq_trans_on i i le_rfl le_rfl (c := 1) (one_mul _).symm).symm
  cocycle i j k := by
    have hi : D.U i ⊓ D.U j ⊓ D.U k ≤ D.U i := inf_le_left.trans inf_le_left
    have hj : D.U i ⊓ D.U j ⊓ D.U k ≤ D.U j := inf_le_left.trans inf_le_right
    have hk : D.U i ⊓ D.U j ⊓ D.U k ≤ D.U k := inf_le_right
    refine Units.ext (D.eq_trans_on i k hi hk ?_)
    rw [D.trans_spec_on i j hi hj, D.trans_spec_on j k hj hk, ← mul_assoc]
    rfl
def canonical : D.lb.Sec where
  f := D.f
  compat := D.trans_spec
@[simp] theorem canonical_f (i : D.ι) : D.canonical.f i = D.f i := rfl
theorem isRegularSec_canonical : IsRegularSec D.canonical := D.regular
theorem associated_germ (i j : D.ι) (x : X) (hi : x ∈ D.U i) (hj : x ∈ D.U j) :
    Associated ((X.presheaf.germ _ x hi).hom (D.f i)) ((X.presheaf.germ _ x hj).hom (D.f j)) := by
  have hm : x ∈ D.U i ⊓ D.U j := ⟨hi, hj⟩
  have := (D.assoc i j).map (X.presheaf.germ _ x hm).hom
  rwa [germ_resG, germ_resG] at this
section LocIdeal
variable {κ : Type} (V : κ → X.Opens) (g : ∀ c, Γ(X, V c)) (hV : ∀ x : X, ∃ c, x ∈ V c)
  (hg : ∀ c c' (x : X) (hx : x ∈ V c) (hx' : x ∈ V c'),
    Associated ((X.presheaf.germ _ x hx).hom (g c)) ((X.presheaf.germ _ x hx').hom (g c')))
include hg in

theorem exists_unit_germ (c c' : κ) (x : X) (hx : x ∈ V c) (hx' : x ∈ V c') :
    ∃ u : (X.presheaf.stalk x)ˣ,
      X.presheaf.germ (V c) x hx (g c) = u * X.presheaf.germ (V c') x hx' (g c') := by
  obtain ⟨u, hu⟩ := (hg c c' x hx hx').symm
  exact ⟨u, hu.symm.trans (mul_comm _ _)⟩
def locIdeal : X.IdealSheafData where
  ideal := dsJ V g
  map_ideal_basicOpen := dsJ_basicOpen hV (exists_unit_germ V g hg)
theorem mem_locIdeal_iff {W : X.affineOpens} {a : Γ(X, W.1)} :
    a ∈ (locIdeal V g hV hg).ideal W ↔ ∀ c x (hx : x ∈ W.1) (hc : x ∈ V c),
      (X.presheaf.germ _ x hc).hom (g c) ∣ (X.presheaf.germ _ x hx).hom a := by
  refine mem_dsJ.trans ⟨fun h c x hx hc => ?_, fun h x hx => ?_⟩
  · have := h x hx
    rw [dsK_eq (exists_unit_germ V g hg) c hc] at this
    exact Ideal.mem_span_singleton.1 this
  · obtain ⟨c, hc⟩ := hV x
    rw [dsK_eq (exists_unit_germ V g hg) c hc]
    exact Ideal.mem_span_singleton.2 (h c x hx hc)
theorem ideal_locIdeal (W : X.affineOpens) (c : κ) (h : W.1 ≤ V c) :
    (locIdeal V g hV hg).ideal W = Ideal.span {resG X h (g c)} := by
  ext a
  rw [mem_locIdeal_iff, W.2.mem_ideal_iff]
  refine ⟨fun H x hx => ?_, fun H c' x hx hc' => ?_⟩
  · rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton, germ_resG]
    exact H c x hx (h hx)
  · have := H x hx
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton, germ_resG] at this
    exact (hg c' c x hc' (h hx)).dvd.trans this
end LocIdeal
def idealSheaf : X.IdealSheafData := locIdeal D.U D.f D.exists_mem D.associated_germ
theorem ideal_idealSheaf (W : X.affineOpens) (i : D.ι) (h : W.1 ≤ D.U i) :
    D.idealSheaf.ideal W = Ideal.span {resG X h (D.f i)} :=
  ideal_locIdeal _ _ _ _ W i h
theorem exists_affine_le {V : X.Opens} {x : X} (hx : x ∈ V) :
    ∃ W : X.affineOpens, x ∈ W.1 ∧ W.1 ≤ V := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
  exact ⟨⟨W, hW⟩, hxW, hWV⟩
theorem stalkId_idealSheaf (i : D.ι) (x : X) (hx : x ∈ D.U i) :
    FinalTheorems.stalkId D.idealSheaf x = Ideal.span {(X.presheaf.germ _ x hx).hom (D.f i)} := by
  obtain ⟨W, hxW, hW⟩ := exists_affine_le hx
  rw [ds_stalkId_eq_map _ W x hxW, D.ideal_idealSheaf W i hW, Ideal.map_span, Set.image_singleton,
    germ_resG]
abbrev zeroScheme : Scheme.{0} := D.idealSheaf.subscheme
abbrev zeroSchemeι : D.zeroScheme ⟶ X := D.idealSheaf.subschemeι
theorem mem_support_iff (i : D.ι) {x : X} (hx : x ∈ D.U i) :
    x ∈ D.idealSheaf.support ↔ x ∉ X.basicOpen (D.f i) := by
  refine (mem_support_iff_stalkId D.idealSheaf x).trans ?_
  rw [D.stalkId_idealSheaf i x hx, Ne, Ideal.span_singleton_eq_top, X.mem_basicOpen _ x hx]
theorem coe_nonzeroLocus_canonical :
    (Out.nonzeroLocus D.canonical : Set X) = (D.idealSheaf.support : Set X)ᶜ := by
  ext x
  obtain ⟨i, hi⟩ := D.exists_mem x
  exact (mem_nonzeroLocus_iff D.canonical i hi).trans
    (not_not.symm.trans (not_congr (D.mem_support_iff i hi)).symm)
theorem dense_nonzeroLocus_canonical : Dense (Out.nonzeroLocus D.canonical : Set X) := by
  refine dense_iff_inter_open.2 fun V hV ⟨x, hx⟩ => ?_
  obtain ⟨i, hi⟩ := D.exists_mem x
  obtain ⟨W, hxW, hW⟩ := exists_affine_le (V := ⟨V, hV⟩ ⊓ D.U i) ⟨hx, hi⟩
  have hWi : W.1 ≤ D.U i := hW.trans inf_le_right
  by_contra hne
  have hbot : X.basicOpen (resG X hWi (D.f i)) = ⊥ := by
    refine eq_bot_iff.2 fun y hy => hne ⟨y, (hW (X.basicOpen_le _ hy)).1, ?_⟩
    have hyW : y ∈ W.1 := X.basicOpen_le _ hy
    refine (mem_nonzeroLocus_iff D.canonical i (hWi hyW)).2 ?_
    rw [X.mem_basicOpen _ y hyW] at hy
    exact (X.mem_basicOpen _ y (hWi hyW)).2 ((congrArg IsUnit (germ_resG hWi y hyW _)).mp hy)
  obtain ⟨n, hn⟩ := (Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact W.2.isCompact _).2 hbot
  have : Nonempty W.1 := ⟨⟨x, hxW⟩⟩
  exact (((D.regular i).resG hWi).pow n).ne_zero hn
def ofSec {L : LB X} (hL : L.IsLB) (s : L.Sec) (hs : IsRegularSec s) : EffCartierData X where
  ι := L.ι
  U := L.U
  f := s.f
  cover := hL.cover
  regular := hs
  assoc i j := (congrArg (Associated · _) (s.compat i j)).mpr
    (associated_unit_mul_left _ _ (L.g i j).isUnit)
def KeepsRegular (φ : Y ⟶ X) : Prop := ∀ i, IsRegularFn ((φ.app (D.U i)).hom (D.f i))
theorem germ_app (φ : Y ⟶ X) {U : X.Opens} (a : Γ(X, U)) (y : Y) (hy : φ y ∈ U) :
    (Y.presheaf.germ (φ ⁻¹ᵁ U) y hy).hom ((φ.app U).hom a) =
      (φ.stalkMap y).hom ((X.presheaf.germ U (φ y) hy).hom a) :=
  (Scheme.Hom.germ_stalkMap_apply φ U y hy a).symm
theorem associated_germ_app (φ : Y ⟶ X) (i j : D.ι) (y : Y) (hi : y ∈ φ ⁻¹ᵁ D.U i)
    (hj : y ∈ φ ⁻¹ᵁ D.U j) :
    Associated ((Y.presheaf.germ _ y hi).hom ((φ.app (D.U i)).hom (D.f i)))
      ((Y.presheaf.germ _ y hj).hom ((φ.app (D.U j)).hom (D.f j))) := by
  rw [germ_app φ _ y hi, germ_app φ _ y hj]
  exact (D.associated_germ i j (φ y) hi hj).map _
theorem comap_idealSheaf (φ : Y ⟶ X) : D.idealSheaf.comap φ =
    locIdeal (fun i => φ ⁻¹ᵁ D.U i) (fun i => (φ.app (D.U i)).hom (D.f i))
      (fun y => D.exists_mem (φ y)) (D.associated_germ_app φ) := by
  apply le_antisymm
  · refine (comap_le_iff _ _ _).2 fun U a ha W h => (mem_locIdeal_iff _ _ _ _).2
      fun i y hy hi => ?_
    rw [germ_resG, germ_app φ _ y hi, germ_app φ a y (h hy)]
    exact map_dvd _ ((mem_locIdeal_iff _ _ _ _).1 ha i (φ y) (h hy) hi)
  · have loc : ∀ y : Y, ∃ (W : Y.affineOpens) (U : X.affineOpens) (i : D.ι),
        y ∈ W.1 ∧ W.1 ≤ φ ⁻¹ᵁ U.1 ∧ U.1 ≤ D.U i := fun y => by
      obtain ⟨i, hi⟩ := D.exists_mem (φ y)
      obtain ⟨U, hyU, hU⟩ := exists_affine_le hi
      obtain ⟨W, hyW, hW⟩ := exists_affine_le (V := φ ⁻¹ᵁ U.1) (x := y) hyU
      exact ⟨W, U, i, hyW, hW, hU⟩
    choose W U i hy hW hU using loc
    refine Scheme.IdealSheafData.le_of_iSup_eq_top W
      (eq_top_iff.2 fun y _ => Opens.mem_iSup.2 ⟨y, hy y⟩) fun y => ?_
    refine (ideal_locIdeal (fun i => φ ⁻¹ᵁ D.U i) _ _ _ (W y) (i y)
      ((hW y).trans (φ.preimage_mono (hU y)))).trans_le ?_
    rw [Ideal.span_singleton_le_iff_mem]
    have := (comap_le_iff D.idealSheaf φ _).1 le_rfl (U y) (resG X (hU y) (D.f (i y)))
      (by rw [D.ideal_idealSheaf (U y) (i y) (hU y)]; exact Ideal.mem_span_singleton_self _)
      (W y) (hW y)
    rwa [app_resG, resG_resG] at this
theorem keepsRegular_of_flat (φ : Y ⟶ X) [Flat φ] : D.KeepsRegular φ :=
  fun i => (D.regular i).app_of_flat φ
def pull (φ : Y ⟶ X) (h : D.KeepsRegular φ) : EffCartierData Y where
  ι := D.ι
  U i := φ ⁻¹ᵁ D.U i
  f i := (φ.app (D.U i)).hom (D.f i)
  cover := eq_top_iff.2 fun y _ => Opens.mem_iSup.2 (D.exists_mem (φ y))
  regular := h
  assoc i j := by
    have := (D.assoc i j).map (φ.app (D.U i ⊓ D.U j)).hom
    rw [app_resG, app_resG] at this
    exact this
theorem idealSheaf_pull (φ : Y ⟶ X) (h : D.KeepsRegular φ) :
    (D.pull φ h).idealSheaf = D.idealSheaf.comap φ :=
  (D.comap_idealSheaf φ).symm
theorem keepsRegular_comp_iff (φ : Y ⟶ X) (h : D.KeepsRegular φ) (ψ : Z ⟶ Y) :
    D.KeepsRegular (ψ ≫ φ) ↔ (D.pull φ h).KeepsRegular ψ := Iff.rfl
def add : EffCartierData X where
  ι := D.ι × D'.ι
  U p := D.U p.1 ⊓ D'.U p.2
  f p := resG X inf_le_left (D.f p.1) * resG X inf_le_right (D'.f p.2)
  cover := eq_top_iff.2 fun x _ => by
    obtain ⟨i, hi⟩ := D.exists_mem x
    obtain ⟨j, hj⟩ := D'.exists_mem x
    exact Opens.mem_iSup.2 ⟨(i, j), hi, hj⟩
  regular p := ((D.regular p.1).resG _).mul ((D'.regular p.2).resG _)
  assoc p q := by
    have h₁ := (D.assoc p.1 q.1).map (resG X (le_inf (inf_le_left.trans inf_le_left)
      (inf_le_right.trans inf_le_left) :
        D.U p.1 ⊓ D'.U p.2 ⊓ (D.U q.1 ⊓ D'.U q.2) ≤ D.U p.1 ⊓ D.U q.1))
    have h₂ := (D'.assoc p.2 q.2).map (resG X (le_inf (inf_le_left.trans inf_le_right)
      (inf_le_right.trans inf_le_right) :
        D.U p.1 ⊓ D'.U p.2 ⊓ (D.U q.1 ⊓ D'.U q.2) ≤ D'.U p.2 ⊓ D'.U q.2))
    rw [resG_resG, resG_resG] at h₁ h₂
    rw [map_mul, map_mul, resG_resG, resG_resG, resG_resG, resG_resG]
    exact h₁.mul_mul h₂
def addGen : LB.Gen (LB.div (LB.div (D.add D').lb D.lb) D'.lb) where
  s := fun p : ((D.ι × D'.ι) × D.ι) × D'.ι =>
    (res (le_inf (inf_le_left.trans (inf_le_left.trans inf_le_left))
        (inf_le_left.trans inf_le_right)) (D.trans p.1.1.1 p.1.2) *
      res (le_inf (inf_le_left.trans (inf_le_left.trans inf_le_right)) inf_le_right)
        (D'.trans p.1.1.2 p.2) : Γ(X, D.U p.1.1.1 ⊓ D'.U p.1.1.2 ⊓ D.U p.1.2 ⊓ D'.U p.2)ˣ)
theorem app_add_f (φ : Y ⟶ X) (p : D.ι × D'.ι) :
    (φ.app ((D.add D').U p)).hom ((D.add D').f p) =
      resG Y (φ.preimage_mono inf_le_left) ((φ.app (D.U p.1)).hom (D.f p.1)) *
        resG Y (φ.preimage_mono inf_le_right) ((φ.app (D'.U p.2)).hom (D'.f p.2)) :=
  (map_mul (φ.app (D.U p.1 ⊓ D'.U p.2)).hom _ _).trans
    (congrArg₂ (· * ·) (app_resG φ _ _) (app_resG φ _ _))
theorem KeepsRegular.add {D D' : EffCartierData X} {φ : Y ⟶ X} (h : D.KeepsRegular φ)
    (h' : D'.KeepsRegular φ) : (D.add D').KeepsRegular φ := fun p =>
  (congrArg IsRegularFn (D.app_add_f D' φ p)).mpr (((h p.1).resG _).mul ((h' p.2).resG _))
def nsmul (n : ℕ) : EffCartierData X where
  ι := D.ι
  U := D.U
  f i := D.f i ^ n
  cover := D.cover
  regular i := (D.regular i).pow n
  assoc i j := by
    rw [map_pow, map_pow]
    exact (D.assoc i j).pow_pow
section Rational
variable [IsIntegral X]
def poleSecs (n : ℕ) (V : X.Opens) [Nonempty V] : Submodule Γ(X, V) X.functionField :=
  ratSecs (D.nsmul n).canonical V
theorem mem_poleSecs_iff_stalk (n : ℕ) (V : X.Opens) [Nonempty V] (h : X.functionField) :
    h ∈ D.poleSecs n V ↔ ∀ (i : D.ι) (x : X) (_ : x ∈ V) (hx : x ∈ D.U i),
      algebraMap (X.presheaf.stalk x) X.functionField ((X.presheaf.germ _ x hx).hom (D.f i)) ^ n *
        h ∈ Set.range (algebraMap (X.presheaf.stalk x) X.functionField) := by
  refine (mem_ratSecs_iff_stalk _ V h).trans (forall₄_congr fun i x _ hx => iff_of_eq
    (congrArg (fun r => r * h ∈ Set.range (algebraMap (X.presheaf.stalk x) X.functionField)) ?_))
  exact (congrArg _ (map_pow (X.presheaf.germ _ x hx).hom (D.f i) n)).trans (map_pow _ _ n)
theorem mem_poleSecs_zero_iff (V : X.Opens) [Nonempty V] (h : X.functionField) :
    h ∈ D.poleSecs 0 V ↔ ∃ a : Γ(X, V), (X.germToFunctionField V).hom a = h := by
  rw [mem_poleSecs_iff_stalk]
  constructor
  · intro H
    refine exists_germK_eq_of_stalk V h fun x hx => ?_
    obtain ⟨i, hi⟩ := D.exists_mem x
    simpa using H i x hx hi
  · rintro ⟨a, rfl⟩ i x hx hi
    rw [pow_zero, one_mul]
    exact ⟨_, Scheme.algebraMap_germ_eq_germToFunctionField X hx a⟩
theorem isLB_lbPow {X : Scheme.{0}} (D : EffCartierData X) (n : ℕ) : (lbPow D.lb n).IsLB :=
  LB.isLB_linComb D.isLB_lb _ _
theorem mem_poleSecs_principal_iff (a : Γ(X, ⊤)) (ha : IsRegularFn a) (n : ℕ) (V : X.Opens)
    [Nonempty V] (h : X.functionField) :
    h ∈ (principal a ha).poleSecs n V ↔ ∃ b : Γ(X, V), (X.germToFunctionField V).hom b =
      (X.germToFunctionField V).hom (resG X le_top a) ^ n * h := by
  have e : ∀ x (hx : x ∈ V), algebraMap (X.presheaf.stalk x) X.functionField
      ((X.presheaf.germ ⊤ x trivial).hom a) = (X.germToFunctionField V).hom (resG X le_top a) :=
    fun x hx => (congrArg _ (germ_resG le_top x hx a).symm).trans
      (Scheme.algebraMap_germ_eq_germToFunctionField X hx _)
  rw [mem_poleSecs_iff_stalk]
  constructor
  · intro H
    refine exists_germK_eq_of_stalk V _ fun x hx => ?_
    rw [← e x hx]
    exact H ⟨⟩ x hx trivial
  · rintro ⟨b, hb⟩ i x hx hi
    refine ⟨_, (Scheme.algebraMap_germ_eq_germToFunctionField X hx b).trans (hb.trans ?_)⟩
    rw [← e x hx]
    rfl
end Rational
theorem mem_support_ofElement_iff {R : Type} [CommRing R] (r : R) (hr : r ∈ nonZeroDivisors R)
    (p : PrimeSpectrum R) :
    (p : Sp R) ∈ (ofElement r hr).idealSheaf.support ↔ r ∈ p.asIdeal := by
  refine ((ofElement r hr).mem_support_iff ⟨⟩ (x := p) trivial).trans ?_
  have e := basicOpen_eq_of_affine (R := CommRingCat.of R) r
  exact (not_congr (iff_of_eq (congrArg (fun W => (p : Sp R) ∈ W) e))).trans not_not
example : (⟨Ideal.span {Polynomial.X}, (Ideal.span_singleton_prime Polynomial.X_ne_zero).2
    Polynomial.prime_X⟩ : PrimeSpectrum (Polynomial ℤ)) ∈ lineOrigin.idealSheaf.support :=
  (mem_support_ofElement_iff _ _ _).2 (Ideal.mem_span_singleton_self _)
example : (⊥ : PrimeSpectrum (Polynomial ℤ)) ∉ lineOrigin.idealSheaf.support :=
  fun h => Polynomial.X_ne_zero ((mem_support_ofElement_iff _ _ _).1 h)
example (a : Γ(X, ⊤)) (ha : IsRegularFn a) (u : Γ(X, ⊤)ˣ) :
    (principalTwist a ha u).lb.g true false = res (inf_le_left : (⊤ : X.Opens) ⊓ ⊤ ≤ ⊤) u :=
  ((principalTwist a ha u).eq_trans true false (map_mul (resG X _) _ _)).symm
example (t : (Sp (Polynomial ℤ)).functionField)
    (ht : t = ((Sp (Polynomial ℤ)).germToFunctionField ⊤).hom
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℤ))).inv.hom Polynomial.X)) :
    t⁻¹ ∈ lineOrigin.poleSecs 1 ⊤ ∧ t⁻¹ ∉ lineOrigin.poleSecs 0 ⊤ := by
  have h0 : t ≠ 0 := ht ▸ nonZeroDivisors.ne_zero
    (isRegularFn_iff_germ.1 (lineOrigin.regular ⟨⟩) _ trivial)
  have hh : t * t⁻¹ = 1 := mul_inv_cancel₀ h0
  constructor
  · refine (mem_poleSecs_principal_iff _ _ 1 ⊤ _).2 ⟨1, ?_⟩
    rw [map_one, pow_one, resG_self, ← ht, hh]
  · intro H
    obtain ⟨b, hb⟩ := (mem_poleSecs_zero_iff _ ⊤ _).1 H
    rw [← hb, ht, ← map_mul, ← map_one ((Sp (Polynomial ℤ)).germToFunctionField ⊤).hom] at hh
    have e := congrArg (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℤ))).hom.hom
      ((Sp (Polynomial ℤ)).germToFunctionField_injective ⊤ hh)
    rw [map_mul, map_one, Iso.inv_hom_id_apply] at e
    exact Polynomial.not_isUnit_X (IsUnit.of_mul_eq_one _ e)
example : ¬ lineOrigin.KeepsRegular (spMap (Polynomial.evalRingHom (0 : ℤ))) := fun h => by
  have hd := (lineOrigin.pull _ h).dense_nonzeroLocus_canonical
  have : Nonempty (Sp ℤ) := ⟨(⊥ : PrimeSpectrum ℤ)⟩
  obtain ⟨p, hp⟩ := hd.nonempty
  rw [coe_nonzeroLocus_canonical, idealSheaf_pull, Scheme.IdealSheafData.support_comap] at hp
  refine hp ((mem_support_ofElement_iff _ _ _).2 ?_)
  change Polynomial.evalRingHom (0 : ℤ) Polynomial.X ∈ PrimeSpectrum.asIdeal p
  simp
end EffCartierData
end GlobalTheory


