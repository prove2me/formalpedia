-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:29:47.664213+00:00
-- url     : https://prove2.me/theorems/c708be2e-2617-40e0-b6da-25223689eaba
-- title:
--   Val Calc
-- statement:
--   Definitions and structural lemmas for Val Calc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ValCalc.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Y' Z : Scheme.{0}}
open Classical in

def gs (f : Y ⟶ X) (y : Y) (U : X.Opens) (a : Γ(X, U)) : Y.presheaf.stalk y :=
  if h : f y ∈ U then (Y.presheaf.germ (f ⁻¹ᵁ U) y h).hom ((f.app U).hom a) else 0
theorem gs_eq (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) :
    gs f y U a = (Y.presheaf.germ (f ⁻¹ᵁ U) y h).hom ((f.app U).hom a) := by
  unfold gs
  exact dif_pos h
theorem gs_unit (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)ˣ) : gs f y U a.val = (gm f y U a).val := by
  rw [gs_eq f y U h]
  unfold gm
  rw [dif_pos h]
  rfl
theorem gs_mul (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a b : Γ(X, U)) :
    gs f y U (a * b) = gs f y U a * gs f y U b := by
  simp only [gs_eq f y U h, map_mul]
theorem gs_res (f : Y ⟶ X) (y : Y) {U V : X.Opens} (hle : V ≤ U) (h : f y ∈ V) (a : Γ(X, U)) :
    gs f y V ((X.presheaf.map (homOfLE hle).op).hom a) = gs f y U a := by
  rw [gs_eq f y V h, gs_eq f y U (hle h)]
  first
  | (rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply,
      Scheme.Hom.naturality_assoc]
     first
     | (erw [TopCat.Presheaf.germ_res]; done)
     | (simp only [TopCat.Presheaf.germ_res]; done))
  | (rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
      Scheme.Hom.naturality_assoc]
     erw [TopCat.Presheaf.germ_res])
theorem gs_pull (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (f z) ∈ U) (a : Γ(X, U)) :
    gs f z (g ⁻¹ᵁ U) ((g.app U).hom a) = gs (f ≫ g) z U a := by
  have h' : (f ≫ g) z ∈ U := h
  rw [gs_eq f z (g ⁻¹ᵁ U) h, gs_eq (f ≫ g) z U h']
  simp only [Scheme.Hom.comp_app, CommRingCat.comp_apply]
  try rfl
theorem fn_ext {V : X.Opens} {a b : Γ(X, V)} (h : ∀ x ∈ V, gs (𝟙 X) x V a = gs (𝟙 X) x V b) : a = b := by
  apply TopCat.Presheaf.section_ext X.sheaf V a b
  intro x hx
  have e := h x hx
  rw [gs_eq (𝟙 X) x V hx, gs_eq (𝟙 X) x V hx] at e
  exact e
variable (L : LB X)
def Good (z : Z) (J : (Z ⟶ X) → L.ι) : Prop := ∀ ψ : Z ⟶ X, ψ z ∈ L.U (J ψ)
variable {L} {K K' : Type} [Fintype K] [Fintype K']
theorem Good.mem {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (φ : K → (Y ⟶ X)) (r : Z ⟶ Y) :
    r z ∈ LB.wchart L φ (fun k => J (r ≫ φ k)) := Set.mem_iInter.2 fun k => hJ (r ≫ φ k)
def val {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    (Z.presheaf.stalk z)ˣ := gm r z (LB.wchart L φ (fun k => J (r ≫ φ k))) (t.s (fun k => J (r ≫ φ k)))
def sval {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    Z.presheaf.stalk z := gs r z (LB.wchart L φ (fun k => J (r ≫ φ k))) (s.f (fun k => J (r ≫ φ k)))
section
variable {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
include hJ
theorem val_mul (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) (r : Z ⟶ Y) :
    val (LB.mulGen L φ ε φ' ε' t t') r z J = val t r z J * val t' r z J := by
  simp only [val, LB.mulGen, map_mul]
  congr 1
  · exact gm_res r z _ (hJ.mem (Sum.elim φ φ') r) _
  · exact gm_res r z _ (hJ.mem (Sum.elim φ φ') r) _
end
def trF (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z) (j j' : K → L.ι) : (Z.presheaf.stalk z)ˣ :=
  ∏ k, gm (r ≫ φ k) z (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)) ^ ε k
theorem gen_trans {φ : K → (Y ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) (r : Z ⟶ Y) (z : Z)
    {j j' : K → L.ι} (hj : r z ∈ LB.wchart L φ j) (hj' : r z ∈ LB.wchart L φ j') :
    gm r z (LB.wchart L φ j) (t.s j) = trF φ ε r z j j' * gm r z (LB.wchart L φ j') (t.s j') := by
  have hm : r z ∈ LB.wchart L φ j ⊓ LB.wchart L φ j' := ⟨hj, hj'⟩
  have e := congrArg (gm r z (LB.wchart L φ j ⊓ LB.wchart L φ j')) (ht j j')
  have e1 : gm r z (LB.wchart L φ j ⊓ LB.wchart L φ j') ((LB.LinComb L φ ε).g j j') = trF φ ε r z j j' :=
    gm_linComb L φ ε r z j j' hj hj'
  exact (gm_res r z inf_le_left hm _).symm.trans
    (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) e1 (gm_res r z inf_le_right hm _))))
theorem sec_trans {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z)
    {j j' : K → L.ι} (hj : r z ∈ LB.wchart L φ j) (hj' : r z ∈ LB.wchart L φ j') :
    gs r z (LB.wchart L φ j) (s.f j) = (trF φ ε r z j j').val * gs r z (LB.wchart L φ j') (s.f j') := by
  have hm : r z ∈ LB.wchart L φ j ⊓ LB.wchart L φ j' := ⟨hj, hj'⟩
  have e := congrArg (gs r z (LB.wchart L φ j ⊓ LB.wchart L φ j')) (s.compat j j')
  have e1 := (gs_unit r z _ hm ((LB.LinComb L φ ε).g j j')).trans
    (congrArg Units.val (gm_linComb L φ ε r z j j' hj hj'))
  exact (gs_res r z inf_le_left hm _).symm.trans
    (e.trans ((gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·) e1 (gs_res r z inf_le_right hm _))))
def FormEq (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) : Prop :=
  ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = ∏ k, h (φ' k) ^ ε' k
theorem FormEq.trF {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (h : FormEq φ ε φ' ε') (r : Z ⟶ Y)
    (z : Z) (I I' : (Y ⟶ X) → L.ι) :
    trF φ ε r z (fun k => I (φ k)) (fun k => I' (φ k)) = trF φ' ε' r z (fun k => I (φ' k)) (fun k => I' (φ' k)) := h _ fun ψ => gm (r ≫ ψ) z (L.U (I ψ) ⊓ L.U (I' ψ)) (L.g (I ψ) (I' ψ))
def genSec {M : LB Y} (t : LB.Gen M) (ht : t.IsGen) : LB.Sec M := ⟨fun i => (t.s i).val, fun i j => congrArg Units.val (ht i j)⟩
def pullMulSec {K₃ : Type} [Fintype K₃] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y)
    {φ₃ : K₃ → (Y' ⟶ X)} {ε₃ : K₃ → ℤ} (u : LB.Gen (LB.LinComb L φ₃ ε₃)) (hu : u.IsGen) :
    LB.Sec (LB.LinComb L (Sum.elim (fun k => h ≫ φ k) φ₃) (Sum.elim ε ε₃)) :=
  have l₁ : ∀ j : K ⊕ K₃ → L.ι, LB.wchart L (Sum.elim (fun k => h ≫ φ k) φ₃) j ≤ h ⁻¹ᵁ LB.wchart L φ (j ∘ Sum.inl) :=
    fun _ _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k)
  have l₂ : ∀ j : K ⊕ K₃ → L.ι, LB.wchart L (Sum.elim (fun k => h ≫ φ k) φ₃) j ≤ LB.wchart L φ₃ (j ∘ Sum.inr) :=
    fun _ _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)
  { f := fun j => (Y'.presheaf.map (homOfLE (l₁ j)).op).hom ((h.app _).hom (s.f (j ∘ Sum.inl))) *
      (Y'.presheaf.map (homOfLE (l₂ j)).op).hom (u.s (j ∘ Sum.inr)).val
    compat := fun (j j' : K ⊕ K₃ → L.ι) => fn_ext fun y hy => by
      have v : ∀ j : K ⊕ K₃ → L.ι, y ∈ LB.wchart L (Sum.elim (fun k => h ≫ φ k) φ₃) j →
          gs (𝟙 Y') y _ ((Y'.presheaf.map (homOfLE (l₁ j)).op).hom ((h.app _).hom (s.f (j ∘ Sum.inl))) *
            (Y'.presheaf.map (homOfLE (l₂ j)).op).hom (u.s (j ∘ Sum.inr)).val) =
          gs (𝟙 Y' ≫ h) y (LB.wchart L φ (j ∘ Sum.inl)) (s.f (j ∘ Sum.inl)) *
            (gm (𝟙 Y') y (LB.wchart L φ₃ (j ∘ Sum.inr)) (u.s (j ∘ Sum.inr))).val := fun j hj =>
        (gs_mul _ y _ hj _ _).trans (congrArg₂ (· * ·) ((gs_res _ y _ hj _).trans (gs_pull _ h y _ (l₁ j hj) _))
          ((gs_res _ y _ hj _).trans (gs_unit _ y _ (l₂ j hj) _)))
      refine ((gs_res (𝟙 Y') y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y') y _ hy _ _).trans
        (congrArg₂ (· * ·) ((gs_unit (𝟙 Y') y _ hy _).trans
          (congrArg Units.val (gm_linComb L _ _ (𝟙 Y') y j j' hy.1 hy.2))) ((gs_res (𝟙 Y') y _ hy _).trans (v j' hy.2)))).symm)
      rw [sec_trans s (𝟙 Y' ≫ h) y (l₁ j hy.1) (l₁ j' hy.2), gen_trans hu (𝟙 Y') y (l₂ j hy.1) (l₂ j' hy.2),
        Fintype.prod_sum_type, Units.val_mul, Units.val_mul, mul_mul_mul_comm]
      simp only [trF, Category.assoc, Sum.elim_inl, Sum.elim_inr, Function.comp_apply] }
end ReciprocityTheory.ChartRestriction.G.Geo.Tor


