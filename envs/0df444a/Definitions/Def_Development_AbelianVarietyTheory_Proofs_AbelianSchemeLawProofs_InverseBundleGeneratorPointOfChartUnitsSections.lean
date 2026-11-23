-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InverseBundleGeneratorPointOfChartUnitsSections
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InverseBundleGeneratorPointOfChartUnitsSections
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:22:40.206805+00:00
-- url     : https://prove2.me/theorems/3b05f668-7e0a-457d-879b-48ec0aeb6f46
-- title:
--   Inverse Bundle Generator Point Of Chart Units Sections
-- statement:
--   Definitions and structural lemmas for Inverse Bundle Generator Point Of Chart Units Sections, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/InverseBundleGeneratorPointOfChartUnitsSections.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_pull_cocycle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
namespace GeneratorFunctor
open Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
noncomputable def pb {Y Z : Scheme.{0}} (f : Z ⟶ Y) (U : Y.Opens) (W : Z.Opens) (h : W ≤ f ⁻¹ᵁ U) :
    Γ(Y, U)ˣ →* Γ(Z, W)ˣ :=
  Units.map (f.appLE U W h).hom.toMonoidHom
theorem pb_val {Y Z : Scheme.{0}} (f : Z ⟶ Y) (U : Y.Opens) (W : Z.Opens) (h : W ≤ f ⁻¹ᵁ U)
    (x : Γ(Y, U)ˣ) : (pb f U W h x).val = (f.appLE U W h).hom x.val := rfl
theorem pb_pb {X Y Z : Scheme.{0}} (g : Z ⟶ Y) (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens)
    (W : Z.Opens) (h : V ≤ f ⁻¹ᵁ U) (h' : W ≤ g ⁻¹ᵁ V) (x : Γ(X, U)ˣ) :
    pb g V W h' (pb f U V h x) = pb (g ≫ f) U W (h'.trans (g.preimage_mono h)) x := by
  ext
  rw [pb_val, pb_val, pb_val, ← Scheme.Hom.appLE_comp_appLE]
  rfl
theorem pb_congr {Y Z : Scheme.{0}} {f f' : Z ⟶ Y} (e : f = f') (U : Y.Opens) (W : Z.Opens)
    (h : W ≤ f ⁻¹ᵁ U) (x : Γ(Y, U)ˣ) : pb f U W h x = pb f' U W (e ▸ h) x := by
  subst e; rfl
theorem res_eq_pb {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)ˣ) :
    res h x = pb (𝟙 X) U V h x := by
  ext
  rw [pb_val, Scheme.Hom.appLE, Scheme.Hom.id_app]
  rfl
theorem pullU_eq_pb {Y Z : Scheme.{0}} (f : Z ⟶ Y) (U : Y.Opens) (x : Γ(Y, U)ˣ) :
    pullU f U x = pb f U _ le_rfl x := by
  ext
  rw [pb_val, ← Scheme.Hom.app_eq_appLE]
  rfl
theorem pb_id {X : Scheme.{0}} {U : X.Opens} (h : U ≤ 𝟙 X ⁻¹ᵁ U) (x : Γ(X, U)ˣ) :
    pb (𝟙 X) U U h x = x := by
  rw [← res_eq_pb le_rfl]
  ext
  change (X.presheaf.map (𝟙 _)).hom _ = _
  rw [CategoryTheory.Functor.map_id]
  rfl
theorem pb_id_comp {Y Z : Scheme.{0}} (f : Z ⟶ Y) (U : Y.Opens) (V W : Z.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (h' : W ≤ 𝟙 Z ⁻¹ᵁ V) (x : Γ(Y, U)ˣ) :
    pb (𝟙 Z) V W h' (pb f U V h x) = pb f U W (le_trans h' h) x := by
  rw [pb_pb]; exact pb_congr (Category.id_comp f) _ _ _ _
theorem pb_comp_id {Y Z : Scheme.{0}} (f : Z ⟶ Y) (U V : Y.Opens) (W : Z.Opens)
    (h : V ≤ 𝟙 Y ⁻¹ᵁ U) (h' : W ≤ f ⁻¹ᵁ V) (x : Γ(Y, U)ˣ) :
    pb f V W h' (pb (𝟙 Y) U V h x) = pb f U W (h'.trans (f.preimage_mono h)) x := by
  rw [pb_pb]; exact pb_congr (Category.comp_id f) _ _ _ _
variable {B : Scheme.{0}} {κ : Type} (N : κ → LB B)
structure Pt (Z : Scheme.{0}) where
  b : Z ⟶ B
  s : ∀ k (i : (N k).ι), Γ(Z, b ⁻¹ᵁ (N k).U i)ˣ
  compat : ∀ k i i' (W : Z.Opens) (h : W ≤ b ⁻¹ᵁ (N k).U i) (h' : W ≤ b ⁻¹ᵁ (N k).U i'),
    pb (𝟙 Z) (b ⁻¹ᵁ (N k).U i') W h' (s k i') =
      pb b ((N k).U i ⊓ (N k).U i') W (le_inf h h') ((N k).g i i') *
        pb (𝟙 Z) (b ⁻¹ᵁ (N k).U i) W h (s k i)
variable {N}
theorem Pt.compat' {Z : Scheme.{0}} (y : Pt N Z) (k) (i i') {T : Scheme.{0}} (a : T ⟶ Z)
    (W : T.Opens) (h : W ≤ a ⁻¹ᵁ y.b ⁻¹ᵁ (N k).U i) (h' : W ≤ a ⁻¹ᵁ y.b ⁻¹ᵁ (N k).U i') :
    pb a _ W h' (y.s k i') =
      pb (a ≫ y.b) ((N k).U i ⊓ (N k).U i') W (le_inf h h') ((N k).g i i') *
        pb a _ W h (y.s k i) := by
  have := congrArg (pb a (y.b ⁻¹ᵁ (N k).U i ⊓ y.b ⁻¹ᵁ (N k).U i') W (le_inf h h'))
    (y.compat k i i' (y.b ⁻¹ᵁ (N k).U i ⊓ y.b ⁻¹ᵁ (N k).U i') inf_le_left inf_le_right)
  rwa [map_mul, pb_comp_id, pb_comp_id, pb_pb] at this
theorem Pt.ext' {Z : Scheme.{0}} {x y : Pt N Z} (hb : x.b = y.b)
    (hs : ∀ k i, x.s k i = pb (𝟙 Z) _ _ (by rw [hb]; exact le_rfl) (y.s k i)) : x = y := by
  obtain ⟨b, s, _⟩ := x
  obtain ⟨b', s', _⟩ := y
  obtain rfl : b = b' := hb
  obtain rfl : s = s' := by
    funext k i
    exact (hs k i).trans (pb_id _ _)
  rfl
noncomputable def Pt.map {Z Z' : Scheme.{0}} (a : Z' ⟶ Z) (y : Pt N Z) : Pt N Z' where
  b := a ≫ y.b
  s k i := pb a _ ((a ≫ y.b) ⁻¹ᵁ (N k).U i) le_rfl (y.s k i)
  compat k i i' W h h' := by
    rw [pb_id_comp, pb_id_comp]
    exact y.compat' k i i' a W h h'
variable (N) in

noncomputable def genFunctor : Scheme.{0}ᵒᵖ ⥤ Type where
  obj Z := Pt N Z.unop
  map a := TypeCat.ofHom (Pt.map a.unop)
  map_id Z := by
    ext y
    exact Pt.ext' (Category.id_comp _) fun k i => rfl
  map_comp a a' := by
    ext y
    refine Pt.ext' (Category.assoc _ _ _) fun k i => ?_
    change pb _ _ _ _ _ = pb _ _ _ _ (pb _ _ _ _ (pb _ _ _ _ _))
    rw [pb_id_comp, pb_pb]
    rfl
noncomputable def Pt.ofChart (hN : ∀ k, (N k).IsLB) {Z : Scheme.{0}} (b : Z ⟶ B)
    (j : ∀ k, (N k).ι) (hb : ∀ k, ⊤ ≤ b ⁻¹ᵁ (N k).U (j k)) (v : κ → Γ(Z, ⊤)ˣ) : Pt N Z where
  b := b
  s k i := pb b _ _ (le_inf (le_top.trans (hb k)) le_rfl) ((N k).g (j k) i) *
    pb (𝟙 Z) ⊤ _ le_top (v k)
  compat k i i' W h h' := by
    have := LB.pull_cocycle (hN k) b (j k) i i' (W := W) (le_inf (le_top.trans (hb k)) h)
      (le_inf h h') (le_inf (le_top.trans (hb k)) h')
    simp only [res_eq_pb, pullU_eq_pb] at this
    rw [pb_id_comp, pb_id_comp, pb_id_comp] at this
    rw [map_mul, map_mul, pb_id_comp, pb_id_comp, pb_id_comp, pb_id_comp, ← this, ← _root_.mul_assoc,
      _root_.mul_comm (pb b ((N k).U i ⊓ (N k).U i') W (le_inf h h') _)]
end GeneratorFunctor
end GlobalTheory


