-- Prove2me | solution 1 for AlgebraicGeometry.TwoGluedCurves.IsNodeUnitModule.tensor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/0f340790-5455-5fc1-9234-fc81a441d78c

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_TwoGluedCurvesNodeUnitModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackTensorObjIso_hom_app_pullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_tensorHom_app_tensorSections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_leftUnitor_hom_app_tensorSections
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_exists_opens_iSup_eq_top_nodeLocus_eq_bot
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_injective_and_range_eq_nodeCondition_of_forall_exists_isFrameOn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_tensor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.TwoGluedCurves Opposite TopologicalSpace"

noncomputable section

namespace TwoGluedCurvesN7

variable {κ : Type u} [Field κ]
  {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (.of κ))
  {c₁ : C₁ ⟶ Spec (.of κ)} {c₂ : C₂ ⟶ Spec (.of κ)}
  (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x)
  {ι : Type v} (p₁ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₁) (p₂ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₂)
  {T : Scheme.{u}} (h : T ⟶ Spec (.of κ))

abbrev P₁ : (pullback x h).Modules :=
  (Scheme.Modules.pushforward (curveChange i₁.1 i₁.2 h)).obj (SheafOfModules.unit (pullback c₁ h).ringCatSheaf)

abbrev P₂ : (pullback x h).Modules :=
  (Scheme.Modules.pushforward (curveChange i₂.1 i₂.2 h)).obj (SheafOfModules.unit (pullback c₂ h).ringCatSheaf)

def toR₁ (W : (pullback x h).Opens) (f : Γ(P₁ x i₁ h, W)) : Γ(pullback c₁ h, (curveChange i₁.1 i₁.2 h) ⁻¹ᵁ W) := f
def ofR₁ (W : (pullback x h).Opens) (f : Γ(pullback c₁ h, (curveChange i₁.1 i₁.2 h) ⁻¹ᵁ W)) : Γ(P₁ x i₁ h, W) := f
def toR₂ (W : (pullback x h).Opens) (g : Γ(P₂ x i₂ h, W)) : Γ(pullback c₂ h, (curveChange i₂.1 i₂.2 h) ⁻¹ᵁ W) := g
def ofR₂ (W : (pullback x h).Opens) (g : Γ(pullback c₂ h, (curveChange i₂.1 i₂.2 h) ⁻¹ᵁ W)) : Γ(P₂ x i₂ h, W) := g
@[scoped simp] lemma toR₁_ofR₁ (W : (pullback x h).Opens) (f) : toR₁ x i₁ h W (ofR₁ x i₁ h W f) = f := rfl
@[scoped simp] lemma ofR₁_toR₁ (W : (pullback x h).Opens) (f) : ofR₁ x i₁ h W (toR₁ x i₁ h W f) = f := rfl
@[scoped simp] lemma toR₂_ofR₂ (W : (pullback x h).Opens) (g) : toR₂ x i₂ h W (ofR₂ x i₂ h W g) = g := rfl
@[scoped simp] lemma ofR₂_toR₂ (W : (pullback x h).Opens) (g) : ofR₂ x i₂ h W (toR₂ x i₂ h W g) = g := rfl
lemma toR₁_injective (W : (pullback x h).Opens) : Function.Injective (toR₁ x i₁ h W) := fun _ _ e => e
lemma toR₂_injective (W : (pullback x h).Opens) : Function.Injective (toR₂ x i₂ h W) := fun _ _ e => e
lemma toR₁_smul (W : (pullback x h).Opens) (r : Γ(pullback x h, W)) (f : Γ(P₁ x i₁ h, W)) :
    toR₁ x i₁ h W (r • f) = (curveChange i₁.1 i₁.2 h).app W r * toR₁ x i₁ h W f := rfl
lemma toR₂_smul (W : (pullback x h).Opens) (r : Γ(pullback x h, W)) (g : Γ(P₂ x i₂ h, W)) :
    toR₂ x i₂ h W (r • g) = (curveChange i₂.1 i₂.2 h).app W r * toR₂ x i₂ h W g := rfl
lemma toR₁_map {W W' : (pullback x h).Opens} (e : W' ⟶ W) (f : Γ(P₁ x i₁ h, W)) :
    toR₁ x i₁ h W' ((P₁ x i₁ h).presheaf.map e.op f) =
      (pullback c₁ h).presheaf.map (homOfLE ((curveChange i₁.1 i₁.2 h).preimage_mono e.le)).op (toR₁ x i₁ h W f) := rfl
lemma toR₂_map {W W' : (pullback x h).Opens} (e : W' ⟶ W) (g : Γ(P₂ x i₂ h, W)) :
    toR₂ x i₂ h W' ((P₂ x i₂ h).presheaf.map e.op g) =
      (pullback c₂ h).presheaf.map (homOfLE ((curveChange i₂.1 i₂.2 h).preimage_mono e.le)).op (toR₂ x i₂ h W g) := rfl

lemma pair_ext {W : (pullback x h).Opens} {p q : Γ(P₁ x i₁ h, W) × Γ(P₂ x i₂ h, W)}
    (h1 : toR₁ x i₁ h W p.1 = toR₁ x i₁ h W q.1) (h2 : toR₂ x i₂ h W p.2 = toR₂ x i₂ h W q.2) : p = q :=
  Prod.ext h1 h2

def nv₁ (j : ι) (W : (pullback x h).Opens) (f : Γ(pullback c₁ h, (curveChange i₁.1 i₁.2 h) ⁻¹ᵁ W)) :
    Γ(T, nodeLocus x i₁ i₂ p₁ p₂ h j W) :=
  (nodeSectionFst p₁ h j).appLE ((curveChange i₁.1 i₁.2 h) ⁻¹ᵁ W) (nodeLocus x i₁ i₂ p₁ p₂ h j W) inf_le_left f

def nv₂ (j : ι) (W : (pullback x h).Opens) (g : Γ(pullback c₂ h, (curveChange i₂.1 i₂.2 h) ⁻¹ᵁ W)) :
    Γ(T, nodeLocus x i₁ i₂ p₁ p₂ h j W) :=
  (nodeSectionSnd p₂ h j).appLE ((curveChange i₂.1 i₂.2 h) ⁻¹ᵁ W) (nodeLocus x i₁ i₂ p₁ p₂ h j W) inf_le_right g

abbrev uOn (u : ι → Γ(T, ⊤)ˣ) (j : ι) (V : T.Opens) : Γ(T, V) := T.presheaf.map (homOfLE le_top).op (u j : Γ(T, ⊤))

lemma nodeCondition_iff (u : ι → Γ(T, ⊤)ˣ) (W : (pullback x h).Opens) (j : ι) (f) (g) :
    NodeCondition x i₁ i₂ p₁ p₂ h u W j f g ↔
      nv₁ x i₁ i₂ p₁ p₂ h j W f = uOn u j _ * nv₂ x i₁ i₂ p₁ p₂ h j W g := Iff.rfl

lemma nodeLocus_mono (j : ι) {W W' : (pullback x h).Opens} (hW : W' ≤ W) :
    nodeLocus x i₁ i₂ p₁ p₂ h j W' ≤ nodeLocus x i₁ i₂ p₁ p₂ h j W :=
  inf_le_inf ((nodeSectionFst p₁ h j).preimage_mono ((curveChange i₁.1 i₁.2 h).preimage_mono hW))
    ((nodeSectionSnd p₂ h j).preimage_mono ((curveChange i₂.1 i₂.2 h).preimage_mono hW))

abbrev ρ {V V' : T.Opens} (hV : V' ≤ V) : Γ(T, V) →+* Γ(T, V') := (T.presheaf.map (homOfLE hV).op).hom

lemma ρ_ρ {V V' V'' : T.Opens} (hV : V' ≤ V) (hV' : V'' ≤ V') (a : Γ(T, V)) :
    ρ hV' (ρ hV a) = ρ (hV'.trans hV) a := by
  change (T.presheaf.map _ ≫ T.presheaf.map _) a = _
  rw [← Functor.map_comp]; rfl

lemma ρ_uOn (u : ι → Γ(T, ⊤)ˣ) (j : ι) {V V' : T.Opens} (hV : V' ≤ V) :
    ρ hV (uOn u j V) = uOn u j V' := ρ_ρ _ _ _

lemma nv₁_res (j : ι) {W W' : (pullback x h).Opens} (hW : W' ≤ W) (f : Γ(pullback c₁ h, (curveChange i₁.1 i₁.2 h) ⁻¹ᵁ W)) :
    nv₁ x i₁ i₂ p₁ p₂ h j W' ((pullback c₁ h).presheaf.map (homOfLE ((curveChange i₁.1 i₁.2 h).preimage_mono hW)).op f) =
      ρ (nodeLocus_mono x i₁ i₂ p₁ p₂ h j hW) (nv₁ x i₁ i₂ p₁ p₂ h j W f) := by
  unfold nv₁
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

lemma nv₂_res (j : ι) {W W' : (pullback x h).Opens} (hW : W' ≤ W) (g : Γ(pullback c₂ h, (curveChange i₂.1 i₂.2 h) ⁻¹ᵁ W)) :
    nv₂ x i₁ i₂ p₁ p₂ h j W' ((pullback c₂ h).presheaf.map (homOfLE ((curveChange i₂.1 i₂.2 h).preimage_mono hW)).op g) =
      ρ (nodeLocus_mono x i₁ i₂ p₁ p₂ h j hW) (nv₂ x i₁ i₂ p₁ p₂ h j W g) := by
  unfold nv₂
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

lemma nv₁_mul_app (j : ι) (hK : nodeSectionFst p₁ h j ≫ curveChange i₁.1 i₁.2 h = nodeSectionSnd p₂ h j ≫ curveChange i₂.1 i₂.2 h)
    (W : (pullback x h).Opens) (r : Γ(pullback x h, W)) (f : Γ(pullback c₁ h, (curveChange i₁.1 i₁.2 h) ⁻¹ᵁ W)) :
    nv₁ x i₁ i₂ p₁ p₂ h j W ((curveChange i₁.1 i₁.2 h).app W r * f) =
      (nodeSectionSnd p₂ h j ≫ curveChange i₂.1 i₂.2 h).appLE W (nodeLocus x i₁ i₂ p₁ p₂ h j W) (by exact inf_le_right) r *
        nv₁ x i₁ i₂ p₁ p₂ h j W f := by
  unfold nv₁
  rw [map_mul]
  congr 1
  have e₁ : (nodeSectionFst p₁ h j).appLE ((curveChange i₁.1 i₁.2 h) ⁻¹ᵁ W)
        (nodeLocus x i₁ i₂ p₁ p₂ h j W) inf_le_left ((curveChange i₁.1 i₁.2 h).app W r) =
      (nodeSectionFst p₁ h j ≫ curveChange i₁.1 i₁.2 h).appLE W
        (nodeLocus x i₁ i₂ p₁ p₂ h j W) (by exact inf_le_left) r := by
    rw [Scheme.Hom.comp_appLE]; rfl
  rw [e₁, Scheme.Hom.appLE, Scheme.Hom.appLE, Scheme.Hom.congr_app hK W, Category.assoc, ← Functor.map_comp]
  rfl

lemma nv₂_mul_app (j : ι) (W : (pullback x h).Opens) (r : Γ(pullback x h, W)) (g : Γ(pullback c₂ h, (curveChange i₂.1 i₂.2 h) ⁻¹ᵁ W)) :
    nv₂ x i₁ i₂ p₁ p₂ h j W ((curveChange i₂.1 i₂.2 h).app W r * g) =
      (nodeSectionSnd p₂ h j ≫ curveChange i₂.1 i₂.2 h).appLE W (nodeLocus x i₁ i₂ p₁ p₂ h j W) (by exact inf_le_right) r *
        nv₂ x i₁ i₂ p₁ p₂ h j W g := by
  unfold nv₂
  rw [map_mul]
  congr 1

theorem nodeSection_comp_eq (hnode : ∀ j, (p₁ j).1 ≫ i₁.1 = (p₂ j).1 ≫ i₂.1) (j : ι) :
    nodeSectionFst p₁ h j ≫ curveChange i₁.1 i₁.2 h = nodeSectionSnd p₂ h j ≫ curveChange i₂.1 i₂.2 h := by
  let ν : SchemeHomOver (𝟙 (Spec (.of κ))) x :=
    ⟨(p₁ j).1 ≫ i₁.1, by rw [Category.assoc, i₁.2, (p₁ j).2]⟩
  have h1 : nodeSectionFst p₁ h j ≫ curveChange i₁.1 i₁.2 h = rigSection x h ν :=
    rigSection_curveChange i₁.1 i₁.2 (ε' := p₁ j) (ε := ν) rfl h
  have h2 : nodeSectionSnd p₂ h j ≫ curveChange i₂.1 i₂.2 h = rigSection x h ν :=
    rigSection_curveChange i₂.1 i₂.2 (ε' := p₂ j) (ε := ν) (hnode j).symm h
  rw [h1, h2]

lemma mem_nodeLocus (hnode : ∀ j, (p₁ j).1 ≫ i₁.1 = (p₂ j).1 ≫ i₂.1) (j : ι) (W : (pullback x h).Opens) (t : T)
    (ht : (nodeSectionFst p₁ h j ≫ curveChange i₁.1 i₁.2 h).base t ∈ W) :
    t ∈ nodeLocus x i₁ i₂ p₁ p₂ h j W := by
  refine ⟨ht, ?_⟩
  show (nodeSectionSnd p₂ h j ≫ curveChange i₂.1 i₂.2 h).base t ∈ W
  rw [← nodeSection_comp_eq x i₁ i₂ p₁ p₂ h hnode j]
  exact ht

end TwoGluedCurvesN7
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_tensor.TwoGluedCurvesN7"

namespace TwoGluedCurvesN7

set_option quotPrecheck false

variable {κ : Type u} [Field κ]
  {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (.of κ))
  {c₁ : C₁ ⟶ Spec (.of κ)} {c₂ : C₂ ⟶ Spec (.of κ)}
  (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x)
  {ι : Type v} (p₁ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₁) (p₂ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₂)
  {T : Scheme.{u}} (h : T ⟶ Spec (.of κ)) (u : ι → Γ(T, ⊤)ˣ)

local notation "nl" => nodeLocus x i₁ i₂ p₁ p₂ h

def uSec (i : ι) (W : (pullback x h).Opens) : Γ(pullback c₁ h, (curveChange i₁.1 i₁.2 h) ⁻¹ᵁ W) :=
  (pullback.snd c₁ h).appLE ⊤ ((curveChange i₁.1 i₁.2 h) ⁻¹ᵁ W) le_top (u i : Γ(T, ⊤))

lemma isUnit_uSec (i : ι) (W : (pullback x h).Opens) : IsUnit (uSec x i₁ h u i W) :=
  (u i).isUnit.map _

lemma nv₁_uSec (i : ι) (W : (pullback x h).Opens) :
    nv₁ x i₁ i₂ p₁ p₂ h i W (uSec x i₁ h u i W) = uOn u i (nl i W) := by
  unfold uSec nv₁
  have hsec : nodeSectionFst p₁ h i ≫ pullback.snd c₁ h = 𝟙 T := by
    unfold nodeSectionFst rigSection; exact pullback.lift_snd _ _ _
  have := Scheme.Hom.appLE_comp_appLE (nodeSectionFst p₁ h i) (pullback.snd c₁ h) ⊤
    ((curveChange i₁.1 i₁.2 h) ⁻¹ᵁ W) (nl i W) le_top inf_le_left
  rw [hsec] at this
  have h2 := ConcreteCategory.congr_hom this (u i : Γ(T, ⊤))
  simp only [CommRingCat.comp_apply] at h2
  rw [h2]
  simp [Scheme.Hom.appLE]

lemma nodeCondition_uSec_one (i : ι) (W : (pullback x h).Opens) :
    NodeCondition x i₁ i₂ p₁ p₂ h u W i (uSec x i₁ h u i W) 1 := by
  rw [nodeCondition_iff, nv₁_uSec]
  unfold nv₂
  rw [map_one, mul_one]

lemma nodeCondition_one_one (i : ι) (W : (pullback x h).Opens) :
    NodeCondition x i₁ i₂ p₁ p₂ h 1 W i 1 1 := by
  rw [nodeCondition_iff]
  unfold nv₁ nv₂ uOn
  rw [map_one, map_one, Pi.one_apply, Units.val_one, map_one, mul_one]

lemma nodeCondition_mul (u' : ι → Γ(T, ⊤)ˣ) (i : ι) (W : (pullback x h).Opens)
    (f f' : Γ(pullback c₁ h, (curveChange i₁.1 i₁.2 h) ⁻¹ᵁ W)) (g g' : Γ(pullback c₂ h, (curveChange i₂.1 i₂.2 h) ⁻¹ᵁ W))
    (hfg : NodeCondition x i₁ i₂ p₁ p₂ h u W i f g) (hfg' : NodeCondition x i₁ i₂ p₁ p₂ h u' W i f' g') :
    NodeCondition x i₁ i₂ p₁ p₂ h (u * u') W i (f * f') (g * g') := by
  rw [nodeCondition_iff] at hfg hfg' ⊢
  unfold nv₁ nv₂ uOn at *
  rw [map_mul, map_mul, hfg, hfg', Pi.mul_apply, Units.val_mul, map_mul]
  ring

variable {M : (pullback x h).Modules} (j₁ : M ⟶ P₁ x i₁ h) (j₂ : M ⟶ P₂ x i₂ h)

lemma map_homOfLE_refl {N : (pullback x h).Modules} {W : (pullback x h).Opens} (m : Γ(N, W)) :
    N.presheaf.map (homOfLE (le_refl W)).op m = m := by
  rw [show (homOfLE (le_refl W)).op = 𝟙 (Opposite.op W) from rfl, CategoryTheory.Functor.map_id]; rfl

theorem isUnit_of_isFrameOn_of_mem_range {W : (pullback x h).Opens} (m₀ : Γ(M, W))
    (hm₀ : Scheme.Modules.IsFrameOn m₀ W)
    (f₀ : Γ(pullback c₁ h, (curveChange i₁.1 i₁.2 h) ⁻¹ᵁ W)) (g₀ : Γ(pullback c₂ h, (curveChange i₂.1 i₂.2 h) ⁻¹ᵁ W))
    (hf₀ : IsUnit f₀) (hg₀ : IsUnit g₀)
    (hmem : (ofR₁ x i₁ h W f₀, ofR₂ x i₂ h W g₀) ∈ Set.range (fun m : Γ(M, W) => (j₁.app W m, j₂.app W m))) :
    IsUnit (toR₁ x i₁ h W (j₁.app W m₀)) ∧ IsUnit (toR₂ x i₂ h W (j₂.app W m₀)) := by
  obtain ⟨m, hm⟩ := hmem
  obtain ⟨g, hg⟩ := (hm₀ le_rfl le_rfl).2 m
  change g • M.presheaf.map (homOfLE (le_refl W)).op m₀ = m at hg
  rw [map_homOfLE_refl] at hg
  have e1 : toR₁ x i₁ h W (j₁.app W m) = f₀ := congrArg (fun p => toR₁ x i₁ h W p.1) hm
  have e2 : toR₂ x i₂ h W (j₂.app W m) = g₀ := congrArg (fun p => toR₂ x i₂ h W p.2) hm
  rw [← hg, Scheme.Modules.Hom.app_smul, toR₁_smul] at e1
  rw [← hg, Scheme.Modules.Hom.app_smul, toR₂_smul] at e2
  exact ⟨isUnit_of_mul_isUnit_right (e1 ▸ hf₀), isUnit_of_mul_isUnit_right (e2 ▸ hg₀)⟩

end TwoGluedCurvesN7
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_tensor.TwoGluedCurvesN7"

namespace TwoGluedCurvesN7

p2m_open "AlgebraicGeometry.Scheme.Modules"

variable {Y Z : Scheme.{u}} (f : Z ⟶ Y) {M M' : Y.Modules}
  (k : M ⟶ (Scheme.Modules.pushforward f).obj (𝟙_ Z.Modules))
  (k' : M' ⟶ (Scheme.Modules.pushforward f).obj (𝟙_ Z.Modules))

def flatOf : (Scheme.Modules.pullback f).obj M ⟶ 𝟙_ Z.Modules :=
  ((pullbackPushforwardAdjunction f).homEquiv M (𝟙_ Z.Modules)).symm k

def tensorJ : M ⊗ M' ⟶ (Scheme.Modules.pushforward f).obj (𝟙_ Z.Modules) :=
  ((pullbackPushforwardAdjunction f).homEquiv (M ⊗ M') (𝟙_ Z.Modules))
    ((pullbackTensorObjIso f M M').hom ≫ (flatOf f k ⊗ₘ flatOf f k') ≫ (λ_ (𝟙_ Z.Modules)).hom)

theorem tensorJ_app_tensorSections {U : Y.Opens} (m : Γ(M, U)) (m' : Γ(M', U)) :
    (show Γ(Z, f ⁻¹ᵁ U) from (tensorJ f k k').app U (tensorSections m m')) =
      (show Γ(Z, f ⁻¹ᵁ U) from k.app U m) * (show Γ(Z, f ⁻¹ᵁ U) from k'.app U m') := by
  have h1 : (tensorJ f k k').app U (tensorSections m m') =
      ((pullbackTensorObjIso f M M').hom ≫ (flatOf f k ⊗ₘ flatOf f k') ≫ (λ_ (𝟙_ Z.Modules)).hom).app (f ⁻¹ᵁ U)
        (pullbackLocalSection f (tensorSections m m')) :=
    (app_pullbackLocalSection f _ (tensorSections m m')).symm
  have h2 : ((pullbackTensorObjIso f M M').hom ≫ (flatOf f k ⊗ₘ flatOf f k') ≫ (λ_ (𝟙_ Z.Modules)).hom).app (f ⁻¹ᵁ U)
        (pullbackLocalSection f (tensorSections m m')) =
      (λ_ (𝟙_ Z.Modules)).hom.app (f ⁻¹ᵁ U) ((flatOf f k ⊗ₘ flatOf f k').app (f ⁻¹ᵁ U)
        ((pullbackTensorObjIso f M M').hom.app (f ⁻¹ᵁ U) (pullbackLocalSection f (tensorSections m m')))) := by
    simp only [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply]
  have h3 : (flatOf f k).app (f ⁻¹ᵁ U) (pullbackLocalSection f m) = k.app U m :=
    homEquiv_symm_app_pullbackLocalSection f k m
  have h4 : (flatOf f k').app (f ⁻¹ᵁ U) (pullbackLocalSection f m') = k'.app U m' :=
    homEquiv_symm_app_pullbackLocalSection f k' m'
  change (tensorJ f k k').app U (tensorSections m m') = _
  rw [h1, h2, pullbackTensorObjIso_hom_app_pullbackLocalSection, tensorHom_app_tensorSections, h3, h4,
    leftUnitor_hom_app_tensorSections]
  rfl

end TwoGluedCurvesN7
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_tensor.TwoGluedCurvesN7"

open TwoGluedCurvesN7 _root_.AlgebraicGeometry.Scheme.Modules in
theorem solution
    (κ : Type u) [Field κ] [IsAlgClosed κ]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (.of κ)) [IsReduced X]
    {c₁ : C₁ ⟶ Spec (.of κ)} {c₂ : C₂ ⟶ Spec (.of κ)}
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x)
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    {ι : Type v} [Finite ι]
    (p₁ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₁) (p₂ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₂)
    (hinj : Function.Injective fun j => (p₁ j).1.base (IsLocalRing.closedPoint κ))
    (hnode : ∀ j, (p₁ j).1 ≫ i₁.1 = (p₂ j).1 ≫ i₂.1)
    (hinter : ∀ (q₁ : C₁) (q₂ : C₂), i₁.1.base q₁ = i₂.1.base q₂ →
      ∃ j, q₁ = (p₁ j).1.base (IsLocalRing.closedPoint κ) ∧ q₂ = (p₂ j).1.base (IsLocalRing.closedPoint κ))
    (hcr : IsReduced (pullback i₁.1 i₂.1))
    {T : Scheme.{u}} {h : T ⟶ Spec (.of κ)} {u u' : ι → Γ(T, ⊤)ˣ} {M M' : (pullback x h).Modules}
    (hM : Scheme.Modules.IsInvertible M) (hu : IsNodeUnitModule x i₁ i₂ p₁ p₂ h u M)
    (hM' : Scheme.Modules.IsInvertible M') (hu' : IsNodeUnitModule x i₁ i₂ p₁ p₂ h u' M') :
    IsNodeUnitModule x i₁ i₂ p₁ p₂ h (u * u') (M ⊗ M') := by
  classical
  obtain ⟨j₁, j₂, hj⟩ := hu
  obtain ⟨j₁', j₂', hj'⟩ := hu'
  obtain ⟨U₀, U, hcov, -, -, -, -, hvac₀, hvac⟩ :=
    exists_opens_iSup_eq_top_nodeLocus_eq_bot κ x i₁ i₂ hjs p₁ p₂ hinj hnode hinter hcr h
  let J₁ : M ⊗ M' ⟶ P₁ x i₁ h := tensorJ (curveChange i₁.1 i₁.2 h) j₁ j₁'
  let J₂ : M ⊗ M' ⟶ P₂ x i₂ h := tensorJ (curveChange i₂.1 i₂.2 h) j₂ j₂'
  refine ⟨J₁, J₂, ?_⟩
  apply injective_and_range_eq_nodeCondition_of_forall_exists_isFrameOn κ x i₁ i₂ hjs p₁ p₂ hinj hnode hinter hcr
    (u * u') J₁ J₂
  intro y

  have htest : ∃ W₁ : (pullback x h).Opens, y ∈ W₁ ∧ ∀ W ≤ W₁,
      (∃ (f₀ : Γ(pullback c₁ h, (curveChange i₁.1 i₁.2 h) ⁻¹ᵁ W)) (g₀ : Γ(pullback c₂ h, (curveChange i₂.1 i₂.2 h) ⁻¹ᵁ W)),
        IsUnit f₀ ∧ IsUnit g₀ ∧ ∀ j, NodeCondition x i₁ i₂ p₁ p₂ h u W j f₀ g₀) ∧
      (∃ (f₀ : Γ(pullback c₁ h, (curveChange i₁.1 i₁.2 h) ⁻¹ᵁ W)) (g₀ : Γ(pullback c₂ h, (curveChange i₂.1 i₂.2 h) ⁻¹ᵁ W)),
        IsUnit f₀ ∧ IsUnit g₀ ∧ ∀ j, NodeCondition x i₁ i₂ p₁ p₂ h u' W j f₀ g₀) := by
    have hy : y ∈ (U₀ ⊔ ⨆ i, U i) := by rw [hcov]; trivial
    rcases Opens.mem_sup.mp hy with hy0 | hyU
    · exact ⟨U₀, hy0, fun W hW =>
        ⟨⟨1, 1, isUnit_one, isUnit_one, fun j => hvac₀ u j W hW 1 1⟩,
         ⟨1, 1, isUnit_one, isUnit_one, fun j => hvac₀ u' j W hW 1 1⟩⟩⟩
    · obtain ⟨i, hyi⟩ := Opens.mem_iSup.mp hyU
      refine ⟨U i, hyi, fun W hW => ⟨⟨uSec x i₁ h u i W, 1, isUnit_uSec x i₁ h u i W, isUnit_one, fun j => ?_⟩,
        ⟨uSec x i₁ h u' i W, 1, isUnit_uSec x i₁ h u' i W, isUnit_one, fun j => ?_⟩⟩⟩
      · by_cases hji : j = i
        · subst hji; exact nodeCondition_uSec_one x i₁ i₂ p₁ p₂ h u j W
        · exact hvac u i j hji W hW _ _
      · by_cases hji : j = i
        · subst hji; exact nodeCondition_uSec_one x i₁ i₂ p₁ p₂ h u' j W
        · exact hvac u' i j hji W hW _ _
  obtain ⟨W₁, hyW₁, hW₁⟩ := htest

  obtain ⟨V, m₀, hyV, hm₀⟩ := hM.exists_isFrameOn y
  obtain ⟨V', m₀', hyV', hm₀'⟩ := hM'.exists_isFrameOn y
  let W : (pullback x h).Opens := W₁ ⊓ (V ⊓ V')
  have hWV : W ≤ V := inf_le_right.trans inf_le_left
  have hWV' : W ≤ V' := inf_le_right.trans inf_le_right
  have hyW : y ∈ W := ⟨hyW₁, hyV, hyV'⟩
  let e₀ : Γ(M, W) := M.presheaf.map (homOfLE hWV).op m₀
  let e₀' : Γ(M', W) := M'.presheaf.map (homOfLE hWV').op m₀'
  have he₀ : IsFrameOn e₀ W := (hm₀.map (homOfLE hWV)).mono hWV
  have he₀' : IsFrameOn e₀' W := (hm₀'.map (homOfLE hWV')).mono hWV'
  obtain ⟨⟨f₀, g₀, hf₀, hg₀, hc⟩, ⟨f₀', g₀', hf₀', hg₀', hc'⟩⟩ := hW₁ W inf_le_left

  have hun := isUnit_of_isFrameOn_of_mem_range x i₁ i₂ h j₁ j₂ e₀ he₀ f₀ g₀ hf₀ hg₀ (by rw [(hj W).2]; exact hc)
  have hun' := isUnit_of_isFrameOn_of_mem_range x i₁ i₂ h j₁' j₂' e₀' he₀' f₀' g₀' hf₀' hg₀' (by rw [(hj' W).2]; exact hc')

  have hnc : ∀ j, NodeCondition x i₁ i₂ p₁ p₂ h u W j (toR₁ x i₁ h W (j₁.app W e₀)) (toR₂ x i₂ h W (j₂.app W e₀)) := by
    have hm : (j₁.app W e₀, j₂.app W e₀) ∈ Set.range (fun m : Γ(M, W) => (j₁.app W m, j₂.app W m)) := ⟨e₀, rfl⟩
    rw [(hj W).2] at hm
    exact hm
  have hnc' : ∀ j, NodeCondition x i₁ i₂ p₁ p₂ h u' W j (toR₁ x i₁ h W (j₁'.app W e₀')) (toR₂ x i₂ h W (j₂'.app W e₀')) := by
    have hm : (j₁'.app W e₀', j₂'.app W e₀') ∈ Set.range (fun m : Γ(M', W) => (j₁'.app W m, j₂'.app W m)) := ⟨e₀', rfl⟩
    rw [(hj' W).2] at hm
    exact hm

  refine ⟨W, tensorSections e₀ e₀',
    toR₁ x i₁ h W (j₁.app W e₀) * toR₁ x i₁ h W (j₁'.app W e₀'),
    toR₂ x i₂ h W (j₂.app W e₀) * toR₂ x i₂ h W (j₂'.app W e₀'),
    hyW, he₀.tensorSections he₀', ?_, ?_, hun.1.mul hun'.1, hun.2.mul hun'.2,
    fun j => nodeCondition_mul x i₁ i₂ p₁ p₂ h u u' j W _ _ _ _ (hnc j) (hnc' j)⟩
  · exact tensorJ_app_tensorSections (curveChange i₁.1 i₁.2 h) j₁ j₁' e₀ e₀'
  · exact tensorJ_app_tensorSections (curveChange i₂.1 i₂.2 h) j₂ j₂' e₀ e₀'

#print axioms solution
end
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_tensor.TwoGluedCurvesN7"

end S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_tensor
end P2MW
export P2MW.S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_tensor (solution)
