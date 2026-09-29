-- Prove2me | solution 1 for AlgebraicGeometry.TwoGluedCurves.exists_isNodeUnitModule_of_pullback_curveChange_iso_unit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/f367c4d8-b701-5b83-b166-e762ec4a7f00

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_TwoGluedCurvesNodeUnitModule
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_injective_and_range_eq_nodeCondition_of_forall_exists_isFrameOn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_TwoGluedCurves_exists_isNodeUnitModule_of_pullback_curveChange_iso_unit
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.TwoGluedCurves Opposite TopologicalSpace

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
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedCurves_exists_isNodeUnitModule_of_pullback_curveChange_iso_unit.TwoGluedCurvesN7"

namespace TwoGluedCurvesN7

p2m_open "AlgebraicGeometry.Scheme.Modules"

variable {Y Z : Scheme.{u}} (f : Z ⟶ Y) (L : Y.Modules)

def jOf (e : (Scheme.Modules.pullback f).obj L ≅ SheafOfModules.unit Z.ringCatSheaf) :
    L ⟶ (Scheme.Modules.pushforward f).obj (SheafOfModules.unit Z.ringCatSheaf) :=
  ((pullbackPushforwardAdjunction f).homEquiv _ _) e.hom

theorem isUnit_of_isFrameOn_unit {V : Z.Opens}
    (v : Γ((SheafOfModules.unit Z.ringCatSheaf : Z.Modules), V)) (hv : Scheme.Modules.IsFrameOn v V) :
    IsUnit (show Γ(Z, V) from v) := by
  have hmap : ∀ w : Γ((SheafOfModules.unit Z.ringCatSheaf : Z.Modules), V),
      (Scheme.Modules.presheaf (SheafOfModules.unit Z.ringCatSheaf : Z.Modules)).map (homOfLE (le_refl V)).op w = w :=
    fun w => by
    rw [show (homOfLE (le_refl V)).op = 𝟙 (Opposite.op V) from rfl, CategoryTheory.Functor.map_id]
    rfl
  obtain ⟨g, hg⟩ := (hv le_rfl le_rfl).2 (show Γ((SheafOfModules.unit Z.ringCatSheaf : Z.Modules), V) from (1 : Γ(Z, V)))
  change g • ((Scheme.Modules.presheaf (SheafOfModules.unit Z.ringCatSheaf : Z.Modules)).map (homOfLE (le_refl V)).op v) =
    (show Γ((SheafOfModules.unit Z.ringCatSheaf : Z.Modules), V) from (1 : Γ(Z, V))) at hg
  rw [hmap] at hg
  have hg' : g * (show Γ(Z, V) from v) = 1 := hg
  exact IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact hg')

theorem isUnit_jOf_app_of_isFrameOn
    (e : (Scheme.Modules.pullback f).obj L ≅ SheafOfModules.unit Z.ringCatSheaf)
    {U : Y.Opens} (s : Γ(L, U)) (hs : Scheme.Modules.IsFrameOn s U) :
    IsUnit (show Γ(Z, f ⁻¹ᵁ U) from (jOf f L e).app U s) := by
  have hframe := (hs.pullbackLocalSection f).map_iso e
  have heq : e.hom.app (f ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection f s) = (jOf f L e).app U s := by
    rw [Scheme.Modules.app_pullbackLocalSection]
    rfl
  rw [heq] at hframe
  exact isUnit_of_isFrameOn_unit _ hframe

end TwoGluedCurvesN7
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedCurves_exists_isNodeUnitModule_of_pullback_curveChange_iso_unit.TwoGluedCurvesN7"

namespace TwoGluedCurvesN7

set_option quotPrecheck false

variable {κ : Type u} [Field κ]
  {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (.of κ))
  {c₁ : C₁ ⟶ Spec (.of κ)} {c₂ : C₂ ⟶ Spec (.of κ)}
  (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x)
  {ι : Type v} (p₁ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₁) (p₂ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₂)
  {T : Scheme.{u}} (h : T ⟶ Spec (.of κ))
  {L : (pullback x h).Modules} (j₁ : L ⟶ P₁ x i₁ h) (j₂ : L ⟶ P₂ x i₂ h)

local notation "nl" => nodeLocus x i₁ i₂ p₁ p₂ h

def aVal (j : ι) (W : (pullback x h).Opens) (e : Γ(L, W)) : Γ(T, nl j W) :=
  nv₁ x i₁ i₂ p₁ p₂ h j W (toR₁ x i₁ h W (j₁.app W e))

def bVal (j : ι) (W : (pullback x h).Opens) (e : Γ(L, W)) : Γ(T, nl j W) :=
  nv₂ x i₁ i₂ p₁ p₂ h j W (toR₂ x i₂ h W (j₂.app W e))

local notation "AV" => aVal x i₁ i₂ p₁ p₂ h j₁
local notation "BV" => bVal x i₁ i₂ p₁ p₂ h j₂

lemma app_map {N N' : (pullback x h).Modules} (φ : N ⟶ N') {W W' : (pullback x h).Opens} (i : W' ⟶ W) (n : Γ(N, W)) :
    φ.app W' (N.presheaf.map i.op n) = N'.presheaf.map i.op (φ.app W n) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality i.op) n

lemma aVal_res (j : ι) {W W' : (pullback x h).Opens} (hW : W' ≤ W) (e : Γ(L, W)) :
    AV j W' (L.presheaf.map (homOfLE hW).op e) = ρ (nodeLocus_mono x i₁ i₂ p₁ p₂ h j hW) (AV j W e) := by
  unfold aVal
  rw [app_map, toR₁_map, nv₁_res x i₁ i₂ p₁ p₂ h j hW]

lemma bVal_res (j : ι) {W W' : (pullback x h).Opens} (hW : W' ≤ W) (e : Γ(L, W)) :
    BV j W' (L.presheaf.map (homOfLE hW).op e) = ρ (nodeLocus_mono x i₁ i₂ p₁ p₂ h j hW) (BV j W e) := by
  unfold bVal
  rw [app_map, toR₂_map, nv₂_res x i₁ i₂ p₁ p₂ h j hW]

lemma aVal_smul (j : ι) (hK : nodeSectionFst p₁ h j ≫ curveChange i₁.1 i₁.2 h = nodeSectionSnd p₂ h j ≫ curveChange i₂.1 i₂.2 h)
    (W : (pullback x h).Opens) (g : Γ(pullback x h, W)) (e : Γ(L, W)) :
    AV j W (g • e) = (nodeSectionSnd p₂ h j ≫ curveChange i₂.1 i₂.2 h).appLE W (nl j W) (by exact inf_le_right) g * AV j W e := by
  unfold aVal
  rw [Scheme.Modules.Hom.app_smul, toR₁_smul, nv₁_mul_app x i₁ i₂ p₁ p₂ h j hK]

lemma bVal_smul (j : ι) (W : (pullback x h).Opens) (g : Γ(pullback x h, W)) (e : Γ(L, W)) :
    BV j W (g • e) = (nodeSectionSnd p₂ h j ≫ curveChange i₂.1 i₂.2 h).appLE W (nl j W) (by exact inf_le_right) g * BV j W e := by
  unfold bVal
  rw [Scheme.Modules.Hom.app_smul, toR₂_smul, nv₂_mul_app]

theorem cross (j : ι) (hK : nodeSectionFst p₁ h j ≫ curveChange i₁.1 i₁.2 h = nodeSectionSnd p₂ h j ≫ curveChange i₂.1 i₂.2 h)
    {U U' : (pullback x h).Opens} (e : Γ(L, U)) (e' : Γ(L, U')) (he : Scheme.Modules.IsFrameOn e U)
    {Zt : T.Opens} (hZ : Zt ≤ nl j U) (hZ' : Zt ≤ nl j U') :
    ρ hZ (AV j U e) * ρ hZ' (BV j U' e') = ρ hZ' (AV j U' e') * ρ hZ (BV j U e) := by

  have hZV : Zt ≤ nl j (U ⊓ U') := fun t ht => ⟨⟨(hZ ht).1, (hZ' ht).1⟩, ⟨(hZ ht).2, (hZ' ht).2⟩⟩
  set eV : Γ(L, U ⊓ U') := L.presheaf.map (homOfLE inf_le_left).op e with heV
  set e'V : Γ(L, U ⊓ U') := L.presheaf.map (homOfLE inf_le_right).op e' with he'V
  obtain ⟨g, hg⟩ := (he inf_le_left inf_le_left).2 e'V
  change g • eV = e'V at hg
  have r1 : ρ hZ (AV j U e) = ρ hZV (AV j (U ⊓ U') eV) := by rw [heV, aVal_res, ρ_ρ]
  have r2 : ρ hZ (BV j U e) = ρ hZV (BV j (U ⊓ U') eV) := by rw [heV, bVal_res, ρ_ρ]
  have r3 : ρ hZ' (AV j U' e') = ρ hZV (AV j (U ⊓ U') e'V) := by rw [he'V, aVal_res, ρ_ρ]
  have r4 : ρ hZ' (BV j U' e') = ρ hZV (BV j (U ⊓ U') e'V) := by rw [he'V, bVal_res, ρ_ρ]
  rw [r1, r2, r3, r4, ← hg, aVal_smul x i₁ i₂ p₁ p₂ h j₁ j hK, bVal_smul, map_mul, map_mul]
  ring

variable (hj : ∀ (U : (pullback x h).Opens) (e : Γ(L, U)), Scheme.Modules.IsFrameOn e U →
    IsUnit (toR₁ x i₁ h U (j₁.app U e)) ∧ IsUnit (toR₂ x i₂ h U (j₂.app U e)))

include hj in

theorem exists_unit (hL : Scheme.Modules.IsInvertible L) (hnode : ∀ j, (p₁ j).1 ≫ i₁.1 = (p₂ j).1 ≫ i₂.1) (j : ι) :
    ∃ uj : Γ(T, ⊤)ˣ, ∀ (W : (pullback x h).Opens) (e : Γ(L, W)), Scheme.Modules.IsFrameOn e W →
      AV j W e = T.presheaf.map (homOfLE le_top).op (uj : Γ(T, ⊤)) * BV j W e := by
  classical
  have hK := nodeSection_comp_eq x i₁ i₂ p₁ p₂ h hnode j

  have hfr : ∀ t : T, ∃ (U : (pullback x h).Opens) (s : Γ(L, U)),
      (nodeSectionFst p₁ h j ≫ curveChange i₁.1 i₁.2 h).base t ∈ U ∧ Scheme.Modules.IsFrameOn s U :=
    fun t => hL.exists_isFrameOn _
  choose U s hyU hs using hfr
  let V : T → T.Opens := fun t => nl j (U t)
  have htV : ∀ t, t ∈ V t := fun t => mem_nodeLocus x i₁ i₂ p₁ p₂ h hnode j (U t) t (hyU t)
  have hcov : (⊤ : T.Opens) ≤ iSup V := fun t _ => Opens.mem_iSup.mpr ⟨t, htV t⟩
  have ha : ∀ t, IsUnit (AV j (U t) (s t)) := fun t => (hj _ _ (hs t)).1.map _
  have hb : ∀ t, IsUnit (BV j (U t) (s t)) := fun t => (hj _ _ (hs t)).2.map _
  let r : ∀ t, Γ(T, V t) := fun t => AV j (U t) (s t) * ↑((hb t).unit⁻¹)
  let r' : ∀ t, Γ(T, V t) := fun t => BV j (U t) (s t) * ↑((ha t).unit⁻¹)

  have key : ∀ (t t' : T) (Zt : T.Opens) (hZ : Zt ≤ V t) (hZ' : Zt ≤ V t'), ρ hZ (r t) = ρ hZ' (r t') := by
    intro t t' Zt hZ hZ'
    have hx := cross x i₁ i₂ p₁ p₂ h j₁ j₂ j hK (s t) (s t') (hs t) hZ hZ'
    have h2 : ρ hZ (BV j (U t) (s t)) * ρ hZ ↑((hb t).unit⁻¹) = 1 := by
      rw [← map_mul, IsUnit.mul_val_inv, map_one]
    have h3 : ρ hZ' (BV j (U t') (s t')) * ρ hZ' ↑((hb t').unit⁻¹) = 1 := by
      rw [← map_mul, IsUnit.mul_val_inv, map_one]
    simp only [r, map_mul]
    linear_combination (ρ hZ ↑((hb t).unit⁻¹)) * (ρ hZ' ↑((hb t').unit⁻¹)) * hx
      - (ρ hZ (AV j (U t) (s t))) * (ρ hZ ↑((hb t).unit⁻¹)) * h3
      + (ρ hZ' (AV j (U t') (s t'))) * (ρ hZ' ↑((hb t').unit⁻¹)) * h2
  have key' : ∀ (t t' : T) (Zt : T.Opens) (hZ : Zt ≤ V t) (hZ' : Zt ≤ V t'), ρ hZ (r' t) = ρ hZ' (r' t') := by
    intro t t' Zt hZ hZ'
    have hx := cross x i₁ i₂ p₁ p₂ h j₁ j₂ j hK (s t) (s t') (hs t) hZ hZ'
    have h2 : ρ hZ (AV j (U t) (s t)) * ρ hZ ↑((ha t).unit⁻¹) = 1 := by
      rw [← map_mul, IsUnit.mul_val_inv, map_one]
    have h3 : ρ hZ' (AV j (U t') (s t')) * ρ hZ' ↑((ha t').unit⁻¹) = 1 := by
      rw [← map_mul, IsUnit.mul_val_inv, map_one]
    simp only [r', map_mul]
    linear_combination (-(ρ hZ ↑((ha t).unit⁻¹)) * (ρ hZ' ↑((ha t').unit⁻¹))) * hx
      - (ρ hZ (BV j (U t) (s t))) * (ρ hZ ↑((ha t).unit⁻¹)) * h3
      + (ρ hZ' (BV j (U t') (s t'))) * (ρ hZ' ↑((ha t').unit⁻¹)) * h2

  obtain ⟨uj, huj, -⟩ := TopCat.Sheaf.existsUnique_gluing' T.sheaf V ⊤ (fun t => homOfLE le_top) hcov r
    (fun t t' => key t t' _ inf_le_left inf_le_right)
  obtain ⟨wj, hwj, -⟩ := TopCat.Sheaf.existsUnique_gluing' T.sheaf V ⊤ (fun t => homOfLE le_top) hcov r'
    (fun t t' => key' t t' _ inf_le_left inf_le_right)
  have huj' : ∀ t, ρ (le_top : V t ≤ ⊤) uj = r t := huj
  have hwj' : ∀ t, ρ (le_top : V t ≤ ⊤) wj = r' t := hwj
  have hmul : uj * wj = 1 := by
    refine TopCat.Sheaf.eq_of_locally_eq' T.sheaf V ⊤ (fun t => homOfLE le_top) hcov _ _ fun t => ?_
    change ρ (le_top : V t ≤ ⊤) (uj * wj) = ρ (le_top : V t ≤ ⊤) 1
    rw [map_mul, map_one, huj', hwj']
    have h1 := (ha t).mul_val_inv
    have h2 := (hb t).mul_val_inv
    simp only [r, r']
    linear_combination (BV j (U t) (s t) * ↑((hb t).unit⁻¹)) * h1 + h2
  have hunit : IsUnit uj := IsUnit.of_mul_eq_one wj hmul
  refine ⟨hunit.unit, fun W e he => ?_⟩
  rw [IsUnit.unit_spec]

  refine TopCat.Sheaf.eq_of_locally_eq' T.sheaf (fun t => nl j W ⊓ V t) (nl j W) (fun t => homOfLE inf_le_left)
    (fun t ht => Opens.mem_iSup.mpr ⟨t, ht, htV t⟩) _ _ fun t => ?_
  change ρ (inf_le_left : nl j W ⊓ V t ≤ nl j W) (AV j W e) =
    ρ (inf_le_left : nl j W ⊓ V t ≤ nl j W) (T.presheaf.map (homOfLE le_top).op uj * BV j W e)
  have hu : ρ (inf_le_left : nl j W ⊓ V t ≤ nl j W) (T.presheaf.map (homOfLE le_top).op uj) =
      ρ (inf_le_right : nl j W ⊓ V t ≤ V t) (r t) := by
    rw [← huj' t, ρ_ρ]
    exact (ρ_ρ _ _ _).symm
  have hx := cross x i₁ i₂ p₁ p₂ h j₁ j₂ j hK e (s t) he (inf_le_left : nl j W ⊓ V t ≤ nl j W) inf_le_right
  have h3 : ρ (inf_le_right : nl j W ⊓ V t ≤ V t) (BV j (U t) (s t)) * ρ inf_le_right ↑((hb t).unit⁻¹) = 1 := by
    rw [← map_mul, IsUnit.mul_val_inv, map_one]
  rw [map_mul, hu]
  simp only [r, map_mul]
  linear_combination (ρ (inf_le_right : nl j W ⊓ V t ≤ V t) ↑((hb t).unit⁻¹)) * hx
    - (ρ (inf_le_left : nl j W ⊓ V t ≤ nl j W) (AV j W e)) * h3

end TwoGluedCurvesN7
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedCurves_exists_isNodeUnitModule_of_pullback_curveChange_iso_unit.TwoGluedCurvesN7"

open TwoGluedCurvesN7 in
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
    {T : Scheme.{u}} (h : T ⟶ Spec (.of κ)) (L : (pullback x h).Modules) (hL : Scheme.Modules.IsInvertible L)
    (h₁ : Nonempty ((Scheme.Modules.pullback (curveChange i₁.1 i₁.2 h)).obj L ≅
      SheafOfModules.unit (pullback c₁ h).ringCatSheaf))
    (h₂ : Nonempty ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 h)).obj L ≅
      SheafOfModules.unit (pullback c₂ h).ringCatSheaf)) :
    ∃ u : ι → Γ(T, ⊤)ˣ, IsNodeUnitModule x i₁ i₂ p₁ p₂ h u L := by
  classical
  let J₁ : L ⟶ P₁ x i₁ h := jOf (curveChange i₁.1 i₁.2 h) L h₁.some
  let J₂ : L ⟶ P₂ x i₂ h := jOf (curveChange i₂.1 i₂.2 h) L h₂.some
  have hj : ∀ (U : (pullback x h).Opens) (e : Γ(L, U)), Scheme.Modules.IsFrameOn e U →
      IsUnit (toR₁ x i₁ h U (J₁.app U e)) ∧ IsUnit (toR₂ x i₂ h U (J₂.app U e)) := fun U e he =>
    ⟨isUnit_jOf_app_of_isFrameOn _ L h₁.some e he, isUnit_jOf_app_of_isFrameOn _ L h₂.some e he⟩
  have hu := fun j => exists_unit x i₁ i₂ p₁ p₂ h J₁ J₂ hj hL hnode j
  choose u hu using hu
  refine ⟨u, J₁, J₂, ?_⟩
  apply injective_and_range_eq_nodeCondition_of_forall_exists_isFrameOn κ x i₁ i₂ hjs p₁ p₂ hinj hnode hinter hcr u J₁ J₂
  intro y
  obtain ⟨W, e, hyW, he⟩ := hL.exists_isFrameOn y
  exact ⟨W, e, toR₁ x i₁ h W (J₁.app W e), toR₂ x i₂ h W (J₂.app W e), hyW, he, rfl, rfl, (hj W e he).1,
    (hj W e he).2, fun j => (nodeCondition_iff x i₁ i₂ p₁ p₂ h u W j _ _).mpr (hu j W e he)⟩

#print axioms solution

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedCurves_exists_isNodeUnitModule_of_pullback_curveChange_iso_unit.TwoGluedCurvesN7"

end S_AlgebraicGeometry_TwoGluedCurves_exists_isNodeUnitModule_of_pullback_curveChange_iso_unit
end P2MW
export P2MW.S_AlgebraicGeometry_TwoGluedCurves_exists_isNodeUnitModule_of_pullback_curveChange_iso_unit (solution)
