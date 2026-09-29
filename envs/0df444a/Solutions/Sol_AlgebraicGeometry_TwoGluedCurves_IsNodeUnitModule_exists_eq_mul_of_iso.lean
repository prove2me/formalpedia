-- Prove2me | solution 1 for AlgebraicGeometry.TwoGluedCurves.IsNodeUnitModule.exists_eq_mul_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/0e8c5810-88cd-5dbf-a40c-1cd484dd18e9

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_TwoGluedCurvesNodeUnitModule
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_isNodeUnitModule_one_unit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_bijective_algebraMap_appTop_of_isProper_of_isIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_exists_eq_mul_of_iso
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.TwoGluedCurves Opposite TopologicalSpace

noncomputable section

namespace TwoGluedCurvesFrameAux

abbrev unitMod (Y : Scheme.{u}) : Y.Modules := SheafOfModules.unit Y.ringCatSheaf

variable {X : Scheme.{u}} {M : X.Modules} {U : X.Opens} (m₀ : Γ(M, U))

def resFrame (W : U.toScheme.Opens) : Γ(M, U.ι ''ᵁ W) :=
  M.presheaf.map (homOfLE (U.ι_image_le W)).op m₀

lemma resFrame_map {W W' : U.toScheme.Opens} (i : W' ⟶ W) :
    M.presheaf.map (U.ι.opensFunctor.map i).op (resFrame m₀ W) = resFrame m₀ W' := by
  unfold resFrame
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

def mulFrame (W : U.toScheme.Opens) (g : Γ(X, U.ι ''ᵁ W)) : Γ(M, U.ι ''ᵁ W) :=
  g • resFrame m₀ W

lemma mulFrame_add (W : U.toScheme.Opens) (g g' : Γ(X, U.ι ''ᵁ W)) :
    mulFrame m₀ W (g + g') = mulFrame m₀ W g + mulFrame m₀ W g' :=
  add_smul g g' (resFrame m₀ W)

lemma mulFrame_mul (W : U.toScheme.Opens) (r g : Γ(X, U.ι ''ᵁ W)) :
    mulFrame m₀ W (r * g) = r • mulFrame m₀ W g :=
  mul_smul r g (resFrame m₀ W)

lemma mulFrame_map {W W' : U.toScheme.Opens} (i : W' ⟶ W) (g : Γ(X, U.ι ''ᵁ W)) :
    (M.restrict U.ι).presheaf.map i.op (mulFrame m₀ W g) =
      mulFrame m₀ W' (U.toScheme.presheaf.map i.op g) := by
  rw [Scheme.Modules.restrict_map, Scheme.Opens.toScheme_presheaf_map]
  unfold mulFrame
  erw [Scheme.Modules.map_smul]
  rw [resFrame_map]
  rfl

def mulFramePresheafHom : (unitMod U.toScheme).presheaf ⟶ (M.restrict U.ι).presheaf where
  app W := AddCommGrpCat.ofHom (AddMonoidHom.mk' (mulFrame m₀ W.unop) (mulFrame_add m₀ W.unop))
  naturality W W' i := by
    ext g
    obtain ⟨i, rfl⟩ : ∃ i' : W'.unop ⟶ W.unop, i = i'.op := ⟨i.unop, rfl⟩
    exact (mulFrame_map m₀ i g).symm

def mulFrameHom : unitMod U.toScheme ⟶ M.restrict U.ι :=
  ⟨PresheafOfModules.homMk (mulFramePresheafHom m₀) (fun W r g => by
    change mulFrame m₀ W.unop
      (@HMul.hMul Γ(X, U.ι ''ᵁ W.unop) Γ(X, U.ι ''ᵁ W.unop) Γ(X, U.ι ''ᵁ W.unop) instHMul r g) =
        ((U.ι.appIso W.unop).inv r) • mulFrame m₀ W.unop g
    rw [Scheme.Opens.ι_appIso, Iso.refl_inv]
    exact mulFrame_mul m₀ W.unop r g)⟩

@[scoped simp] lemma mulFrameHom_app (W : U.toScheme.Opens) (g : Γ(X, U.ι ''ᵁ W)) :
    (mulFrameHom m₀).app W g = mulFrame m₀ W g := rfl

def IsFrame : Prop :=
  ∀ ⦃W : X.Opens⦄ (hWU : W ≤ U), Function.Bijective fun g : Γ(X, W) => g • (M.presheaf.map (homOfLE hWU).op m₀ : Γ(M, W))

lemma IsFrame.smul_isUnit (hfr : IsFrame m₀) {r : Γ(X, U)} (hr : IsUnit r) : IsFrame (r • m₀) := by
  intro W hWU
  have hr' : IsUnit (X.presheaf.map (homOfLE hWU).op r) := hr.map _
  have e : ∀ g : Γ(X, W), g • M.presheaf.map (homOfLE hWU).op (r • m₀) =
      (g * X.presheaf.map (homOfLE hWU).op r) • M.presheaf.map (homOfLE hWU).op m₀ := by
    intro g
    rw [Scheme.Modules.map_smul, smul_smul]
  simp only [e]
  refine (hfr hWU).comp ⟨hr'.mul_left_injective, fun y => ?_⟩
  obtain ⟨r'', hr''⟩ := hr'.exists_left_inv
  exact ⟨y * r'', show y * r'' * X.presheaf.map (homOfLE hWU).op r = y by rw [mul_assoc, hr'', mul_one]⟩

lemma bijective_mulFrame (hfr : IsFrame m₀) (W : U.toScheme.Opens) :
    Function.Bijective (mulFrame m₀ W) :=
  hfr (U.ι_image_le W)

lemma isIso_mulFrameHom (hfr : IsFrame m₀) : IsIso (mulFrameHom m₀) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro W
  have : IsIso ((forget Ab).map ((mulFrameHom m₀).app W)) :=
    (isIso_iff_bijective _).mpr (bijective_mulFrame m₀ hfr W)
  exact isIso_of_reflects_iso _ (forget Ab)

theorem nonempty_pullback_iso_unit (hfr : IsFrame m₀) :
    Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) := by
  haveI := isIso_mulFrameHom m₀ hfr
  exact ⟨((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm ≪≫ (asIso (mulFrameHom m₀)).symm⟩

theorem isInvertible_of_forall_exists_isFrame {Y : Scheme.{u}} {N : Y.Modules}
    (hN : ∀ y : Y, ∃ (U : Y.Opens) (m₀ : Γ(N, U)), y ∈ U ∧ IsFrame m₀) : Scheme.Modules.IsInvertible N := by
  refine ⟨fun y => ?_⟩
  obtain ⟨U, m₀, hyU, hfr⟩ := hN y
  exact ⟨U, hyU, nonempty_pullback_iso_unit m₀ hfr⟩

end TwoGluedCurvesFrameAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_exists_eq_mul_of_iso.TwoGluedCurvesFrameAux"

namespace TwoGluedCurvesNodeUnitAux

open TwoGluedCurvesFrameAux

variable {κ : Type u} [Field κ]
  {X C₁ C₂ : Scheme.{u}} {x : X ⟶ Spec (.of κ)}
  {c₁ : C₁ ⟶ Spec (.of κ)} {c₂ : C₂ ⟶ Spec (.of κ)}
  {i₁ : SchemeHomOver c₁ x} {i₂ : SchemeHomOver c₂ x}
  {ι : Type v} {p₁ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₁} {p₂ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₂}
  {T : Scheme.{u}} {h : T ⟶ Spec (.of κ)} (u : ι → Γ(T, ⊤)ˣ)

local notation "XT" => pullback x h
local notation "C₁T" => pullback c₁ h
local notation "C₂T" => pullback c₂ h
set_option quotPrecheck false in
local notation "i₁T" => curveChange i₁.1 i₁.2 h
set_option quotPrecheck false in
local notation "i₂T" => curveChange i₂.1 i₂.2 h
local notation "σ¹" => nodeSectionFst p₁ h
local notation "σ²" => nodeSectionSnd p₂ h
local notation "nl" => nodeLocus x i₁ i₂ p₁ p₂ h
set_option quotPrecheck false in

local notation "P¹" => (Scheme.Modules.pushforward (curveChange i₁.1 i₁.2 h)).obj
  (SheafOfModules.unit (pullback c₁ h).ringCatSheaf)
set_option quotPrecheck false in

local notation "P²" => (Scheme.Modules.pushforward (curveChange i₂.1 i₂.2 h)).obj
  (SheafOfModules.unit (pullback c₂ h).ringCatSheaf)

def fn₁ (W : (XT).Opens) (f : Γ(P¹, W)) : Γ(C₁T, (i₁T) ⁻¹ᵁ W) := f

def fn₂ (W : (XT).Opens) (g : Γ(P², W)) : Γ(C₂T, (i₂T) ⁻¹ᵁ W) := g

def ofFn₁ (W : (XT).Opens) (f : Γ(C₁T, (i₁T) ⁻¹ᵁ W)) : Γ(P¹, W) := f

def ofFn₂ (W : (XT).Opens) (g : Γ(C₂T, (i₂T) ⁻¹ᵁ W)) : Γ(P², W) := g

@[scoped simp] lemma fn₁_ofFn₁ (W : (XT).Opens) (f : Γ(C₁T, (i₁T) ⁻¹ᵁ W)) : fn₁ W (ofFn₁ W f) = f := rfl
@[scoped simp] lemma fn₂_ofFn₂ (W : (XT).Opens) (g : Γ(C₂T, (i₂T) ⁻¹ᵁ W)) : fn₂ W (ofFn₂ W g) = g := rfl
lemma fn₁_injective (W : (XT).Opens) : Function.Injective (fn₁ (i₁ := i₁) W) := fun _ _ e => e
lemma fn₂_injective (W : (XT).Opens) : Function.Injective (fn₂ (i₂ := i₂) W) := fun _ _ e => e
@[scoped simp] lemma fn₁_zero (W : (XT).Opens) : fn₁ (i₁ := i₁) W 0 = 0 := rfl
@[scoped simp] lemma fn₂_zero (W : (XT).Opens) : fn₂ (i₂ := i₂) W 0 = 0 := rfl
@[scoped simp] lemma fn₁_add (W : (XT).Opens) (f g : Γ(P¹, W)) : fn₁ W (f + g) = fn₁ W f + fn₁ W g := rfl
@[scoped simp] lemma fn₂_add (W : (XT).Opens) (f g : Γ(P², W)) : fn₂ W (f + g) = fn₂ W f + fn₂ W g := rfl

lemma fn₁_smul (W : (XT).Opens) (r : Γ(XT, W)) (f : Γ(P¹, W)) :
    fn₁ W (r • f) = (i₁T).app W r * fn₁ W f := rfl
lemma fn₂_smul (W : (XT).Opens) (r : Γ(XT, W)) (g : Γ(P², W)) :
    fn₂ W (r • g) = (i₂T).app W r * fn₂ W g := rfl

lemma preimage_mono {Y Z : Scheme.{u}} (f : Y ⟶ Z) {W W' : Z.Opens} (hW : W' ≤ W) : f ⁻¹ᵁ W' ≤ f ⁻¹ᵁ W :=
  fun _ hy => hW hy

lemma fn₁_map {W W' : (XT).Opens} (hW : W' ≤ W) (f : Γ(P¹, W)) :
    fn₁ W' ((P¹).presheaf.map (homOfLE hW).op f) =
      (C₁T).presheaf.map (homOfLE (preimage_mono (i₁T) hW)).op (fn₁ W f) := rfl

lemma fn₂_map {W W' : (XT).Opens} (hW : W' ≤ W) (g : Γ(P², W)) :
    fn₂ W' ((P²).presheaf.map (homOfLE hW).op g) =
      (C₂T).presheaf.map (homOfLE (preimage_mono (i₂T) hW)).op (fn₂ W g) := rfl

def ofFun (W : (XT).Opens) (r : Γ(XT, W)) : Γ(unitMod XT, W) := r

def toFun' (W : (XT).Opens) (r : Γ(unitMod XT, W)) : Γ(XT, W) := r

@[scoped simp] lemma ofFun_toFun' (W : (XT).Opens) (r : Γ(unitMod XT, W)) : ofFun W (toFun' W r) = r := rfl
lemma ofFun_mul (W : (XT).Opens) (r r' : Γ(XT, W)) : ofFun W (r * r') = r • ofFun W r' := rfl
lemma ofFun_map {W W' : (XT).Opens} (hW : W' ≤ W) (r : Γ(XT, W)) :
    (unitMod XT).presheaf.map (homOfLE hW).op (ofFun W r) = ofFun W' ((XT).presheaf.map (homOfLE hW).op r) := rfl

def ures (i : ι) (V : T.Opens) : Γ(T, V) := T.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (u i : Γ(T, ⊤))

lemma nodeCondition_iff (W : (XT).Opens) (i : ι) (f : Γ(C₁T, (i₁T) ⁻¹ᵁ W)) (g : Γ(C₂T, (i₂T) ⁻¹ᵁ W)) :
    NodeCondition x i₁ i₂ p₁ p₂ h u W i f g ↔
      (σ¹ i).appLE ((i₁T) ⁻¹ᵁ W) (nl i W) inf_le_left f =
        ures u i (nl i W) * (σ² i).appLE ((i₂T) ⁻¹ᵁ W) (nl i W) inf_le_right g := Iff.rfl

lemma ures_one (i : ι) (V : T.Opens) : ures (1 : ι → Γ(T, ⊤)ˣ) i V = 1 := by
  simp [ures]

lemma nodeCondition_one_iff (W : (XT).Opens) (i : ι) (f : Γ(C₁T, (i₁T) ⁻¹ᵁ W))
    (g : Γ(C₂T, (i₂T) ⁻¹ᵁ W)) :
    NodeCondition x i₁ i₂ p₁ p₂ h 1 W i f g ↔
      (σ¹ i).appLE ((i₁T) ⁻¹ᵁ W) (nl i W) inf_le_left f =
        (σ² i).appLE ((i₂T) ⁻¹ᵁ W) (nl i W) inf_le_right g := by
  rw [nodeCondition_iff, ures_one, one_mul]

lemma nodeCondition_one_mul (W : (XT).Opens) (i : ι) {f f' : Γ(C₁T, (i₁T) ⁻¹ᵁ W)}
    {g g' : Γ(C₂T, (i₂T) ⁻¹ᵁ W)}
    (hfg : NodeCondition x i₁ i₂ p₁ p₂ h 1 W i f g)
    (hfg' : NodeCondition x i₁ i₂ p₁ p₂ h 1 W i f' g') :
    NodeCondition x i₁ i₂ p₁ p₂ h 1 W i (f * f') (g * g') := by
  rw [nodeCondition_one_iff] at hfg hfg' ⊢
  rw [map_mul, map_mul, hfg, hfg']

lemma nodeCondition_one_one (W : (XT).Opens) (i : ι) :
    NodeCondition x i₁ i₂ p₁ p₂ h 1 W i (1 : Γ(C₁T, (i₁T) ⁻¹ᵁ W)) 1 := by
  rw [nodeCondition_one_iff, map_one, map_one]

lemma nodeLocus_mono (i : ι) {W W' : (XT).Opens} (hW : W' ≤ W) : nl i W' ≤ nl i W :=
  inf_le_inf (preimage_mono _ (preimage_mono _ hW)) (preimage_mono _ (preimage_mono _ hW))

lemma appLE_fst_res (i : ι) {W W' : (XT).Opens} (hW : W' ≤ W) (f : Γ(C₁T, (i₁T) ⁻¹ᵁ W)) :
    (σ¹ i).appLE ((i₁T) ⁻¹ᵁ W') (nl i W') inf_le_left
        ((C₁T).presheaf.map (homOfLE (preimage_mono (i₁T) hW)).op f) =
      T.presheaf.map (homOfLE (nodeLocus_mono i hW)).op
        ((σ¹ i).appLE ((i₁T) ⁻¹ᵁ W) (nl i W) inf_le_left f) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE,
    Scheme.Hom.appLE_map]

lemma appLE_snd_res (i : ι) {W W' : (XT).Opens} (hW : W' ≤ W) (g : Γ(C₂T, (i₂T) ⁻¹ᵁ W)) :
    (σ² i).appLE ((i₂T) ⁻¹ᵁ W') (nl i W') inf_le_right
        ((C₂T).presheaf.map (homOfLE (preimage_mono (i₂T) hW)).op g) =
      T.presheaf.map (homOfLE (nodeLocus_mono i hW)).op
        ((σ² i).appLE ((i₂T) ⁻¹ᵁ W) (nl i W) inf_le_right g) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE,
    Scheme.Hom.appLE_map]

lemma ures_res (u' : ι → Γ(T, ⊤)ˣ) {V V' : T.Opens} (hV : V' ≤ V) (i : ι) :
    T.presheaf.map (homOfLE hV).op (ures u' i V) = ures u' i V' := by
  unfold ures
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl

lemma unit_res {V V' : T.Opens} (hV : V' ≤ V) (i : ι) :
    T.presheaf.map (homOfLE hV).op (T.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (u i : Γ(T, ⊤))) =
      T.presheaf.map (homOfLE (le_top : V' ≤ ⊤)).op (u i : Γ(T, ⊤)) := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl

theorem nodeCondition_res (u' : ι → Γ(T, ⊤)ˣ) (i : ι) {W W' : (XT).Opens} (hW : W' ≤ W)
    (f : Γ(C₁T, (i₁T) ⁻¹ᵁ W)) (g : Γ(C₂T, (i₂T) ⁻¹ᵁ W))
    (hfg : NodeCondition x i₁ i₂ p₁ p₂ h u' W i f g) :
    NodeCondition x i₁ i₂ p₁ p₂ h u' W' i
      ((C₁T).presheaf.map (homOfLE (preimage_mono (i₁T) hW)).op f)
      ((C₂T).presheaf.map (homOfLE (preimage_mono (i₂T) hW)).op g) := by
  rw [nodeCondition_iff] at hfg ⊢
  rw [appLE_fst_res i hW f, appLE_snd_res i hW g, hfg, map_mul, ures_res]

lemma appLE_congr_hom {Y Z : Scheme.{u}} {f g : Y ⟶ Z} (e : f = g) (U : Z.Opens) (V : Y.Opens)
    (h₁ : V ≤ f ⁻¹ᵁ U) (h₂ : V ≤ g ⁻¹ᵁ U) : f.appLE U V h₁ = g.appLE U V h₂ := by
  subst e; rfl

lemma appLE_fst_app_eq_appLE_snd_app
    (hν : ∀ i : ι, nodeSectionFst p₁ h i ≫ curveChange i₁.1 i₁.2 h =
      nodeSectionSnd p₂ h i ≫ curveChange i₂.1 i₂.2 h)
    (i : ι) (W : (XT).Opens) (r : Γ(XT, W)) :
    (σ¹ i).appLE ((i₁T) ⁻¹ᵁ W) (nl i W) inf_le_left ((i₁T).app W r) =
      (σ² i).appLE ((i₂T) ⁻¹ᵁ W) (nl i W) inf_le_right ((i₂T).app W r) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appLE,
    ← Scheme.Hom.comp_appLE]
  rw [appLE_congr_hom (hν i)]

theorem nodeSectionFst_comp_eq_nodeSectionSnd_comp
    (hnode : ∀ i, (p₁ i).1 ≫ i₁.1 = (p₂ i).1 ≫ i₂.1) (i : ι) :
    nodeSectionFst p₁ h i ≫ curveChange i₁.1 i₁.2 h = nodeSectionSnd p₂ h i ≫ curveChange i₂.1 i₂.2 h := by
  let ν : SchemeHomOver (𝟙 (Spec (.of κ))) x :=
    ⟨(p₁ i).1 ≫ i₁.1, by rw [Category.assoc, i₁.2, (p₁ i).2]⟩
  have h1 : nodeSectionFst p₁ h i ≫ curveChange i₁.1 i₁.2 h = rigSection x h ν :=
    rigSection_curveChange i₁.1 i₁.2 (ε' := p₁ i) (ε := ν) rfl h
  have h2 : nodeSectionSnd p₂ h i ≫ curveChange i₂.1 i₂.2 h = rigSection x h ν :=
    rigSection_curveChange i₂.1 i₂.2 (ε' := p₂ i) (ε := ν) (hnode i).symm h
  rw [h1, h2]

section Conductor

variable (hO : IsNodeUnitModule x i₁ i₂ p₁ p₂ h 1 (unitMod (pullback x h)))

lemma app_ofFun {P : (XT).Modules} (j : unitMod XT ⟶ P) (W : (XT).Opens) (r : Γ(XT, W)) :
    j.app W (ofFun W r) = r • j.app W (ofFun W 1) := by
  rw [← Scheme.Modules.Hom.app_smul, ← ofFun_mul, mul_one]

include hO in

theorem conductor (W : (XT).Opens) :
    Function.Injective (fun r : Γ(XT, W) => ((i₁T).app W r, (i₂T).app W r)) ∧
      ∀ (f : Γ(C₁T, (i₁T) ⁻¹ᵁ W)) (g : Γ(C₂T, (i₂T) ⁻¹ᵁ W)),
        (∀ i, NodeCondition x i₁ i₂ p₁ p₂ h 1 W i f g) →
          ∃ r : Γ(XT, W), (i₁T).app W r = f ∧ (i₂T).app W r = g := by
  obtain ⟨j₁, j₂, hj⟩ := hO
  obtain ⟨hinj, hrange⟩ := hj W

  set ε₁ : Γ(C₁T, (i₁T) ⁻¹ᵁ W) := fn₁ W (j₁.app W (ofFun W 1))
  set ε₂ : Γ(C₂T, (i₂T) ⁻¹ᵁ W) := fn₂ W (j₂.app W (ofFun W 1))
  have key₁ : ∀ r : Γ(XT, W), fn₁ W (j₁.app W (ofFun W r)) = (i₁T).app W r * ε₁ := fun r => by
    rw [app_ofFun, fn₁_smul]
  have key₂ : ∀ r : Γ(XT, W), fn₂ W (j₂.app W (ofFun W r)) = (i₂T).app W r * ε₂ := fun r => by
    rw [app_ofFun, fn₂_smul]

  have hmem : ∀ (f : Γ(C₁T, (i₁T) ⁻¹ᵁ W)) (g : Γ(C₂T, (i₂T) ⁻¹ᵁ W)),
      (∀ i, NodeCondition x i₁ i₂ p₁ p₂ h 1 W i f g) →
        ∃ r : Γ(XT, W), fn₁ W (j₁.app W (ofFun W r)) = f ∧ fn₂ W (j₂.app W (ofFun W r)) = g := by
    intro f g hfg
    have : (ofFn₁ W f, ofFn₂ W g) ∈ Set.range (fun m : Γ(unitMod XT, W) => (j₁.app W m, j₂.app W m)) := by
      rw [hrange]; exact hfg
    obtain ⟨m, hm⟩ := this
    refine ⟨toFun' W m, ?_, ?_⟩
    · rw [ofFun_toFun']; exact congrArg (fn₁ W) (congrArg Prod.fst hm)
    · rw [ofFun_toFun']; exact congrArg (fn₂ W) (congrArg Prod.snd hm)
  have hsat : ∀ (r : Γ(XT, W)) (i : ι), NodeCondition x i₁ i₂ p₁ p₂ h 1 W i
      (fn₁ W (j₁.app W (ofFun W r))) (fn₂ W (j₂.app W (ofFun W r))) := by
    intro r
    have : (j₁.app W (ofFun W r), j₂.app W (ofFun W r)) ∈
        Set.range (fun m : Γ(unitMod XT, W) => (j₁.app W m, j₂.app W m)) := ⟨_, rfl⟩
    rw [hrange] at this
    exact this

  obtain ⟨r₀, hr₀₁, hr₀₂⟩ := hmem 1 1 (fun i => nodeCondition_one_one W i)
  have hu₁ : IsUnit ε₁ := by
    rw [key₁] at hr₀₁
    exact IsUnit.of_mul_eq_one_right _ hr₀₁
  have hu₂ : IsUnit ε₂ := by
    rw [key₂] at hr₀₂
    exact IsUnit.of_mul_eq_one_right _ hr₀₂
  have hεν : ∀ i, NodeCondition x i₁ i₂ p₁ p₂ h 1 W i ε₁ ε₂ := hsat 1
  refine ⟨?_, ?_⟩
  · intro r r' hrr'
    simp only [Prod.mk.injEq] at hrr'
    have e : ofFun W r = ofFun W r' := by
      apply hinj
      simp only [Prod.mk.injEq]
      constructor
      · apply fn₁_injective
        rw [key₁, key₁, hrr'.1]
      · apply fn₂_injective
        rw [key₂, key₂, hrr'.2]
    exact congrArg (toFun' W) e
  · intro f g hfg
    obtain ⟨r, hr₁, hr₂⟩ := hmem (f * ε₁) (g * ε₂) (fun i => nodeCondition_one_mul W i (hfg i) (hεν i))
    refine ⟨r, ?_, ?_⟩
    · rw [key₁] at hr₁
      exact hu₁.mul_right_cancel hr₁
    · rw [key₂] at hr₂
      exact hu₂.mul_right_cancel hr₂

end Conductor
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_exists_eq_mul_of_iso.TwoGluedCurvesFrameAux"

def nodePt (i₁ : SchemeHomOver c₁ x) (p₁ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₁) (i : ι) : X :=
  i₁.1.base ((p₁ i).1.base (IsLocalRing.closedPoint κ))

lemma nodeSectionFst_curveChange_fst (i : ι) :
    σ¹ i ≫ (i₁T) ≫ pullback.fst x h = h ≫ (p₁ i).1 ≫ i₁.1 := by
  simp only [nodeSectionFst, rigSection, curveChange, pullback.lift_fst, pullback.lift_fst_assoc,
    Category.assoc]

lemma nodeSectionFst_curveChange_fst_apply (i : ι) (t : T) :
    (pullback.fst x h).base ((i₁T).base ((σ¹ i).base t)) = nodePt i₁ p₁ i := by
  have e := nodeSectionFst_curveChange_fst (x := x) (i₁ := i₁) (p₁ := p₁) (h := h) i
  have := congrArg (fun φ : T ⟶ X => φ.base t) e
  simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply] at this
  rw [this, Subsingleton.elim (h.base t) (IsLocalRing.closedPoint κ)]
  rfl

lemma nodeLocus_eq_bot {V : X.Opens} {i : ι} (hi : nodePt i₁ p₁ i ∉ V) {W : (XT).Opens}
    (hW : W ≤ (pullback.fst x h) ⁻¹ᵁ V) : nl i W = ⊥ := by
  rw [eq_bot_iff]
  intro t ht
  have h1 : (i₁T).base ((σ¹ i).base t) ∈ W := ht.1
  have h2 := hW h1
  change (pullback.fst x h).base ((i₁T).base ((σ¹ i).base t)) ∈ V at h2
  rw [nodeSectionFst_curveChange_fst_apply] at h2
  exact (hi h2).elim

lemma nodeCondition_of_eq_bot (u' : ι → Γ(T, ⊤)ˣ) {W : (XT).Opens} {i : ι} (hbot : nl i W = ⊥)
    (f : Γ(C₁T, (i₁T) ⁻¹ᵁ W)) (g : Γ(C₂T, (i₂T) ⁻¹ᵁ W)) :
    NodeCondition x i₁ i₂ p₁ p₂ h u' W i f g := by
  haveI : Subsingleton Γ(T, nl i W) :=
    CommRingCat.subsingleton_of_isTerminal (T.sheaf.isTerminalOfEqEmpty hbot)
  exact Subsingleton.elim _ _

def sndFun (c : Γ(T, ⊤)) (W : (XT).Opens) : Γ(C₂T, (i₂T) ⁻¹ᵁ W) :=
  (pullback.snd c₂ h).appLE ⊤ ((i₂T) ⁻¹ᵁ W) le_top c

lemma sndFun_mul (c c' : Γ(T, ⊤)) (W : (XT).Opens) :
    sndFun (i₂ := i₂) (c * c') W = sndFun c W * sndFun c' W := map_mul _ _ _

lemma sndFun_one (W : (XT).Opens) : sndFun (i₂ := i₂) (1 : Γ(T, ⊤)) W = 1 := map_one _

lemma sndFun_map {W W' : (XT).Opens} (hW : W' ≤ W) (c : Γ(T, ⊤)) :
    (C₂T).presheaf.map (homOfLE (preimage_mono (i₂T) hW)).op (sndFun c W) = sndFun c W' := by
  unfold sndFun
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]

lemma isUnit_sndFun (v : Γ(T, ⊤)ˣ) (W : (XT).Opens) : IsUnit (sndFun (i₂ := i₂) (v : Γ(T, ⊤)) W) :=
  (Units.isUnit v).map _

lemma nodeSectionSnd_snd (i : ι) : σ² i ≫ pullback.snd c₂ h = 𝟙 T := by
  simp only [nodeSectionSnd, rigSection, pullback.lift_snd]

lemma appLE_sndFun (i : ι) (W : (XT).Opens) (c : Γ(T, ⊤)) :
    (σ² i).appLE ((i₂T) ⁻¹ᵁ W) (nl i W) inf_le_right (sndFun c W) =
      T.presheaf.map (homOfLE (le_top : nl i W ≤ ⊤)).op c := by
  unfold sndFun
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_comp_appLE]
  rw [appLE_congr_hom (nodeSectionSnd_snd i) ⊤ (nl i W) _ le_top]
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
  rfl

section Frame

variable {M : (pullback x h).Modules}
  (j₁ : M ⟶ (Scheme.Modules.pushforward (curveChange i₁.1 i₁.2 h)).obj
    (SheafOfModules.unit (pullback c₁ h).ringCatSheaf))
  (j₂ : M ⟶ (Scheme.Modules.pushforward (curveChange i₂.1 i₂.2 h)).obj
    (SheafOfModules.unit (pullback c₂ h).ringCatSheaf))
  (hj : ∀ W : (pullback x h).Opens, Function.Injective (fun m : Γ(M, W) => (j₁.app W m, j₂.app W m)) ∧
    Set.range (fun m : Γ(M, W) => (j₁.app W m, j₂.app W m)) =
      {fg | ∀ i : ι, NodeCondition x i₁ i₂ p₁ p₂ h u W i fg.1 fg.2})
  (hO : IsNodeUnitModule x i₁ i₂ p₁ p₂ h 1 (unitMod (pullback x h)))
  {V : X.Opens} {v : Γ(T, ⊤)ˣ} (hV : ∀ i, nodePt i₁ p₁ i ∈ V → u i = v)

include hV in

lemma nodeCondition_one_vinv {W : (XT).Opens} (hW : W ≤ (pullback.fst x h) ⁻¹ᵁ V) (i : ι) :
    NodeCondition x i₁ i₂ p₁ p₂ h u W i 1 (sndFun (v⁻¹ : Γ(T, ⊤)ˣ) W) := by
  by_cases hi : nodePt i₁ p₁ i ∈ V
  · rw [nodeCondition_iff, map_one, appLE_sndFun, ures, hV i hi, ← map_mul, Units.mul_inv, map_one]
  · exact nodeCondition_of_eq_bot u (nodeLocus_eq_bot hi hW) _ _

include hV in

lemma nodeCondition_one_of_nodeCondition {W : (XT).Opens} (hW : W ≤ (pullback.fst x h) ⁻¹ᵁ V) (i : ι)
    (f : Γ(C₁T, (i₁T) ⁻¹ᵁ W)) (g : Γ(C₂T, (i₂T) ⁻¹ᵁ W))
    (hfg : NodeCondition x i₁ i₂ p₁ p₂ h u W i f g) :
    NodeCondition x i₁ i₂ p₁ p₂ h 1 W i f (g * sndFun (v : Γ(T, ⊤)) W) := by
  by_cases hi : nodePt i₁ p₁ i ∈ V
  · rw [nodeCondition_one_iff, map_mul, appLE_sndFun]
    rw [nodeCondition_iff, ures, hV i hi] at hfg
    rw [hfg, mul_comm]
  · exact nodeCondition_of_eq_bot 1 (nodeLocus_eq_bot hi hW) _ _

include hj hO hV in

theorem exists_isFrame :
    ∃ m₀ : Γ(M, (pullback.fst x h) ⁻¹ᵁ V), IsFrame m₀ ∧
      fn₁ _ (j₁.app _ m₀) = 1 ∧ fn₂ _ (j₂.app _ m₀) = sndFun (v⁻¹ : Γ(T, ⊤)ˣ) _ := by
  set U₀ : (XT).Opens := (pullback.fst x h) ⁻¹ᵁ V

  have hp₀ : (ofFn₁ U₀ 1, ofFn₂ U₀ (sndFun (v⁻¹ : Γ(T, ⊤)ˣ) U₀)) ∈
      Set.range (fun m : Γ(M, U₀) => (j₁.app U₀ m, j₂.app U₀ m)) := by
    rw [(hj U₀).2]
    exact fun i => nodeCondition_one_vinv u hV le_rfl i
  obtain ⟨m₀, hm₀⟩ := hp₀
  have hm₀₁ : fn₁ U₀ (j₁.app U₀ m₀) = 1 := congrArg (fn₁ U₀) (congrArg Prod.fst hm₀)
  have hm₀₂ : fn₂ U₀ (j₂.app U₀ m₀) = sndFun (v⁻¹ : Γ(T, ⊤)ˣ) U₀ := congrArg (fn₂ U₀) (congrArg Prod.snd hm₀)
  refine ⟨m₀, ?_, hm₀₁, hm₀₂⟩
  intro W hWU

  have app_map : ∀ {N N' : (XT).Modules} (φ : N ⟶ N') (n : Γ(N, U₀)),
      φ.app W (N.presheaf.map (homOfLE hWU).op n) = N'.presheaf.map (homOfLE hWU).op (φ.app U₀ n) :=
    fun φ n => ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE hWU).op) n
  have c₁ : ∀ g : Γ(XT, W), fn₁ W (j₁.app W (g • M.presheaf.map (homOfLE hWU).op m₀)) = (i₁T).app W g := by
    intro g
    rw [Scheme.Modules.Hom.app_smul, fn₁_smul, app_map, fn₁_map, hm₀₁, map_one, mul_one]
  have c₂ : ∀ g : Γ(XT, W), fn₂ W (j₂.app W (g • M.presheaf.map (homOfLE hWU).op m₀)) =
      (i₂T).app W g * sndFun (v⁻¹ : Γ(T, ⊤)ˣ) W := by
    intro g
    rw [Scheme.Modules.Hom.app_smul, fn₂_smul, app_map, fn₂_map, hm₀₂, sndFun_map hWU]
  obtain ⟨hinjO, hrangeO⟩ := conductor hO W
  have hvv : sndFun (i₂ := i₂) (v : Γ(T, ⊤)) W * sndFun (v⁻¹ : Γ(T, ⊤)ˣ) W = 1 := by
    rw [← sndFun_mul, Units.mul_inv, sndFun_one]
  constructor
  · intro g g' hgg'
    have e₁ := congrArg (fun m => fn₁ W (j₁.app W m)) hgg'
    have e₂ := congrArg (fun m => fn₂ W (j₂.app W m)) hgg'
    simp only [c₁, c₂] at e₁ e₂
    apply hinjO
    simp only [Prod.mk.injEq]
    exact ⟨e₁, (isUnit_sndFun (v⁻¹) W).mul_right_cancel e₂⟩
  · intro m

    have hfg : ∀ i, NodeCondition x i₁ i₂ p₁ p₂ h u W i (fn₁ W (j₁.app W m)) (fn₂ W (j₂.app W m)) := by
      have : (j₁.app W m, j₂.app W m) ∈ Set.range (fun m : Γ(M, W) => (j₁.app W m, j₂.app W m)) := ⟨m, rfl⟩
      rw [(hj W).2] at this
      exact this
    obtain ⟨r, hr₁, hr₂⟩ := hrangeO (fn₁ W (j₁.app W m)) (fn₂ W (j₂.app W m) * sndFun (v : Γ(T, ⊤)) W)
      (fun i => nodeCondition_one_of_nodeCondition u hV hWU i _ _ (hfg i))
    refine ⟨r, ?_⟩
    apply (hj W).1
    simp only [Prod.mk.injEq]
    constructor
    · apply fn₁_injective
      rw [c₁, hr₁]
    · apply fn₂_injective
      rw [c₂, hr₂, mul_assoc, hvv, mul_one]

end Frame
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_exists_eq_mul_of_iso.TwoGluedCurvesFrameAux"

section Cover

variable [IsClosedImmersion i₁.1] [Finite ι]
  (hinj : Function.Injective fun j => (p₁ j).1.base (IsLocalRing.closedPoint κ))

include hinj in
omit [Finite ι] in
lemma nodePt_injective : Function.Injective (nodePt i₁ p₁) := fun _ _ hij =>
  hinj (i₁.1.isClosedEmbedding.injective hij)

omit [Finite ι] in
lemma isClosed_nodePt (i : ι) : IsClosed ({nodePt i₁ p₁ i} : Set X) := by
  haveI : IsClosedImmersion (p₁ i).1 := isClosedImmersion_of_comp_eq_id c₁ (p₁ i).1 (p₁ i).2
  have e : Set.range ((p₁ i).1 ≫ i₁.1).base = {nodePt i₁ p₁ i} := by
    ext q
    constructor
    · rintro ⟨t, rfl⟩
      rw [Subsingleton.elim t (IsLocalRing.closedPoint κ)]
      rfl
    · rintro rfl
      exact ⟨IsLocalRing.closedPoint κ, rfl⟩
  rw [← e]
  exact ((p₁ i).1 ≫ i₁.1).isClosedEmbedding.isClosed_range

def awayFrom (S : Set ι) : X.Opens :=
  ⟨(⋃ j : S, {nodePt i₁ p₁ j.1})ᶜ, isOpen_compl_iff.2 (isClosed_iUnion_of_finite fun j => isClosed_nodePt j.1)⟩

lemma mem_awayFrom_iff (S : Set ι) (q : X) : q ∈ awayFrom (i₁ := i₁) (p₁ := p₁) S ↔ ∀ j ∈ S, q ≠ nodePt i₁ p₁ j := by
  change q ∈ (⋃ j : S, {nodePt i₁ p₁ j.1})ᶜ ↔ _
  simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_singleton_iff, not_exists]
  exact ⟨fun H j hj => H ⟨j, hj⟩, fun H j => H j.1 j.2⟩

include hinj in

theorem exists_open_sameUnit (q : X) :
    ∃ (V : X.Opens) (v : Γ(T, ⊤)ˣ), q ∈ V ∧ ∀ i, nodePt i₁ p₁ i ∈ V → u i = v := by
  by_cases hq : ∃ i₀, q = nodePt i₁ p₁ i₀
  · obtain ⟨i₀, rfl⟩ := hq
    refine ⟨awayFrom (i₁ := i₁) (p₁ := p₁) {j | j ≠ i₀}, u i₀, ?_, ?_⟩
    · rw [mem_awayFrom_iff]
      intro j hj e
      exact hj (nodePt_injective hinj e).symm
    · intro i hi
      rw [mem_awayFrom_iff] at hi
      by_contra hne
      exact hi i (fun e => hne (e ▸ rfl)) rfl
  · refine ⟨awayFrom (i₁ := i₁) (p₁ := p₁) Set.univ, 1, ?_, ?_⟩
    · rw [mem_awayFrom_iff]
      intro j _ e
      exact hq ⟨j, e⟩
    · intro i hi
      rw [mem_awayFrom_iff] at hi
      exact (hi i trivial rfl).elim

end Cover
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_exists_eq_mul_of_iso.TwoGluedCurvesFrameAux"

def topFun (c : Γ(T, ⊤)) (W : (XT).Opens) : Γ(XT, W) := (pullback.snd x h).appLE ⊤ W le_top c

lemma isUnit_topFun (v : Γ(T, ⊤)ˣ) (W : (XT).Opens) : IsUnit (topFun (x := x) (h := h) (v : Γ(T, ⊤)) W) :=
  (Units.isUnit v).map _

lemma app_topFun (c : Γ(T, ⊤)) (W : (XT).Opens) : (i₂T).app W (topFun c W) = sndFun (i₂ := i₂) c W := by
  unfold topFun sndFun
  rw [Scheme.Hom.app_eq_appLE, ← ConcreteCategory.comp_apply, Scheme.Hom.appLE_comp_appLE]
  rw [appLE_congr_hom (curveChange_snd i₂.1 i₂.2 h) ⊤ ((i₂T) ⁻¹ᵁ W) _ le_top]

section Restrict

variable [IsClosedImmersion i₁.1] [Finite ι]
  (hinj : Function.Injective fun j => (p₁ j).1.base (IsLocalRing.closedPoint κ))
  (hO : IsNodeUnitModule x i₁ i₂ p₁ p₂ h 1 (unitMod (pullback x h)))
  {M : (pullback x h).Modules}
  (j₁ : M ⟶ (Scheme.Modules.pushforward (curveChange i₁.1 i₁.2 h)).obj
    (SheafOfModules.unit (pullback c₁ h).ringCatSheaf))
  (j₂ : M ⟶ (Scheme.Modules.pushforward (curveChange i₂.1 i₂.2 h)).obj
    (SheafOfModules.unit (pullback c₂ h).ringCatSheaf))
  (hj : ∀ W : (pullback x h).Opens, Function.Injective (fun m : Γ(M, W) => (j₁.app W m, j₂.app W m)) ∧
    Set.range (fun m : Γ(M, W) => (j₁.app W m, j₂.app W m)) =
      {fg | ∀ i : ι, NodeCondition x i₁ i₂ p₁ p₂ h u W i fg.1 fg.2})

include hinj hO hj in

theorem isIso_transpose_fst :
    IsIso (((Scheme.Modules.pullbackPushforwardAdjunction (i₁T)).homEquiv M _).symm j₁) := by
  have key : ∀ q : X, ∃ (V : X.Opens) (m₀ : Γ(M, (pullback.fst x h) ⁻¹ᵁ V)),
      q ∈ V ∧ IsFrame m₀ ∧ fn₁ _ (j₁.app _ m₀) = 1 := by
    intro q
    obtain ⟨V, v, hqV, hV⟩ := exists_open_sameUnit (i₁ := i₁) (T := T) u hinj q
    obtain ⟨m₀, hfr, h1, -⟩ := exists_isFrame u j₁ j₂ hj hO hV
    exact ⟨V, m₀, hqV, hfr, h1⟩
  choose V m₀ hqV hfr h1 using key
  have hcov : ⨆ q, (i₁T) ⁻¹ᵁ ((pullback.fst x h) ⁻¹ᵁ (V q)) = ⊤ := by
    apply eq_top_iff.mpr
    intro c _
    exact Opens.mem_iSup.mpr ⟨(pullback.fst x h).base ((i₁T).base c), hqV _⟩
  refine Scheme.Modules.isIso_of_isFrameOn_of_iSup_eq_top _
    (fun q => (i₁T) ⁻¹ᵁ ((pullback.fst x h) ⁻¹ᵁ (V q))) hcov
    (fun q => Scheme.Modules.pullbackLocalSection (i₁T) (m₀ q))
    (fun q => Scheme.Modules.unitSection _)
    (fun q => Scheme.Modules.IsFrameOn.pullbackLocalSection (i₁T) (fun W hWU _ => hfr q hWU))
    (fun q => Scheme.Modules.isFrameOn_unitSection _) (fun q => ?_)
  rw [Scheme.Modules.homEquiv_symm_app_pullbackLocalSection]
  exact h1 q

include hinj hO hj in

theorem isIso_transpose_snd :
    IsIso (((Scheme.Modules.pullbackPushforwardAdjunction (i₂T)).homEquiv M _).symm j₂) := by
  have key : ∀ q : X, ∃ (V : X.Opens) (m₁ : Γ(M, (pullback.fst x h) ⁻¹ᵁ V)),
      q ∈ V ∧ IsFrame m₁ ∧ fn₂ _ (j₂.app _ m₁) = 1 := by
    intro q
    obtain ⟨V, v, hqV, hV⟩ := exists_open_sameUnit (i₁ := i₁) (T := T) u hinj q
    obtain ⟨m₀, hfr, -, h2⟩ := exists_isFrame u j₁ j₂ hj hO hV
    refine ⟨V, topFun (v : Γ(T, ⊤)) _ • m₀, hqV, IsFrame.smul_isUnit m₀ hfr (isUnit_topFun v _), ?_⟩
    rw [Scheme.Modules.Hom.app_smul, fn₂_smul, h2, app_topFun, ← sndFun_mul, Units.mul_inv, sndFun_one]
  choose V m₁ hqV hfr h2 using key
  have hcov : ⨆ q, (i₂T) ⁻¹ᵁ ((pullback.fst x h) ⁻¹ᵁ (V q)) = ⊤ := by
    apply eq_top_iff.mpr
    intro c _
    exact Opens.mem_iSup.mpr ⟨(pullback.fst x h).base ((i₂T).base c), hqV _⟩
  refine Scheme.Modules.isIso_of_isFrameOn_of_iSup_eq_top _
    (fun q => (i₂T) ⁻¹ᵁ ((pullback.fst x h) ⁻¹ᵁ (V q))) hcov
    (fun q => Scheme.Modules.pullbackLocalSection (i₂T) (m₁ q))
    (fun q => Scheme.Modules.unitSection _)
    (fun q => Scheme.Modules.IsFrameOn.pullbackLocalSection (i₂T) (fun W hWU _ => hfr q hWU))
    (fun q => Scheme.Modules.isFrameOn_unitSection _) (fun q => ?_)
  rw [Scheme.Modules.homEquiv_symm_app_pullbackLocalSection]
  exact h2 q

end Restrict
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_exists_eq_mul_of_iso.TwoGluedCurvesFrameAux"

section EndUnit

variable {Y : Scheme.{u}}

def secFun (V : Y.Opens) (g : Γ(unitMod Y, V)) : Γ(Y, V) := g

def funSec (V : Y.Opens) (r : Γ(Y, V)) : Γ(unitMod Y, V) := r

@[scoped simp] lemma secFun_funSec (V : Y.Opens) (r : Γ(Y, V)) : secFun V (funSec V r) = r := rfl
@[scoped simp] lemma funSec_secFun (V : Y.Opens) (g : Γ(unitMod Y, V)) : funSec V (secFun V g) = g := rfl
lemma funSec_mul (V : Y.Opens) (r r' : Γ(Y, V)) : funSec V (r * r') = r • funSec V r' := rfl
lemma secFun_smul (V : Y.Opens) (r : Γ(Y, V)) (g : Γ(unitMod Y, V)) : secFun V (r • g) = r * secFun V g := rfl
lemma funSec_map {V V' : Y.Opens} (hV : V' ≤ V) (r : Γ(Y, V)) :
    (unitMod Y).presheaf.map (homOfLE hV).op (funSec V r) = funSec V' (Y.presheaf.map (homOfLE hV).op r) := rfl
lemma secFun_map {V V' : Y.Opens} (hV : V' ≤ V) (g : Γ(unitMod Y, V)) :
    secFun V' ((unitMod Y).presheaf.map (homOfLE hV).op g) = Y.presheaf.map (homOfLE hV).op (secFun V g) := rfl

lemma app_map' {N N' : Y.Modules} (φ : N ⟶ N') {V V' : Y.Opens} (hV : V' ≤ V) (n : Γ(N, V)) :
    φ.app V' (N.presheaf.map (homOfLE hV).op n) = N'.presheaf.map (homOfLE hV).op (φ.app V n) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE hV).op) n

def endFun (α : unitMod Y ⟶ unitMod Y) : Γ(Y, ⊤) := secFun ⊤ (α.app ⊤ (funSec ⊤ 1))

theorem secFun_app (α : unitMod Y ⟶ unitMod Y) (V : Y.Opens) (g : Γ(unitMod Y, V)) :
    secFun V (α.app V g) = secFun V g * Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (endFun α) := by
  have hg : g = secFun V g • funSec V 1 := by
    rw [← funSec_mul, mul_one]; rfl
  have h1 : funSec V (1 : Γ(Y, V)) = (unitMod Y).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (funSec ⊤ 1) := by
    rw [funSec_map, map_one]
  conv_lhs => rw [hg]
  rw [Scheme.Modules.Hom.app_smul, secFun_smul, h1, app_map', secFun_map]
  rfl

lemma map_top_top {F : Y.Opensᵒᵖ ⥤ CommRingCat} (a : F.obj (op ⊤)) :
    F.map (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op a = a := by
  have : (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op = 𝟙 _ := rfl
  rw [this, F.map_id]
  rfl

lemma endFun_comp (α β : unitMod Y ⟶ unitMod Y) : endFun (α ≫ β) = endFun α * endFun β := by
  unfold endFun
  rw [Scheme.Modules.Hom.comp_app]
  change secFun ⊤ (β.app ⊤ (α.app ⊤ (funSec ⊤ 1))) = _
  rw [secFun_app β, map_top_top]
  rfl

lemma endFun_id : endFun (𝟙 (unitMod Y)) = 1 := by
  unfold endFun
  rw [Scheme.Modules.Hom.id_app]
  rfl

lemma isUnit_endFun_hom (α : unitMod Y ≅ unitMod Y) : IsUnit (endFun α.hom) :=
  IsUnit.of_mul_eq_one (endFun α.inv) (by rw [← endFun_comp, Iso.hom_inv_id, endFun_id])

theorem exists_isUnit_secFun_app_eq {N : Y.Modules} (φ ψ : N ⟶ unitMod Y) [IsIso φ] [IsIso ψ] :
    ∃ a : Γ(Y, ⊤), IsUnit a ∧ ∀ (V : Y.Opens) (n : Γ(N, V)),
      secFun V (ψ.app V n) = secFun V (φ.app V n) * Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op a := by
  refine ⟨endFun ((asIso φ).symm ≪≫ asIso ψ).hom, isUnit_endFun_hom _, fun V n => ?_⟩
  have e : φ ≫ ((asIso φ).symm ≪≫ asIso ψ).hom = ψ := by simp
  conv_lhs => rw [← e]
  rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  exact secFun_app ((asIso φ).symm ≪≫ asIso ψ).hom V (φ.app V n)

end EndUnit
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_exists_eq_mul_of_iso.TwoGluedCurvesFrameAux"

section Ratio

variable [IsClosedImmersion i₁.1] [Finite ι]
  (hinj : Function.Injective fun j => (p₁ j).1.base (IsLocalRing.closedPoint κ))
  (hO : IsNodeUnitModule x i₁ i₂ p₁ p₂ h 1 (unitMod (pullback x h)))
  {M : (pullback x h).Modules}
  (j₁ : M ⟶ (Scheme.Modules.pushforward (curveChange i₁.1 i₁.2 h)).obj
    (SheafOfModules.unit (pullback c₁ h).ringCatSheaf))
  (j₂ : M ⟶ (Scheme.Modules.pushforward (curveChange i₂.1 i₂.2 h)).obj
    (SheafOfModules.unit (pullback c₂ h).ringCatSheaf))
  (hj : ∀ W : (pullback x h).Opens, Function.Injective (fun m : Γ(M, W) => (j₁.app W m, j₂.app W m)) ∧
    Set.range (fun m : Γ(M, W) => (j₁.app W m, j₂.app W m)) =
      {fg | ∀ i : ι, NodeCondition x i₁ i₂ p₁ p₂ h u W i fg.1 fg.2})
  (u' : ι → Γ(T, ⊤)ˣ)
  (k₁ : M ⟶ (Scheme.Modules.pushforward (curveChange i₁.1 i₁.2 h)).obj
    (SheafOfModules.unit (pullback c₁ h).ringCatSheaf))
  (k₂ : M ⟶ (Scheme.Modules.pushforward (curveChange i₂.1 i₂.2 h)).obj
    (SheafOfModules.unit (pullback c₂ h).ringCatSheaf))
  (hk : ∀ W : (pullback x h).Opens, Function.Injective (fun m : Γ(M, W) => (k₁.app W m, k₂.app W m)) ∧
    Set.range (fun m : Γ(M, W) => (k₁.app W m, k₂.app W m)) =
      {fg | ∀ i : ι, NodeCondition x i₁ i₂ p₁ p₂ h u' W i fg.1 fg.2})

include hinj hO hj hk in

theorem exists_ratio_fst :
    ∃ a : Γ(C₁T, ⊤), IsUnit a ∧ ∀ (W : (XT).Opens) (m : Γ(M, W)),
      fn₁ W (k₁.app W m) = fn₁ W (j₁.app W m) * (C₁T).presheaf.map (homOfLE le_top).op a := by
  haveI := isIso_transpose_fst u hinj hO j₁ j₂ hj
  haveI := isIso_transpose_fst u' hinj hO k₁ k₂ hk
  obtain ⟨a, ha, key⟩ := exists_isUnit_secFun_app_eq
    (((Scheme.Modules.pullbackPushforwardAdjunction (i₁T)).homEquiv M _).symm j₁)
    (((Scheme.Modules.pullbackPushforwardAdjunction (i₁T)).homEquiv M _).symm k₁)
  refine ⟨a, ha, fun W m => ?_⟩
  have e := key ((i₁T) ⁻¹ᵁ W) (Scheme.Modules.pullbackLocalSection (i₁T) m)
  rw [Scheme.Modules.homEquiv_symm_app_pullbackLocalSection,
    Scheme.Modules.homEquiv_symm_app_pullbackLocalSection] at e
  exact e

include hinj hO hj hk in

theorem exists_ratio_snd :
    ∃ a : Γ(C₂T, ⊤), IsUnit a ∧ ∀ (W : (XT).Opens) (m : Γ(M, W)),
      fn₂ W (k₂.app W m) = fn₂ W (j₂.app W m) * (C₂T).presheaf.map (homOfLE le_top).op a := by
  haveI := isIso_transpose_snd u hinj hO j₁ j₂ hj
  haveI := isIso_transpose_snd u' hinj hO k₁ k₂ hk
  obtain ⟨a, ha, key⟩ := exists_isUnit_secFun_app_eq
    (((Scheme.Modules.pullbackPushforwardAdjunction (i₂T)).homEquiv M _).symm j₂)
    (((Scheme.Modules.pullbackPushforwardAdjunction (i₂T)).homEquiv M _).symm k₂)
  refine ⟨a, ha, fun W m => ?_⟩
  have e := key ((i₂T) ⁻¹ᵁ W) (Scheme.Modules.pullbackLocalSection (i₂T) m)
  rw [Scheme.Modules.homEquiv_symm_app_pullbackLocalSection,
    Scheme.Modules.homEquiv_symm_app_pullbackLocalSection] at e
  exact e

end Ratio
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_exists_eq_mul_of_iso.TwoGluedCurvesFrameAux"

theorem injective_and_range_comp_iso {N N' : (pullback x h).Modules} (e : N ≅ N') (u₀ : ι → Γ(T, ⊤)ˣ)
    (j₁ : N' ⟶ (Scheme.Modules.pushforward (curveChange i₁.1 i₁.2 h)).obj
      (SheafOfModules.unit (pullback c₁ h).ringCatSheaf))
    (j₂ : N' ⟶ (Scheme.Modules.pushforward (curveChange i₂.1 i₂.2 h)).obj
      (SheafOfModules.unit (pullback c₂ h).ringCatSheaf))
    (hj : ∀ W : (pullback x h).Opens, Function.Injective (fun m : Γ(N', W) => (j₁.app W m, j₂.app W m)) ∧
      Set.range (fun m : Γ(N', W) => (j₁.app W m, j₂.app W m)) =
        {fg | ∀ i : ι, NodeCondition x i₁ i₂ p₁ p₂ h u₀ W i fg.1 fg.2})
    (W : (pullback x h).Opens) :
    Function.Injective (fun m : Γ(N, W) => ((e.hom ≫ j₁).app W m, (e.hom ≫ j₂).app W m)) ∧
      Set.range (fun m : Γ(N, W) => ((e.hom ≫ j₁).app W m, (e.hom ≫ j₂).app W m)) =
        {fg | ∀ i : ι, NodeCondition x i₁ i₂ p₁ p₂ h u₀ W i fg.1 fg.2} := by
  have hb : Function.Bijective (e.hom.app W : Γ(N, W) → Γ(N', W)) := by
    refine Function.bijective_iff_has_inverse.2 ⟨e.inv.app W, fun m => ?_, fun m => ?_⟩
    · change (e.hom.app W ≫ e.inv.app W) m = m
      rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app]; rfl
    · change (e.inv.app W ≫ e.hom.app W) m = m
      rw [← Scheme.Modules.Hom.comp_app, e.inv_hom_id, Scheme.Modules.Hom.id_app]; rfl
  have hcomp : (fun m : Γ(N, W) => ((e.hom ≫ j₁).app W m, (e.hom ≫ j₂).app W m)) =
      (fun m : Γ(N', W) => (j₁.app W m, j₂.app W m)) ∘ (e.hom.app W) := rfl
  rw [hcomp, hb.2.range_comp]
  exact ⟨(hj W).1.comp hb.1, (hj W).2⟩

theorem exists_eq_appTop_snd [IsAlgClosed κ] {C : Scheme.{u}} (c : C ⟶ Spec (.of κ))
    [IsProper c] [IsIntegral C] (a : Γ(pullback c (𝟙 (Spec (.of κ))), ⊤)) :
    ∃ d : Γ(Spec (.of κ), ⊤), a = (pullback.snd c (𝟙 (Spec (.of κ)))).appTop d := by
  obtain ⟨t, ht⟩ := (AlgebraicGeometry.bijective_algebraMap_appTop_of_isProper_of_isIntegral κ c).2
    ((inv (pullback.fst c (𝟙 (Spec (.of κ))))).appTop a)
  refine ⟨(Scheme.ΓSpecIso (.of κ)).inv t, ?_⟩
  have h1 : (pullback.fst c (𝟙 (Spec (.of κ)))).appTop
      ((inv (pullback.fst c (𝟙 (Spec (.of κ))))).appTop a) = a := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, IsIso.hom_inv_id, Scheme.Hom.id_appTop]
    rfl
  have h2 : pullback.snd c (𝟙 (Spec (.of κ))) = pullback.fst c (𝟙 (Spec (.of κ))) ≫ c := by
    rw [pullback.condition, Category.comp_id]
  rw [h2, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ← h1]
  congr 1
  exact ht.symm

def fstFun (c : Γ(T, ⊤)) (W : (XT).Opens) : Γ(C₁T, (i₁T) ⁻¹ᵁ W) :=
  (pullback.snd c₁ h).appLE ⊤ ((i₁T) ⁻¹ᵁ W) le_top c

lemma nodeSectionFst_snd (i : ι) : σ¹ i ≫ pullback.snd c₁ h = 𝟙 T := by
  simp only [nodeSectionFst, rigSection, pullback.lift_snd]

lemma appLE_fstFun (i : ι) (W : (XT).Opens) (c : Γ(T, ⊤)) :
    (σ¹ i).appLE ((i₁T) ⁻¹ᵁ W) (nl i W) inf_le_left (fstFun c W) =
      T.presheaf.map (homOfLE (le_top : nl i W ≤ ⊤)).op c := by
  unfold fstFun
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_comp_appLE]
  rw [appLE_congr_hom (nodeSectionFst_snd i) ⊤ (nl i W) _ le_top]
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
  rfl

lemma res_appTop_eq_fstFun (c : Γ(T, ⊤)) (W : (XT).Opens) :
    (C₁T).presheaf.map (homOfLE (le_top : (i₁T) ⁻¹ᵁ W ≤ ⊤)).op ((pullback.snd c₁ h).appTop c) =
      fstFun c W := rfl

lemma res_appTop_eq_sndFun (c : Γ(T, ⊤)) (W : (XT).Opens) :
    (C₂T).presheaf.map (homOfLE (le_top : (i₂T) ⁻¹ᵁ W ≤ ⊤)).op ((pullback.snd c₂ h).appTop c) =
      sndFun c W := rfl

lemma appTop_nodeSectionFst_appTop (i : ι) (d : Γ(T, ⊤)) :
    (σ¹ i).appTop ((pullback.snd c₁ h).appTop d) = d := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, nodeSectionFst_snd, Scheme.Hom.id_appTop]
  rfl

lemma appTop_nodeSectionSnd_appTop (i : ι) (d : Γ(T, ⊤)) :
    (σ² i).appTop ((pullback.snd c₂ h).appTop d) = d := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, nodeSectionSnd_snd, Scheme.Hom.id_appTop]
  rfl

lemma nodeLocus_eq_top (hnode : ∀ i, (p₁ i).1 ≫ i₁.1 = (p₂ i).1 ≫ i₂.1) {V : X.Opens} {i : ι}
    (hi : nodePt i₁ p₁ i ∈ V) : nl i ((pullback.fst x h) ⁻¹ᵁ V) = ⊤ := by
  have hν := nodeSectionFst_comp_eq_nodeSectionSnd_comp (x := x) (i₁ := i₁) (i₂ := i₂) (h := h) hnode i
  rw [eq_top_iff]
  intro t _
  have e : (i₂T).base ((σ² i).base t) = (i₁T).base ((σ¹ i).base t) := by
    have := congrArg (fun φ : T ⟶ XT => φ.base t) hν
    simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply] at this
    exact this.symm
  refine ⟨?_, ?_⟩
  · change (pullback.fst x h).base ((i₁T).base ((σ¹ i).base t)) ∈ V
    rw [nodeSectionFst_curveChange_fst_apply]
    exact hi
  · change (pullback.fst x h).base ((i₂T).base ((σ² i).base t)) ∈ V
    rw [e, nodeSectionFst_curveChange_fst_apply]
    exact hi

lemma map_injective_of_eq_top {Y : Scheme.{u}} {U : Y.Opens} (hU : U = ⊤) :
    Function.Injective (Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) := by
  subst hU
  intro a b hab
  rwa [map_top_top, map_top_top] at hab

end TwoGluedCurvesNodeUnitAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_exists_eq_mul_of_iso.TwoGluedCurvesFrameAux P2MW.S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_exists_eq_mul_of_iso.TwoGluedCurvesNodeUnitAux"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_exists_eq_mul_of_iso.TwoGluedCurvesFrameAux P2MW.S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_exists_eq_mul_of_iso.TwoGluedCurvesNodeUnitAux"

open TwoGluedCurvesNodeUnitAux TwoGluedCurvesFrameAux in
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
    [IsProper c₁] [IsIntegral C₁] [IsProper c₂] [IsIntegral C₂]
    {u u' : ι → Γ(Spec (.of κ), ⊤)ˣ} {M M' : (pullback x (𝟙 (Spec (.of κ)))).Modules}
    (hM : Scheme.Modules.IsInvertible M) (hM' : Scheme.Modules.IsInvertible M')
    (hu : IsNodeUnitModule x i₁ i₂ p₁ p₂ (𝟙 _) u M) (hu' : IsNodeUnitModule x i₁ i₂ p₁ p₂ (𝟙 _) u' M')
    (e : Nonempty (M ≅ M')) :
    ∃ c : Γ(Spec (.of κ), ⊤)ˣ, ∀ j, u' j = c * u j := by
  classical
  obtain ⟨θ⟩ := e
  obtain ⟨j₁, j₂, hj⟩ := hu
  obtain ⟨j₁', j₂', hj'⟩ := hu'

  have hk := injective_and_range_comp_iso (x := x) (i₁ := i₁) (i₂ := i₂) (p₁ := p₁) (p₂ := p₂) θ u' j₁' j₂' hj'

  have hO := AlgebraicGeometry.TwoGluedCurves.isNodeUnitModule_one_unit κ x i₁ i₂ hjs p₁ p₂ hinj hnode hinter
    hcr (𝟙 _)

  obtain ⟨a₁, ha₁, key₁⟩ := exists_ratio_fst u hinj hO j₁ j₂ hj u' (θ.hom ≫ j₁') (θ.hom ≫ j₂') hk
  obtain ⟨a₂, ha₂, key₂⟩ := exists_ratio_snd u hinj hO j₁ j₂ hj u' (θ.hom ≫ j₁') (θ.hom ≫ j₂') hk

  obtain ⟨d₁, hd₁⟩ := exists_eq_appTop_snd (κ := κ) c₁ a₁
  obtain ⟨d₂, hd₂⟩ := exists_eq_appTop_snd (κ := κ) c₂ a₂
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨j₀⟩⟩
  · exact ⟨1, fun j => (IsEmpty.false j).elim⟩
  have hd₁u : IsUnit d₁ := by
    rw [← appTop_nodeSectionFst_appTop (p₁ := p₁) j₀ d₁, ← hd₁]; exact ha₁.map _
  have hd₂u : IsUnit d₂ := by
    rw [← appTop_nodeSectionSnd_appTop (p₂ := p₂) j₀ d₂, ← hd₂]; exact ha₂.map _
  refine ⟨hd₁u.unit * hd₂u.unit⁻¹, fun j => ?_⟩

  obtain ⟨V, v, hqV, hV⟩ := exists_open_sameUnit (i₁ := i₁) u hinj (nodePt i₁ p₁ j)
  have hvj : u j = v := hV j hqV
  obtain ⟨m₀, -, h1, h2⟩ := exists_isFrame u j₁ j₂ hj hO hV

  have hk₁ : fn₁ _ ((θ.hom ≫ j₁').app _ m₀) = fstFun d₁ ((pullback.fst x (𝟙 _)) ⁻¹ᵁ V) := by
    rw [key₁, h1, one_mul, hd₁, res_appTop_eq_fstFun]
  have hk₂ : fn₂ _ ((θ.hom ≫ j₂').app _ m₀) =
      sndFun (((v⁻¹ : Γ(Spec (.of κ), ⊤)ˣ) : Γ(Spec (.of κ), ⊤)) * d₂) ((pullback.fst x (𝟙 _)) ⁻¹ᵁ V) := by
    rw [key₂, h2, hd₂, res_appTop_eq_sndFun, ← sndFun_mul]

  have hnc : NodeCondition x i₁ i₂ p₁ p₂ (𝟙 _) u' ((pullback.fst x (𝟙 _)) ⁻¹ᵁ V) j
      (fn₁ _ ((θ.hom ≫ j₁').app _ m₀)) (fn₂ _ ((θ.hom ≫ j₂').app _ m₀)) := by
    have : ((θ.hom ≫ j₁').app _ m₀, (θ.hom ≫ j₂').app _ m₀) ∈
        Set.range (fun m : Γ(M, (pullback.fst x (𝟙 _)) ⁻¹ᵁ V) =>
          ((θ.hom ≫ j₁').app _ m, (θ.hom ≫ j₂').app _ m)) :=
      ⟨m₀, rfl⟩
    rw [(hk _).2] at this
    exact this j
  rw [hk₁, hk₂, nodeCondition_iff, appLE_fstFun, appLE_sndFun, ures, ← map_mul] at hnc

  have hd : d₁ = (u' j : Γ(Spec (.of κ), ⊤)) * (((v⁻¹ : Γ(Spec (.of κ), ⊤)ˣ) : Γ(Spec (.of κ), ⊤)) * d₂) :=
    map_injective_of_eq_top (nodeLocus_eq_top (x := x) (i₂ := i₂) (p₂ := p₂) (h := 𝟙 _) hnode hqV) hnc

  rw [mul_right_comm, eq_mul_inv_iff_mul_eq]
  ext
  rw [Units.val_mul, Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec, hd, hvj, mul_assoc, mul_assoc,
    mul_comm d₂, Units.inv_mul_cancel_left]

end S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_exists_eq_mul_of_iso
end P2MW
export P2MW.S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_exists_eq_mul_of_iso (solution)
