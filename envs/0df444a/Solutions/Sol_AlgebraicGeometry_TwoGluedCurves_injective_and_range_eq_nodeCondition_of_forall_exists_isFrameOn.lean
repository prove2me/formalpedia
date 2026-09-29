-- Prove2me | solution 1 for AlgebraicGeometry.TwoGluedCurves.injective_and_range_eq_nodeCondition_of_forall_exists_isFrameOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/9e14f8db-249f-596d-999a-6c02ae74b0b1

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_TwoGluedCurvesNodeUnitModule
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_isNodeUnitModule_one_unit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_TwoGluedCurves_injective_and_range_eq_nodeCondition_of_forall_exists_isFrameOn

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.TwoGluedCurves Opposite TopologicalSpace

noncomputable section

namespace TwoGluedCurvesSubsheafAux

variable {Y : Scheme.{u}} {P₁ P₂ : Y.Modules}

def resPair {W W' : Y.Opens} (h : W' ≤ W) (p : Γ(P₁, W) × Γ(P₂, W)) : Γ(P₁, W') × Γ(P₂, W') :=
  (P₁.presheaf.map (homOfLE h).op p.1, P₂.presheaf.map (homOfLE h).op p.2)

lemma resPair_refl {W : Y.Opens} (p : Γ(P₁, W) × Γ(P₂, W)) : resPair le_rfl p = p := by
  have h : (homOfLE (le_rfl : W ≤ W)).op = 𝟙 (op W) := rfl
  simp only [resPair, h, CategoryTheory.Functor.map_id]
  rfl

lemma resPair_resPair {W W' W'' : Y.Opens} (h : W' ≤ W) (h' : W'' ≤ W') (p : Γ(P₁, W) × Γ(P₂, W)) :
    resPair h' (resPair h p) = resPair (h'.trans h) p := by
  simp only [resPair, Prod.mk.injEq]
  constructor <;>
  · rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl

lemma resPair_add {W W' : Y.Opens} (h : W' ≤ W) (p q : Γ(P₁, W) × Γ(P₂, W)) :
    resPair h (p + q) = resPair h p + resPair h q := by
  simp only [resPair, Prod.fst_add, Prod.snd_add, map_add, Prod.mk_add_mk]

lemma resPair_smul {W W' : Y.Opens} (h : W' ≤ W) (r : Γ(Y, W)) (p : Γ(P₁, W) × Γ(P₂, W)) :
    resPair h (r • p) = Y.presheaf.map (homOfLE h).op r • resPair h p := by
  simp only [resPair, Prod.smul_fst, Prod.smul_snd, Scheme.Modules.map_smul, Prod.smul_mk]

variable (P₁ P₂) in

structure IsLocalSubmoduleFamily (S : ∀ W : Y.Opens, Set (Γ(P₁, W) × Γ(P₂, W))) : Prop where
  zero_mem : ∀ W, (0 : Γ(P₁, W) × Γ(P₂, W)) ∈ S W
  add_mem : ∀ W (p q : Γ(P₁, W) × Γ(P₂, W)), p ∈ S W → q ∈ S W → p + q ∈ S W
  smul_mem : ∀ W (r : Γ(Y, W)) (p : Γ(P₁, W) × Γ(P₂, W)), p ∈ S W → r • p ∈ S W
  res : ∀ {W W' : Y.Opens} (h : W' ≤ W) (p : Γ(P₁, W) × Γ(P₂, W)), p ∈ S W → resPair h p ∈ S W'
  glue : ∀ {ι : Type u} (U : ι → Y.Opens) (p : Γ(P₁, iSup U) × Γ(P₂, iSup U)),
    (∀ i, resPair (le_iSup U i) p ∈ S (U i)) → p ∈ S (iSup U)

variable {S : ∀ W : Y.Opens, Set (Γ(P₁, W) × Γ(P₂, W))} (hS : IsLocalSubmoduleFamily P₁ P₂ S)

def subMod (W : Y.Opens) : Submodule Γ(Y, W) (Γ(P₁, W) × Γ(P₂, W)) where
  carrier := S W
  zero_mem' := hS.zero_mem W
  add_mem' := fun {p q} hp hq => hS.add_mem W p q hp hq
  smul_mem' := fun r {p} hp => hS.smul_mem W r p hp

lemma mem_subMod {W : Y.Opens} (p : Γ(P₁, W) × Γ(P₂, W)) : p ∈ subMod hS W ↔ p ∈ S W := Iff.rfl

def subRes {W W' : Y.Opens} (h : W' ≤ W) : subMod hS W →+ subMod hS W' where
  toFun p := ⟨resPair h p.1, hS.res h p.1 p.2⟩
  map_zero' := by
    apply Subtype.ext
    change resPair h 0 = 0
    simp only [resPair, Prod.fst_zero, Prod.snd_zero, map_zero, Prod.mk_zero_zero]
  map_add' p q := by
    apply Subtype.ext
    exact resPair_add h p.1 q.1

def subPresheaf : TopCat.Presheaf Ab Y where
  obj W := AddCommGrpCat.of (subMod hS W.unop)
  map i := AddCommGrpCat.ofHom (subRes hS i.unop.le)
  map_id _ := AddCommGrpCat.hom_ext (AddMonoidHom.ext fun p => Subtype.ext (resPair_refl p.1))
  map_comp i i' := AddCommGrpCat.hom_ext (AddMonoidHom.ext fun p =>
    Subtype.ext (resPair_resPair i.unop.le i'.unop.le p.1).symm)

@[scoped simp] lemma subPresheaf_map_apply_val {W W' : (Y.Opens)ᵒᵖ} (i : W ⟶ W') (p : subMod hS W.unop) :
    ((subPresheaf hS).map i p).1 = resPair i.unop.le p.1 := rfl

scoped instance (W : (Y.Opens)ᵒᵖ) : Module (Y.ringCatSheaf.obj.obj W) ((subPresheaf hS).obj W) :=
  inferInstanceAs (Module Γ(Y, W.unop) (subMod hS W.unop))

lemma subPresheaf_map_smul {W W' : (Y.Opens)ᵒᵖ} (i : W ⟶ W') (r : Y.ringCatSheaf.obj.obj W)
    (m : (subPresheaf hS).obj W) :
    (subPresheaf hS).map i (r • m) = Y.ringCatSheaf.obj.map i r • (subPresheaf hS).map i m := by
  apply Subtype.ext
  exact resPair_smul i.unop.le r m.1

def subPMod : Y.PresheafOfModules :=
  PresheafOfModules.ofPresheaf (subPresheaf hS) (fun _ _ i r m => subPresheaf_map_smul hS i r m)

theorem isSheaf_subPresheaf : (subPresheaf hS).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  let F₁ : TopCat.Sheaf Ab Y := ⟨P₁.presheaf, P₁.isSheaf⟩
  let F₂ : TopCat.Sheaf Ab Y := ⟨P₂.presheaf, P₂.isSheaf⟩

  have h₁ : TopCat.Presheaf.IsCompatible F₁.1 U (fun i => (sf i).1.1) := fun i j =>
    congrArg (fun p => p.1.1) (hsf i j)
  have h₂ : TopCat.Presheaf.IsCompatible F₂.1 U (fun i => (sf i).1.2) := fun i j =>
    congrArg (fun p => p.1.2) (hsf i j)
  obtain ⟨g₁, hg₁, hg₁u⟩ := F₁.existsUnique_gluing U _ h₁
  obtain ⟨g₂, hg₂, hg₂u⟩ := F₂.existsUnique_gluing U _ h₂
  have hmem : (g₁, g₂) ∈ S (iSup U) := by
    refine hS.glue U (g₁, g₂) fun i => ?_
    have : resPair (le_iSup U i) (g₁, g₂) = (sf i).1 := Prod.ext (hg₁ i) (hg₂ i)
    rw [this]
    exact (sf i).2
  refine ⟨⟨(g₁, g₂), hmem⟩, fun i => Subtype.ext (Prod.ext (hg₁ i) (hg₂ i)), ?_⟩
  intro s hs
  apply Subtype.ext
  exact Prod.ext (hg₁u _ fun i => congrArg (fun p => p.1.1) (hs i))
    (hg₂u _ fun i => congrArg (fun p => p.1.2) (hs i))

def subModule : Y.Modules :=
  show SheafOfModules Y.ringCatSheaf from ⟨subPMod hS, isSheaf_subPresheaf hS⟩

def fstPresheafHom : (subModule hS).presheaf ⟶ P₁.presheaf where
  app W := AddCommGrpCat.ofHom
    { toFun := fun p : subMod hS W.unop => p.1.1
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  naturality W W' i := by ext p; rfl

def sndPresheafHom : (subModule hS).presheaf ⟶ P₂.presheaf where
  app W := AddCommGrpCat.ofHom
    { toFun := fun p : subMod hS W.unop => p.1.2
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  naturality W W' i := by ext p; rfl

def fstHom : subModule hS ⟶ P₁ :=
  ⟨PresheafOfModules.homMk (fstPresheafHom hS) (fun _ _ _ => rfl)⟩

def sndHom : subModule hS ⟶ P₂ :=
  ⟨PresheafOfModules.homMk (sndPresheafHom hS) (fun _ _ _ => rfl)⟩

@[scoped simp] lemma fstHom_app (W : Y.Opens) (m : Γ(subModule hS, W)) :
    (fstHom hS).app W m = (show subMod hS W from m).1.1 := rfl

@[scoped simp] lemma sndHom_app (W : Y.Opens) (m : Γ(subModule hS, W)) :
    (sndHom hS).app W m = (show subMod hS W from m).1.2 := rfl

theorem exists_injective_and_range_eq (S : ∀ W : Y.Opens, Set (Γ(P₁, W) × Γ(P₂, W)))
    (hS : IsLocalSubmoduleFamily P₁ P₂ S) :
    ∃ (M : Y.Modules) (j₁ : M ⟶ P₁) (j₂ : M ⟶ P₂), ∀ W : Y.Opens,
      Function.Injective (fun m : Γ(M, W) => (j₁.app W m, j₂.app W m)) ∧
      Set.range (fun m : Γ(M, W) => (j₁.app W m, j₂.app W m)) = S W := by
  refine ⟨subModule hS, fstHom hS, sndHom hS, fun W => ⟨?_, ?_⟩⟩
  · intro m m' h
    exact Subtype.ext h
  · ext p
    constructor
    · rintro ⟨m, rfl⟩
      exact (show subMod hS W from m).2
    · intro hp
      exact ⟨(show subMod hS W from ⟨p, hp⟩), rfl⟩

end TwoGluedCurvesSubsheafAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedCurves_injective_and_range_eq_nodeCondition_of_forall_exists_isFrameOn.TwoGluedCurvesSubsheafAux"

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
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedCurves_injective_and_range_eq_nodeCondition_of_forall_exists_isFrameOn.TwoGluedCurvesSubsheafAux P2MW.S_AlgebraicGeometry_TwoGluedCurves_injective_and_range_eq_nodeCondition_of_forall_exists_isFrameOn.TwoGluedCurvesFrameAux"

namespace TwoGluedCurvesNodeUnitAux

open TwoGluedCurvesSubsheafAux TwoGluedCurvesFrameAux

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

def nodeFamily (W : (XT).Opens) : Set (Γ(P¹, W) × Γ(P², W)) :=
  {fg | ∀ i : ι, NodeCondition x i₁ i₂ p₁ p₂ h u W i (fn₁ W fg.1) (fn₂ W fg.2)}

lemma nodeFamily_eq (W : (XT).Opens) :
    nodeFamily (i₁ := i₁) (i₂ := i₂) (p₁ := p₁) (p₂ := p₂) u W =
      {fg | ∀ i : ι, NodeCondition x i₁ i₂ p₁ p₂ h u W i fg.1 fg.2} := rfl

theorem nodeFamily_res {W W' : (XT).Opens} (hW : W' ≤ W) (p : Γ(P¹, W) × Γ(P², W))
    (hp : p ∈ nodeFamily (i₁ := i₁) (i₂ := i₂) (p₁ := p₁) (p₂ := p₂) u W) :
    resPair hW p ∈ nodeFamily (i₁ := i₁) (i₂ := i₂) (p₁ := p₁) (p₂ := p₂) u W' := by
  intro i
  change NodeCondition x i₁ i₂ p₁ p₂ h u W' i (fn₁ W' ((P¹).presheaf.map (homOfLE hW).op p.1))
    (fn₂ W' ((P²).presheaf.map (homOfLE hW).op p.2))
  rw [fn₁_map, fn₂_map]
  exact nodeCondition_res u i hW _ _ (hp i)

theorem nodeFamily_zero (W : (XT).Opens) :
    (0 : Γ(P¹, W) × Γ(P², W)) ∈ nodeFamily (i₁ := i₁) (i₂ := i₂) (p₁ := p₁) (p₂ := p₂) u W := by
  intro i
  change NodeCondition x i₁ i₂ p₁ p₂ h u W i (fn₁ W 0) (fn₂ W 0)
  unfold NodeCondition
  rw [fn₁_zero, fn₂_zero, map_zero, map_zero, mul_zero]

theorem nodeFamily_add (W : (XT).Opens) (p q : Γ(P¹, W) × Γ(P², W))
    (hp : p ∈ nodeFamily (i₁ := i₁) (i₂ := i₂) (p₁ := p₁) (p₂ := p₂) u W)
    (hq : q ∈ nodeFamily (i₁ := i₁) (i₂ := i₂) (p₁ := p₁) (p₂ := p₂) u W) :
    p + q ∈ nodeFamily (i₁ := i₁) (i₂ := i₂) (p₁ := p₁) (p₂ := p₂) u W := by
  intro i
  have hp' := hp i
  have hq' := hq i
  change NodeCondition x i₁ i₂ p₁ p₂ h u W i (fn₁ W (p.1 + q.1)) (fn₂ W (p.2 + q.2))
  unfold NodeCondition at hp' hq' ⊢
  rw [fn₁_add, fn₂_add, map_add, map_add, mul_add, hp', hq']

theorem nodeFamily_smul
    (hν : ∀ i : ι, nodeSectionFst p₁ h i ≫ curveChange i₁.1 i₁.2 h =
      nodeSectionSnd p₂ h i ≫ curveChange i₂.1 i₂.2 h)
    (W : (XT).Opens) (r : Γ(XT, W)) (p : Γ(P¹, W) × Γ(P², W))
    (hp : p ∈ nodeFamily (i₁ := i₁) (i₂ := i₂) (p₁ := p₁) (p₂ := p₂) u W) :
    r • p ∈ nodeFamily (i₁ := i₁) (i₂ := i₂) (p₁ := p₁) (p₂ := p₂) u W := by
  intro i
  have hp' := hp i
  change NodeCondition x i₁ i₂ p₁ p₂ h u W i (fn₁ W (r • p.1)) (fn₂ W (r • p.2))
  unfold NodeCondition at hp' ⊢
  rw [fn₁_smul, fn₂_smul, map_mul, map_mul, hp', appLE_fst_app_eq_appLE_snd_app hν i W r]
  ring

lemma nodeLocus_eq
    (hν : ∀ i : ι, nodeSectionFst p₁ h i ≫ curveChange i₁.1 i₁.2 h =
      nodeSectionSnd p₂ h i ≫ curveChange i₂.1 i₂.2 h)
    (i : ι) (W : (XT).Opens) : nl i W = ((σ¹ i) ≫ (i₁T)) ⁻¹ᵁ W := by
  change (σ¹ i) ⁻¹ᵁ ((i₁T) ⁻¹ᵁ W) ⊓ (σ² i) ⁻¹ᵁ ((i₂T) ⁻¹ᵁ W) = _
  have h1 : (σ¹ i) ⁻¹ᵁ ((i₁T) ⁻¹ᵁ W) = ((σ¹ i) ≫ (i₁T)) ⁻¹ᵁ W := rfl
  have h2 : (σ² i) ⁻¹ᵁ ((i₂T) ⁻¹ᵁ W) = ((σ² i) ≫ (i₂T)) ⁻¹ᵁ W := rfl
  rw [h1, h2, ← hν i, inf_idem]

lemma nodeLocus_iSup_le
    (hν : ∀ i : ι, nodeSectionFst p₁ h i ≫ curveChange i₁.1 i₁.2 h =
      nodeSectionSnd p₂ h i ≫ curveChange i₂.1 i₂.2 h)
    (i : ι) {ι' : Type u} (U : ι' → (XT).Opens) :
    nl i (iSup U) ≤ ⨆ k, nl i (U k) := by
  rw [nodeLocus_eq hν, Scheme.Hom.preimage_iSup]
  refine iSup_le fun k => ?_
  rw [← nodeLocus_eq hν]
  exact le_iSup (fun k => nl i (U k)) k

theorem nodeCondition_glue
    (hν : ∀ i : ι, nodeSectionFst p₁ h i ≫ curveChange i₁.1 i₁.2 h =
      nodeSectionSnd p₂ h i ≫ curveChange i₂.1 i₂.2 h)
    (i : ι) {ι' : Type u} (U : ι' → (XT).Opens)
    (f : Γ(C₁T, (i₁T) ⁻¹ᵁ (iSup U))) (g : Γ(C₂T, (i₂T) ⁻¹ᵁ (iSup U)))
    (hloc : ∀ k, NodeCondition x i₁ i₂ p₁ p₂ h u (U k) i
      ((C₁T).presheaf.map (homOfLE (preimage_mono (i₁T) (le_iSup U k))).op f)
      ((C₂T).presheaf.map (homOfLE (preimage_mono (i₂T) (le_iSup U k))).op g)) :
    NodeCondition x i₁ i₂ p₁ p₂ h u (iSup U) i f g := by
  unfold NodeCondition at hloc ⊢
  refine TopCat.Sheaf.eq_of_locally_eq' T.sheaf (fun k => nl i (U k)) (nl i (iSup U))
    (fun k => homOfLE (nodeLocus_mono i (le_iSup U k))) (nodeLocus_iSup_le hν i U) _ _ fun k => ?_
  have := hloc k
  rw [appLE_fst_res i (le_iSup U k) f, appLE_snd_res i (le_iSup U k) g] at this
  change T.presheaf.map _ _ = T.presheaf.map _ _
  rw [this, map_mul, unit_res u]

theorem nodeFamily_glue
    (hν : ∀ i : ι, nodeSectionFst p₁ h i ≫ curveChange i₁.1 i₁.2 h =
      nodeSectionSnd p₂ h i ≫ curveChange i₂.1 i₂.2 h)
    {ι' : Type u} (U : ι' → (XT).Opens) (p : Γ(P¹, iSup U) × Γ(P², iSup U))
    (hp : ∀ k, resPair (le_iSup U k) p ∈ nodeFamily (i₁ := i₁) (i₂ := i₂) (p₁ := p₁) (p₂ := p₂) u (U k)) :
    p ∈ nodeFamily (i₁ := i₁) (i₂ := i₂) (p₁ := p₁) (p₂ := p₂) u (iSup U) := by
  intro i
  refine nodeCondition_glue u hν i U (fn₁ _ p.1) (fn₂ _ p.2) fun k => ?_
  rw [← fn₁_map, ← fn₂_map]
  exact hp k i

theorem isLocalSubmoduleFamily_nodeFamily
    (hν : ∀ i : ι, nodeSectionFst p₁ h i ≫ curveChange i₁.1 i₁.2 h =
      nodeSectionSnd p₂ h i ≫ curveChange i₂.1 i₂.2 h) :
    IsLocalSubmoduleFamily (P¹) (P²) (nodeFamily (i₁ := i₁) (i₂ := i₂) (p₁ := p₁) (p₂ := p₂) u) where
  zero_mem := nodeFamily_zero u
  add_mem := nodeFamily_add u
  smul_mem := nodeFamily_smul u hν
  res := nodeFamily_res u
  glue := nodeFamily_glue u hν

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

theorem exists_isNodeUnitModule
    (hnode : ∀ i, (p₁ i).1 ≫ i₁.1 = (p₂ i).1 ≫ i₂.1) :
    ∃ M : (XT).Modules, IsNodeUnitModule x i₁ i₂ p₁ p₂ h u M := by
  have hν := nodeSectionFst_comp_eq_nodeSectionSnd_comp (x := x) (i₁ := i₁) (i₂ := i₂) (h := h) hnode
  obtain ⟨M, j₁, j₂, hj⟩ := TwoGluedCurvesSubsheafAux.exists_injective_and_range_eq _
    (isLocalSubmoduleFamily_nodeFamily u hν)
  exact ⟨M, j₁, j₂, fun W => hj W⟩

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
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedCurves_injective_and_range_eq_nodeCondition_of_forall_exists_isFrameOn.TwoGluedCurvesSubsheafAux P2MW.S_AlgebraicGeometry_TwoGluedCurves_injective_and_range_eq_nodeCondition_of_forall_exists_isFrameOn.TwoGluedCurvesFrameAux"

section Criterion

variable (hO : IsNodeUnitModule x i₁ i₂ p₁ p₂ h 1 (unitMod (pullback x h)))
  (hν : ∀ i : ι, nodeSectionFst p₁ h i ≫ curveChange i₁.1 i₁.2 h =
    nodeSectionSnd p₂ h i ≫ curveChange i₂.1 i₂.2 h)
  {N : (pullback x h).Modules}
  (J₁ : N ⟶ (Scheme.Modules.pushforward (curveChange i₁.1 i₁.2 h)).obj
    (SheafOfModules.unit (pullback c₁ h).ringCatSheaf))
  (J₂ : N ⟶ (Scheme.Modules.pushforward (curveChange i₂.1 i₂.2 h)).obj
    (SheafOfModules.unit (pullback c₂ h).ringCatSheaf))

lemma isUnit_ures (i : ι) (V : T.Opens) : IsUnit (ures u i V) := (Units.isUnit (u i)).map _

lemma nodeCondition_one_mul_u (W : (XT).Opens) (i : ι) {f f' : Γ(C₁T, (i₁T) ⁻¹ᵁ W)}
    {g g' : Γ(C₂T, (i₂T) ⁻¹ᵁ W)}
    (hfg : NodeCondition x i₁ i₂ p₁ p₂ h 1 W i f g) (hfg' : NodeCondition x i₁ i₂ p₁ p₂ h u W i f' g') :
    NodeCondition x i₁ i₂ p₁ p₂ h u W i (f * f') (g * g') := by
  rw [nodeCondition_one_iff] at hfg
  rw [nodeCondition_iff] at hfg' ⊢
  rw [map_mul, map_mul, hfg, hfg']
  ring

lemma nodeCondition_one_of_mul (W : (XT).Opens) (i : ι) {f' v₁ : Γ(C₁T, (i₁T) ⁻¹ᵁ W)}
    {g' v₂ : Γ(C₂T, (i₂T) ⁻¹ᵁ W)} (hv₂ : IsUnit v₂)
    (hfg : NodeCondition x i₁ i₂ p₁ p₂ h u W i (f' * v₁) (g' * v₂))
    (hv : NodeCondition x i₁ i₂ p₁ p₂ h u W i v₁ v₂) :
    NodeCondition x i₁ i₂ p₁ p₂ h 1 W i f' g' := by
  rw [nodeCondition_one_iff]
  rw [nodeCondition_iff] at hfg hv
  rw [map_mul, map_mul, hv] at hfg
  have hu : IsUnit (ures u i (nl i W) * (σ² i).appLE ((i₂T) ⁻¹ᵁ W) (nl i W) inf_le_right v₂) :=
    (isUnit_ures u i _).mul (hv₂.map _)
  apply hu.mul_right_cancel
  rw [hfg]
  ring

lemma app_map {M M' : (XT).Modules} (φ : M ⟶ M') {W W' : (XT).Opens} (hW : W' ≤ W) (n : Γ(M, W)) :
    φ.app W' (M.presheaf.map (homOfLE hW).op n) = M'.presheaf.map (homOfLE hW).op (φ.app W n) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE hW).op) n

section Local

variable {W : (pullback x h).Opens} {e : Γ(N, W)}
  {v₁ : Γ(pullback c₁ h, (curveChange i₁.1 i₁.2 h) ⁻¹ᵁ W)} {v₂ : Γ(pullback c₂ h, (curveChange i₂.1 i₂.2 h) ⁻¹ᵁ W)}
  (hfr : Scheme.Modules.IsFrameOn e W) (he₁ : fn₁ W (J₁.app W e) = v₁) (he₂ : fn₂ W (J₂.app W e) = v₂)
  (hv₁ : IsUnit v₁) (hv₂ : IsUnit v₂)
  (hNC : ∀ i, NodeCondition x i₁ i₂ p₁ p₂ h u W i v₁ v₂)

include he₁ in

lemma fn₁_app_smul_map {W' : (XT).Opens} (hW' : W' ≤ W) (g : Γ(XT, W')) :
    fn₁ W' (J₁.app W' (g • N.presheaf.map (homOfLE hW').op e)) =
      (i₁T).app W' g * (C₁T).presheaf.map (homOfLE (preimage_mono (i₁T) hW')).op v₁ := by
  rw [Scheme.Modules.Hom.app_smul, fn₁_smul, app_map, fn₁_map, he₁]

include he₂ in

lemma fn₂_app_smul_map {W' : (XT).Opens} (hW' : W' ≤ W) (g : Γ(XT, W')) :
    fn₂ W' (J₂.app W' (g • N.presheaf.map (homOfLE hW').op e)) =
      (i₂T).app W' g * (C₂T).presheaf.map (homOfLE (preimage_mono (i₂T) hW')).op v₂ := by
  rw [Scheme.Modules.Hom.app_smul, fn₂_smul, app_map, fn₂_map, he₂]

include hO hfr he₁ he₂ hv₁ hv₂ in

lemma injective_local {W' : (XT).Opens} (hW' : W' ≤ W) :
    Function.Injective (fun m : Γ(N, W') => (J₁.app W' m, J₂.app W' m)) := by
  intro m m' hmm'
  obtain ⟨g, rfl⟩ := (hfr.bijective hW' hW').2 m
  obtain ⟨g', rfl⟩ := (hfr.bijective hW' hW').2 m'
  have e₁ := congrArg (fun q => fn₁ W' q.1) hmm'
  have e₂ := congrArg (fun q => fn₂ W' q.2) hmm'
  dsimp only at e₁ e₂
  rw [fn₁_app_smul_map J₁ he₁, fn₁_app_smul_map J₁ he₁] at e₁
  rw [fn₂_app_smul_map J₂ he₂, fn₂_app_smul_map J₂ he₂] at e₂
  have hg : g = g' := (conductor hO W').1 (Prod.ext ((hv₁.map _).mul_left_injective e₁)
    ((hv₂.map _).mul_left_injective e₂))
  rw [hg]

include hν hfr he₁ he₂ hNC in

lemma nodeCondition_local {W' : (XT).Opens} (hW' : W' ≤ W) (m : Γ(N, W')) (i : ι) :
    NodeCondition x i₁ i₂ p₁ p₂ h u W' i (fn₁ W' (J₁.app W' m)) (fn₂ W' (J₂.app W' m)) := by
  obtain ⟨g, rfl⟩ := (hfr.bijective hW' hW').2 m
  dsimp only
  rw [fn₁_app_smul_map J₁ he₁, fn₂_app_smul_map J₂ he₂]
  refine nodeCondition_one_mul_u u W' i ?_ (nodeCondition_res u i hW' v₁ v₂ (hNC i))
  rw [nodeCondition_one_iff]
  exact appLE_fst_app_eq_appLE_snd_app hν i W' g

include hO hν hfr he₁ he₂ hv₁ hv₂ hNC in

lemma exists_local {W' : (XT).Opens} (hW' : W' ≤ W) (f : Γ(C₁T, (i₁T) ⁻¹ᵁ W')) (g : Γ(C₂T, (i₂T) ⁻¹ᵁ W'))
    (hfg : ∀ i, NodeCondition x i₁ i₂ p₁ p₂ h u W' i f g) :
    ∃ m : Γ(N, W'), fn₁ W' (J₁.app W' m) = f ∧ fn₂ W' (J₂.app W' m) = g := by

  set w₁ := (C₁T).presheaf.map (homOfLE (preimage_mono (i₁T) hW')).op v₁ with hw₁
  set w₂ := (C₂T).presheaf.map (homOfLE (preimage_mono (i₂T) hW')).op v₂ with hw₂
  have hw₁u : IsUnit w₁ := hv₁.map _
  have hw₂u : IsUnit w₂ := hv₂.map _
  have hwNC : ∀ i, NodeCondition x i₁ i₂ p₁ p₂ h u W' i w₁ w₂ := fun i => nodeCondition_res u i hW' v₁ v₂ (hNC i)

  have h1 : ∀ i, NodeCondition x i₁ i₂ p₁ p₂ h 1 W' i (f * ↑hw₁u.unit⁻¹) (g * ↑hw₂u.unit⁻¹) := by
    intro i
    refine nodeCondition_one_of_mul u W' i hw₂u ?_ (hwNC i)
    rw [mul_assoc, mul_assoc, IsUnit.val_inv_mul, IsUnit.val_inv_mul, mul_one, mul_one]
    exact hfg i
  obtain ⟨r, hr₁, hr₂⟩ := (conductor hO W').2 _ _ h1
  refine ⟨r • N.presheaf.map (homOfLE hW').op e, ?_, ?_⟩
  · rw [fn₁_app_smul_map J₁ he₁, hr₁, mul_assoc, IsUnit.val_inv_mul, mul_one]
  · rw [fn₂_app_smul_map J₂ he₂, hr₂, mul_assoc, IsUnit.val_inv_mul, mul_one]

end Local
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedCurves_injective_and_range_eq_nodeCondition_of_forall_exists_isFrameOn.TwoGluedCurvesSubsheafAux P2MW.S_AlgebraicGeometry_TwoGluedCurves_injective_and_range_eq_nodeCondition_of_forall_exists_isFrameOn.TwoGluedCurvesFrameAux"

include hO hν in

theorem injective_and_range_eq_iSup {ι' : Type u} (U : ι' → (XT).Opens)
    (W : ι' → (XT).Opens) (e : ∀ y, Γ(N, W y))
    (v₁ : ∀ y, Γ(C₁T, (i₁T) ⁻¹ᵁ W y)) (v₂ : ∀ y, Γ(C₂T, (i₂T) ⁻¹ᵁ W y))
    (hUW : ∀ y, U y ≤ W y) (hfr : ∀ y, Scheme.Modules.IsFrameOn (e y) (W y))
    (he₁ : ∀ y, fn₁ (W y) (J₁.app (W y) (e y)) = v₁ y) (he₂ : ∀ y, fn₂ (W y) (J₂.app (W y) (e y)) = v₂ y)
    (hv₁ : ∀ y, IsUnit (v₁ y)) (hv₂ : ∀ y, IsUnit (v₂ y))
    (hNC : ∀ y i, NodeCondition x i₁ i₂ p₁ p₂ h u (W y) i (v₁ y) (v₂ y)) :
    Function.Injective (fun m : Γ(N, iSup U) => (J₁.app (iSup U) m, J₂.app (iSup U) m)) ∧
      Set.range (fun m : Γ(N, iSup U) => (J₁.app (iSup U) m, J₂.app (iSup U) m)) =
        {fg | ∀ i : ι, NodeCondition x i₁ i₂ p₁ p₂ h u (iSup U) i (fn₁ _ fg.1) (fn₂ _ fg.2)} := by
  let F : TopCat.Sheaf Ab _ := ⟨N.presheaf, N.isSheaf⟩
  have hinj : Function.Injective (fun m : Γ(N, iSup U) => (J₁.app (iSup U) m, J₂.app (iSup U) m)) := by
    intro m m' hmm'
    refine F.eq_of_locally_eq U m m' fun y => ?_
    apply injective_local hO J₁ J₂ (hfr y) (he₁ y) (he₂ y) (hv₁ y) (hv₂ y) (hUW y)
    change (J₁.app (U y) (N.presheaf.map (homOfLE (le_iSup U y)).op m),
        J₂.app (U y) (N.presheaf.map (homOfLE (le_iSup U y)).op m)) =
      (J₁.app (U y) (N.presheaf.map (homOfLE (le_iSup U y)).op m'),
        J₂.app (U y) (N.presheaf.map (homOfLE (le_iSup U y)).op m'))
    rw [app_map, app_map, app_map, app_map]
    exact Prod.ext (congrArg (fun q => ((Scheme.Modules.pushforward (i₁T)).obj _).presheaf.map _ q.1) hmm')
      (congrArg (fun q => ((Scheme.Modules.pushforward (i₂T)).obj _).presheaf.map _ q.2) hmm')
  refine ⟨hinj, ?_⟩
  ext fg
  constructor
  ·
    rintro ⟨m, rfl⟩ i
    refine nodeCondition_glue u hν i U _ _ fun y => ?_
    rw [← fn₁_map (le_iSup U y), ← fn₂_map (le_iSup U y), ← app_map J₁ (le_iSup U y) m,
      ← app_map J₂ (le_iSup U y) m]
    exact nodeCondition_local u hν J₁ J₂ (hfr y) (he₁ y) (he₂ y) (hNC y) (hUW y) _ i
  ·
    intro hfg
    have hloc : ∀ y, ∃ m : Γ(N, U y),
        fn₁ (U y) (J₁.app (U y) m) = (C₁T).presheaf.map (homOfLE (preimage_mono (i₁T) (le_iSup U y))).op (fn₁ _ fg.1) ∧
        fn₂ (U y) (J₂.app (U y) m) = (C₂T).presheaf.map (homOfLE (preimage_mono (i₂T) (le_iSup U y))).op (fn₂ _ fg.2) :=
      fun y => exists_local u hO hν J₁ J₂ (hfr y) (he₁ y) (he₂ y) (hv₁ y) (hv₂ y) (hNC y) (hUW y) _ _
        fun i => nodeCondition_res u i (le_iSup U y) _ _ (hfg i)
    choose t ht₁ ht₂ using hloc
    have hcompat : TopCat.Presheaf.IsCompatible F.1 U t := by
      intro y y'
      apply injective_local hO J₁ J₂ (hfr y) (he₁ y) (he₂ y) (hv₁ y) (hv₂ y) (inf_le_left.trans (hUW y))
      change (J₁.app (U y ⊓ U y') (N.presheaf.map (homOfLE inf_le_left).op (t y)),
          J₂.app (U y ⊓ U y') (N.presheaf.map (homOfLE inf_le_left).op (t y))) =
        (J₁.app (U y ⊓ U y') (N.presheaf.map (homOfLE inf_le_right).op (t y')),
          J₂.app (U y ⊓ U y') (N.presheaf.map (homOfLE inf_le_right).op (t y')))
      refine Prod.ext ?_ ?_
      · dsimp only
        apply fn₁_injective
        rw [app_map, app_map, fn₁_map, fn₁_map, ht₁, ht₁, ← ConcreteCategory.comp_apply,
          ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
        rfl
      · dsimp only
        apply fn₂_injective
        rw [app_map, app_map, fn₂_map, fn₂_map, ht₂, ht₂, ← ConcreteCategory.comp_apply,
          ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
        rfl
    obtain ⟨m, hm, -⟩ := F.existsUnique_gluing U t hcompat
    refine ⟨m, Prod.ext ?_ ?_⟩
    · let F₁ : TopCat.Sheaf Ab _ := ⟨((Scheme.Modules.pushforward (i₁T)).obj
        (SheafOfModules.unit (pullback c₁ h).ringCatSheaf)).presheaf, Scheme.Modules.isSheaf _⟩
      refine F₁.eq_of_locally_eq U (J₁.app (iSup U) m) fg.1 fun y => ?_
      apply fn₁_injective
      change fn₁ (U y) (((Scheme.Modules.pushforward (i₁T)).obj _).presheaf.map (homOfLE (le_iSup U y)).op
          (J₁.app (iSup U) m)) =
        fn₁ (U y) (((Scheme.Modules.pushforward (i₁T)).obj _).presheaf.map (homOfLE (le_iSup U y)).op fg.1)
      rw [← app_map, fn₁_map]
      have := hm y
      change N.presheaf.map (homOfLE (le_iSup U y)).op m = t y at this
      rw [this, ht₁]
    · let F₂ : TopCat.Sheaf Ab _ := ⟨((Scheme.Modules.pushforward (i₂T)).obj
        (SheafOfModules.unit (pullback c₂ h).ringCatSheaf)).presheaf, Scheme.Modules.isSheaf _⟩
      refine F₂.eq_of_locally_eq U (J₂.app (iSup U) m) fg.2 fun y => ?_
      apply fn₂_injective
      change fn₂ (U y) (((Scheme.Modules.pushforward (i₂T)).obj _).presheaf.map (homOfLE (le_iSup U y)).op
          (J₂.app (iSup U) m)) =
        fn₂ (U y) (((Scheme.Modules.pushforward (i₂T)).obj _).presheaf.map (homOfLE (le_iSup U y)).op fg.2)
      rw [← app_map, fn₂_map]
      have := hm y
      change N.presheaf.map (homOfLE (le_iSup U y)).op m = t y at this
      rw [this, ht₂]

include hO hν in

theorem injective_and_range_eq
    (hloc : ∀ y : ↥(pullback x h), ∃ (W : (pullback x h).Opens) (e : Γ(N, W))
      (v₁ : Γ(pullback c₁ h, (curveChange i₁.1 i₁.2 h) ⁻¹ᵁ W)) (v₂ : Γ(pullback c₂ h, (curveChange i₂.1 i₂.2 h) ⁻¹ᵁ W)),
      y ∈ W ∧ Scheme.Modules.IsFrameOn e W ∧ J₁.app W e = v₁ ∧ J₂.app W e = v₂ ∧ IsUnit v₁ ∧ IsUnit v₂ ∧
      ∀ j, NodeCondition x i₁ i₂ p₁ p₂ h u W j v₁ v₂)
    (W₀ : (pullback x h).Opens) :
    Function.Injective (fun m : Γ(N, W₀) => (J₁.app W₀ m, J₂.app W₀ m)) ∧
      Set.range (fun m : Γ(N, W₀) => (J₁.app W₀ m, J₂.app W₀ m)) =
        {fg | ∀ i : ι, NodeCondition x i₁ i₂ p₁ p₂ h u W₀ i fg.1 fg.2} := by
  choose W e v₁ v₂ hyW hfr he₁ he₂ hv₁ hv₂ hNC using hloc
  obtain ⟨U, hU⟩ : ∃ U : ↥(pullback x h) → (pullback x h).Opens, ∀ y, U y = W₀ ⊓ W y := ⟨_, fun _ => rfl⟩
  have hUW₀ : iSup U = W₀ := by
    apply le_antisymm (iSup_le fun y => (hU y).le.trans inf_le_left)
    intro z hz
    exact Opens.mem_iSup.mpr ⟨z, (hU z).ge ⟨hz, hyW z⟩⟩
  rw [← hUW₀]
  exact injective_and_range_eq_iSup u hO hν J₁ J₂ U W e v₁ v₂ (fun y => (hU y).le.trans inf_le_right)
    hfr he₁ he₂ hv₁ hv₂ hNC

end Criterion
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedCurves_injective_and_range_eq_nodeCondition_of_forall_exists_isFrameOn.TwoGluedCurvesSubsheafAux P2MW.S_AlgebraicGeometry_TwoGluedCurves_injective_and_range_eq_nodeCondition_of_forall_exists_isFrameOn.TwoGluedCurvesFrameAux"

end TwoGluedCurvesNodeUnitAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedCurves_injective_and_range_eq_nodeCondition_of_forall_exists_isFrameOn.TwoGluedCurvesSubsheafAux P2MW.S_AlgebraicGeometry_TwoGluedCurves_injective_and_range_eq_nodeCondition_of_forall_exists_isFrameOn.TwoGluedCurvesFrameAux P2MW.S_AlgebraicGeometry_TwoGluedCurves_injective_and_range_eq_nodeCondition_of_forall_exists_isFrameOn.TwoGluedCurvesNodeUnitAux"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedCurves_injective_and_range_eq_nodeCondition_of_forall_exists_isFrameOn.TwoGluedCurvesSubsheafAux P2MW.S_AlgebraicGeometry_TwoGluedCurves_injective_and_range_eq_nodeCondition_of_forall_exists_isFrameOn.TwoGluedCurvesFrameAux P2MW.S_AlgebraicGeometry_TwoGluedCurves_injective_and_range_eq_nodeCondition_of_forall_exists_isFrameOn.TwoGluedCurvesNodeUnitAux"

open TwoGluedCurvesNodeUnitAux in
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
    {T : Scheme.{u}} {h : T ⟶ Spec (.of κ)} (u : ι → Γ(T, ⊤)ˣ) {N : (pullback x h).Modules}
    (J₁ : N ⟶ (Scheme.Modules.pushforward (curveChange i₁.1 i₁.2 h)).obj
      (SheafOfModules.unit (pullback c₁ h).ringCatSheaf))
    (J₂ : N ⟶ (Scheme.Modules.pushforward (curveChange i₂.1 i₂.2 h)).obj
      (SheafOfModules.unit (pullback c₂ h).ringCatSheaf))
    (hloc : ∀ y : ↥(pullback x h), ∃ (W : (pullback x h).Opens) (e : Γ(N, W))
      (v₁ : Γ(pullback c₁ h, (curveChange i₁.1 i₁.2 h) ⁻¹ᵁ W)) (v₂ : Γ(pullback c₂ h, (curveChange i₂.1 i₂.2 h) ⁻¹ᵁ W)),
      y ∈ W ∧ Scheme.Modules.IsFrameOn e W ∧ J₁.app W e = v₁ ∧ J₂.app W e = v₂ ∧ IsUnit v₁ ∧ IsUnit v₂ ∧
      ∀ j, NodeCondition x i₁ i₂ p₁ p₂ h u W j v₁ v₂) :
    ∀ W : (pullback x h).Opens,
      Function.Injective (fun m : Γ(N, W) => (J₁.app W m, J₂.app W m)) ∧
      Set.range (fun m : Γ(N, W) => (J₁.app W m, J₂.app W m)) =
        {fg | ∀ j : ι, NodeCondition x i₁ i₂ p₁ p₂ h u W j fg.1 fg.2} := by
  intro W₀
  have hO := AlgebraicGeometry.TwoGluedCurves.isNodeUnitModule_one_unit κ x i₁ i₂ hjs p₁ p₂ hinj hnode hinter
    hcr h
  have hν := nodeSectionFst_comp_eq_nodeSectionSnd_comp (x := x) (i₁ := i₁) (i₂ := i₂) (h := h) hnode
  exact injective_and_range_eq u hO hν J₁ J₂ hloc W₀

end S_AlgebraicGeometry_TwoGluedCurves_injective_and_range_eq_nodeCondition_of_forall_exists_isFrameOn
end P2MW
export P2MW.S_AlgebraicGeometry_TwoGluedCurves_injective_and_range_eq_nodeCondition_of_forall_exists_isFrameOn (solution)
