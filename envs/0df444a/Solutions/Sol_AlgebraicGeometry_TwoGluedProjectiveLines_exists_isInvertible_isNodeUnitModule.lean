-- Prove2me | solution 1 for AlgebraicGeometry.TwoGluedProjectiveLines.exists_isInvertible_isNodeUnitModule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/30f5f30b-daa7-5668-8d61-e465040e3ac3

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_TwoGluedProjectiveLinesNodeUnitModule
import Theorems.Thm_AlgebraicGeometry_TwoGluedProjectiveLines_isNodeUnitModule_one_unit
import Theorems.Thm_AlgebraicGeometry_TwoGluedProjectiveLines_pointAt_comp_eq_pointAt_comp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_exists_isInvertible_isNodeUnitModule

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve NeronModelInfra AlgebraicGeometry.TwoGluedProjectiveLines Opposite TopologicalSpace

noncomputable section

namespace TwoGluedLinesSubsheafAux

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

end TwoGluedLinesSubsheafAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_exists_isInvertible_isNodeUnitModule.TwoGluedLinesSubsheafAux"

namespace TwoGluedLinesFrameAux

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

end TwoGluedLinesFrameAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_exists_isInvertible_isNodeUnitModule.TwoGluedLinesSubsheafAux P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_exists_isInvertible_isNodeUnitModule.TwoGluedLinesFrameAux"

namespace TwoGluedLinesNodeUnitAux

open TwoGluedLinesSubsheafAux TwoGluedLinesFrameAux

variable {κ : Type u} [Field κ] [IsAlgClosed κ]
  {X : Scheme.{u}} {x : X ⟶ Spec (.of κ)}
  {M₁ M₂ : CurveModel κ (RatFunc κ)} {i₁ : M₁.C ⟶ X} {i₂ : M₂.C ⟶ X}
  {hi₁ : i₁ ≫ x = M₁.toBase} {hi₂ : i₂ ≫ x = M₂.toBase}
  {s : ℕ} {a b : Fin s → κˣ}
  {T : Scheme.{u}} {h : T ⟶ Spec (.of κ)} (u : Fin s → Γ(T, ⊤)ˣ)

local notation "XT" => pullback x h
local notation "C₁T" => pullback M₁.toBase h
local notation "C₂T" => pullback M₂.toBase h
local notation "i₁T" => curveChange i₁ hi₁ h
local notation "i₂T" => curveChange i₂ hi₂ h
local notation "σ¹" => nodeSectionFst M₁ a h
local notation "σ²" => nodeSectionSnd M₂ b h
local notation "nl" => nodeLocus x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h
set_option quotPrecheck false in

local notation "P¹" => (Scheme.Modules.pushforward (curveChange i₁ hi₁ h)).obj
  (SheafOfModules.unit (pullback M₁.toBase h).ringCatSheaf)
set_option quotPrecheck false in

local notation "P²" => (Scheme.Modules.pushforward (curveChange i₂ hi₂ h)).obj
  (SheafOfModules.unit (pullback M₂.toBase h).ringCatSheaf)

def fn₁ (W : (XT).Opens) (f : Γ(P¹, W)) : Γ(C₁T, (i₁T) ⁻¹ᵁ W) := f

def fn₂ (W : (XT).Opens) (g : Γ(P², W)) : Γ(C₂T, (i₂T) ⁻¹ᵁ W) := g

def ofFn₁ (W : (XT).Opens) (f : Γ(C₁T, (i₁T) ⁻¹ᵁ W)) : Γ(P¹, W) := f

def ofFn₂ (W : (XT).Opens) (g : Γ(C₂T, (i₂T) ⁻¹ᵁ W)) : Γ(P², W) := g

omit [IsAlgClosed κ] in
@[scoped simp] lemma fn₁_ofFn₁ (W : (XT).Opens) (f : Γ(C₁T, (i₁T) ⁻¹ᵁ W)) : fn₁ W (ofFn₁ W f) = f := rfl
omit [IsAlgClosed κ] in
@[scoped simp] lemma fn₂_ofFn₂ (W : (XT).Opens) (g : Γ(C₂T, (i₂T) ⁻¹ᵁ W)) : fn₂ W (ofFn₂ W g) = g := rfl
omit [IsAlgClosed κ] in
lemma fn₁_injective (W : (XT).Opens) : Function.Injective (fn₁ (hi₁ := hi₁) W) := fun _ _ e => e
omit [IsAlgClosed κ] in
lemma fn₂_injective (W : (XT).Opens) : Function.Injective (fn₂ (hi₂ := hi₂) W) := fun _ _ e => e
omit [IsAlgClosed κ] in
@[scoped simp] lemma fn₁_zero (W : (XT).Opens) : fn₁ (hi₁ := hi₁) W 0 = 0 := rfl
omit [IsAlgClosed κ] in
@[scoped simp] lemma fn₂_zero (W : (XT).Opens) : fn₂ (hi₂ := hi₂) W 0 = 0 := rfl
omit [IsAlgClosed κ] in
@[scoped simp] lemma fn₁_add (W : (XT).Opens) (f g : Γ(P¹, W)) : fn₁ W (f + g) = fn₁ W f + fn₁ W g := rfl
omit [IsAlgClosed κ] in
@[scoped simp] lemma fn₂_add (W : (XT).Opens) (f g : Γ(P², W)) : fn₂ W (f + g) = fn₂ W f + fn₂ W g := rfl
omit [IsAlgClosed κ] in

lemma fn₁_smul (W : (XT).Opens) (r : Γ(XT, W)) (f : Γ(P¹, W)) :
    fn₁ W (r • f) = (i₁T).app W r * fn₁ W f := rfl
omit [IsAlgClosed κ] in
lemma fn₂_smul (W : (XT).Opens) (r : Γ(XT, W)) (g : Γ(P², W)) :
    fn₂ W (r • g) = (i₂T).app W r * fn₂ W g := rfl

omit [IsAlgClosed κ] in
lemma preimage_mono {Y Z : Scheme.{u}} (f : Y ⟶ Z) {W W' : Z.Opens} (hW : W' ≤ W) : f ⁻¹ᵁ W' ≤ f ⁻¹ᵁ W :=
  fun _ hy => hW hy

omit [IsAlgClosed κ] in

lemma fn₁_map {W W' : (XT).Opens} (hW : W' ≤ W) (f : Γ(P¹, W)) :
    fn₁ W' ((P¹).presheaf.map (homOfLE hW).op f) =
      (C₁T).presheaf.map (homOfLE (preimage_mono (i₁T) hW)).op (fn₁ W f) := rfl

omit [IsAlgClosed κ] in
lemma fn₂_map {W W' : (XT).Opens} (hW : W' ≤ W) (g : Γ(P², W)) :
    fn₂ W' ((P²).presheaf.map (homOfLE hW).op g) =
      (C₂T).presheaf.map (homOfLE (preimage_mono (i₂T) hW)).op (fn₂ W g) := rfl

def ofFun (W : (XT).Opens) (r : Γ(XT, W)) : Γ(unitMod XT, W) := r

def toFun' (W : (XT).Opens) (r : Γ(unitMod XT, W)) : Γ(XT, W) := r

omit [IsAlgClosed κ] in
@[scoped simp] lemma ofFun_toFun' (W : (XT).Opens) (r : Γ(unitMod XT, W)) : ofFun W (toFun' W r) = r := rfl
omit [IsAlgClosed κ] in
lemma ofFun_mul (W : (XT).Opens) (r r' : Γ(XT, W)) : ofFun W (r * r') = r • ofFun W r' := rfl
omit [IsAlgClosed κ] in
lemma ofFun_map {W W' : (XT).Opens} (hW : W' ≤ W) (r : Γ(XT, W)) :
    (unitMod XT).presheaf.map (homOfLE hW).op (ofFun W r) = ofFun W' ((XT).presheaf.map (homOfLE hW).op r) := rfl

def ures (i : Fin s) (V : T.Opens) : Γ(T, V) := T.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (u i : Γ(T, ⊤))

lemma nodeCondition_iff (W : (XT).Opens) (i : Fin s) (f : Γ(C₁T, (i₁T) ⁻¹ᵁ W)) (g : Γ(C₂T, (i₂T) ⁻¹ᵁ W)) :
    NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h u W i f g ↔
      (σ¹ i).appLE ((i₁T) ⁻¹ᵁ W) (nl i W) inf_le_left f =
        ures u i (nl i W) * (σ² i).appLE ((i₂T) ⁻¹ᵁ W) (nl i W) inf_le_right g := Iff.rfl

omit [IsAlgClosed κ] in
lemma ures_one (i : Fin s) (V : T.Opens) : ures (1 : Fin s → Γ(T, ⊤)ˣ) i V = 1 := by
  simp [ures]

lemma nodeCondition_one_iff (W : (XT).Opens) (i : Fin s) (f : Γ(C₁T, (i₁T) ⁻¹ᵁ W))
    (g : Γ(C₂T, (i₂T) ⁻¹ᵁ W)) :
    NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h 1 W i f g ↔
      (σ¹ i).appLE ((i₁T) ⁻¹ᵁ W) (nl i W) inf_le_left f =
        (σ² i).appLE ((i₂T) ⁻¹ᵁ W) (nl i W) inf_le_right g := by
  rw [nodeCondition_iff, ures_one, one_mul]

lemma nodeCondition_one_mul (W : (XT).Opens) (i : Fin s) {f f' : Γ(C₁T, (i₁T) ⁻¹ᵁ W)}
    {g g' : Γ(C₂T, (i₂T) ⁻¹ᵁ W)}
    (hfg : NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h 1 W i f g)
    (hfg' : NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h 1 W i f' g') :
    NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h 1 W i (f * f') (g * g') := by
  rw [nodeCondition_one_iff] at hfg hfg' ⊢
  rw [map_mul, map_mul, hfg, hfg']

lemma nodeCondition_one_one (W : (XT).Opens) (i : Fin s) :
    NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h 1 W i (1 : Γ(C₁T, (i₁T) ⁻¹ᵁ W)) 1 := by
  rw [nodeCondition_one_iff, map_one, map_one]

lemma nodeLocus_mono (i : Fin s) {W W' : (XT).Opens} (hW : W' ≤ W) : nl i W' ≤ nl i W :=
  inf_le_inf (preimage_mono _ (preimage_mono _ hW)) (preimage_mono _ (preimage_mono _ hW))

lemma appLE_fst_res (i : Fin s) {W W' : (XT).Opens} (hW : W' ≤ W) (f : Γ(C₁T, (i₁T) ⁻¹ᵁ W)) :
    (σ¹ i).appLE ((i₁T) ⁻¹ᵁ W') (nl i W') inf_le_left
        ((C₁T).presheaf.map (homOfLE (preimage_mono (i₁T) hW)).op f) =
      T.presheaf.map (homOfLE (nodeLocus_mono i hW)).op
        ((σ¹ i).appLE ((i₁T) ⁻¹ᵁ W) (nl i W) inf_le_left f) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE,
    Scheme.Hom.appLE_map]

lemma appLE_snd_res (i : Fin s) {W W' : (XT).Opens} (hW : W' ≤ W) (g : Γ(C₂T, (i₂T) ⁻¹ᵁ W)) :
    (σ² i).appLE ((i₂T) ⁻¹ᵁ W') (nl i W') inf_le_right
        ((C₂T).presheaf.map (homOfLE (preimage_mono (i₂T) hW)).op g) =
      T.presheaf.map (homOfLE (nodeLocus_mono i hW)).op
        ((σ² i).appLE ((i₂T) ⁻¹ᵁ W) (nl i W) inf_le_right g) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE,
    Scheme.Hom.appLE_map]

omit [IsAlgClosed κ] in
lemma ures_res (u' : Fin s → Γ(T, ⊤)ˣ) {V V' : T.Opens} (hV : V' ≤ V) (i : Fin s) :
    T.presheaf.map (homOfLE hV).op (ures u' i V) = ures u' i V' := by
  unfold ures
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl

omit [IsAlgClosed κ] in
lemma unit_res {V V' : T.Opens} (hV : V' ≤ V) (i : Fin s) :
    T.presheaf.map (homOfLE hV).op (T.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (u i : Γ(T, ⊤))) =
      T.presheaf.map (homOfLE (le_top : V' ≤ ⊤)).op (u i : Γ(T, ⊤)) := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl

theorem nodeCondition_res (u' : Fin s → Γ(T, ⊤)ˣ) (i : Fin s) {W W' : (XT).Opens} (hW : W' ≤ W)
    (f : Γ(C₁T, (i₁T) ⁻¹ᵁ W)) (g : Γ(C₂T, (i₂T) ⁻¹ᵁ W))
    (hfg : NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h u' W i f g) :
    NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h u' W' i
      ((C₁T).presheaf.map (homOfLE (preimage_mono (i₁T) hW)).op f)
      ((C₂T).presheaf.map (homOfLE (preimage_mono (i₂T) hW)).op g) := by
  rw [nodeCondition_iff] at hfg ⊢
  rw [appLE_fst_res i hW f, appLE_snd_res i hW g, hfg, map_mul, ures_res]

omit [IsAlgClosed κ] in
lemma appLE_congr_hom {Y Z : Scheme.{u}} {f g : Y ⟶ Z} (e : f = g) (U : Z.Opens) (V : Y.Opens)
    (h₁ : V ≤ f ⁻¹ᵁ U) (h₂ : V ≤ g ⁻¹ᵁ U) : f.appLE U V h₁ = g.appLE U V h₂ := by
  subst e; rfl

lemma appLE_fst_app_eq_appLE_snd_app
    (hν : ∀ i : Fin s, nodeSectionFst M₁ a h i ≫ curveChange i₁ hi₁ h =
      nodeSectionSnd M₂ b h i ≫ curveChange i₂ hi₂ h)
    (i : Fin s) (W : (XT).Opens) (r : Γ(XT, W)) :
    (σ¹ i).appLE ((i₁T) ⁻¹ᵁ W) (nl i W) inf_le_left ((i₁T).app W r) =
      (σ² i).appLE ((i₂T) ⁻¹ᵁ W) (nl i W) inf_le_right ((i₂T).app W r) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appLE,
    ← Scheme.Hom.comp_appLE]
  rw [appLE_congr_hom (hν i)]

def nodeFamily (W : (XT).Opens) : Set (Γ(P¹, W) × Γ(P², W)) :=
  {fg | ∀ i : Fin s, NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h u W i (fn₁ W fg.1) (fn₂ W fg.2)}

lemma nodeFamily_eq (W : (XT).Opens) :
    nodeFamily (hi₁ := hi₁) (hi₂ := hi₂) (a := a) (b := b) u W =
      {fg | ∀ i : Fin s, NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h u W i fg.1 fg.2} := rfl

theorem nodeFamily_res {W W' : (XT).Opens} (hW : W' ≤ W) (p : Γ(P¹, W) × Γ(P², W))
    (hp : p ∈ nodeFamily (hi₁ := hi₁) (hi₂ := hi₂) (a := a) (b := b) u W) :
    resPair hW p ∈ nodeFamily (hi₁ := hi₁) (hi₂ := hi₂) (a := a) (b := b) u W' := by
  intro i
  change NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h u W' i (fn₁ W' ((P¹).presheaf.map (homOfLE hW).op p.1))
    (fn₂ W' ((P²).presheaf.map (homOfLE hW).op p.2))
  rw [fn₁_map, fn₂_map]
  exact nodeCondition_res u i hW _ _ (hp i)

theorem nodeFamily_zero (W : (XT).Opens) :
    (0 : Γ(P¹, W) × Γ(P², W)) ∈ nodeFamily (hi₁ := hi₁) (hi₂ := hi₂) (a := a) (b := b) u W := by
  intro i
  change NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h u W i (fn₁ W 0) (fn₂ W 0)
  unfold NodeCondition
  rw [fn₁_zero, fn₂_zero, map_zero, map_zero, mul_zero]

theorem nodeFamily_add (W : (XT).Opens) (p q : Γ(P¹, W) × Γ(P², W))
    (hp : p ∈ nodeFamily (hi₁ := hi₁) (hi₂ := hi₂) (a := a) (b := b) u W)
    (hq : q ∈ nodeFamily (hi₁ := hi₁) (hi₂ := hi₂) (a := a) (b := b) u W) :
    p + q ∈ nodeFamily (hi₁ := hi₁) (hi₂ := hi₂) (a := a) (b := b) u W := by
  intro i
  have hp' := hp i
  have hq' := hq i
  change NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h u W i (fn₁ W (p.1 + q.1)) (fn₂ W (p.2 + q.2))
  unfold NodeCondition at hp' hq' ⊢
  rw [fn₁_add, fn₂_add, map_add, map_add, mul_add, hp', hq']

theorem nodeFamily_smul
    (hν : ∀ i : Fin s, nodeSectionFst M₁ a h i ≫ curveChange i₁ hi₁ h =
      nodeSectionSnd M₂ b h i ≫ curveChange i₂ hi₂ h)
    (W : (XT).Opens) (r : Γ(XT, W)) (p : Γ(P¹, W) × Γ(P², W))
    (hp : p ∈ nodeFamily (hi₁ := hi₁) (hi₂ := hi₂) (a := a) (b := b) u W) :
    r • p ∈ nodeFamily (hi₁ := hi₁) (hi₂ := hi₂) (a := a) (b := b) u W := by
  intro i
  have hp' := hp i
  change NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h u W i (fn₁ W (r • p.1)) (fn₂ W (r • p.2))
  unfold NodeCondition at hp' ⊢
  rw [fn₁_smul, fn₂_smul, map_mul, map_mul, hp', appLE_fst_app_eq_appLE_snd_app hν i W r]
  ring

lemma nodeLocus_eq
    (hν : ∀ i : Fin s, nodeSectionFst M₁ a h i ≫ curveChange i₁ hi₁ h =
      nodeSectionSnd M₂ b h i ≫ curveChange i₂ hi₂ h)
    (i : Fin s) (W : (XT).Opens) : nl i W = ((σ¹ i) ≫ (i₁T)) ⁻¹ᵁ W := by
  change (σ¹ i) ⁻¹ᵁ ((i₁T) ⁻¹ᵁ W) ⊓ (σ² i) ⁻¹ᵁ ((i₂T) ⁻¹ᵁ W) = _
  have h1 : (σ¹ i) ⁻¹ᵁ ((i₁T) ⁻¹ᵁ W) = ((σ¹ i) ≫ (i₁T)) ⁻¹ᵁ W := rfl
  have h2 : (σ² i) ⁻¹ᵁ ((i₂T) ⁻¹ᵁ W) = ((σ² i) ≫ (i₂T)) ⁻¹ᵁ W := rfl
  rw [h1, h2, ← hν i, inf_idem]

lemma nodeLocus_iSup_le
    (hν : ∀ i : Fin s, nodeSectionFst M₁ a h i ≫ curveChange i₁ hi₁ h =
      nodeSectionSnd M₂ b h i ≫ curveChange i₂ hi₂ h)
    (i : Fin s) {ι : Type u} (U : ι → (XT).Opens) :
    nl i (iSup U) ≤ ⨆ k, nl i (U k) := by
  rw [nodeLocus_eq hν, Scheme.Hom.preimage_iSup]
  refine iSup_le fun k => ?_
  rw [← nodeLocus_eq hν]
  exact le_iSup (fun k => nl i (U k)) k

theorem nodeCondition_glue
    (hν : ∀ i : Fin s, nodeSectionFst M₁ a h i ≫ curveChange i₁ hi₁ h =
      nodeSectionSnd M₂ b h i ≫ curveChange i₂ hi₂ h)
    (i : Fin s) {ι : Type u} (U : ι → (XT).Opens)
    (f : Γ(C₁T, (i₁T) ⁻¹ᵁ (iSup U))) (g : Γ(C₂T, (i₂T) ⁻¹ᵁ (iSup U)))
    (hloc : ∀ k, NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h u (U k) i
      ((C₁T).presheaf.map (homOfLE (preimage_mono (i₁T) (le_iSup U k))).op f)
      ((C₂T).presheaf.map (homOfLE (preimage_mono (i₂T) (le_iSup U k))).op g)) :
    NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h u (iSup U) i f g := by
  unfold NodeCondition at hloc ⊢
  refine TopCat.Sheaf.eq_of_locally_eq' T.sheaf (fun k => nl i (U k)) (nl i (iSup U))
    (fun k => homOfLE (nodeLocus_mono i (le_iSup U k))) (nodeLocus_iSup_le hν i U) _ _ fun k => ?_
  have := hloc k
  rw [appLE_fst_res i (le_iSup U k) f, appLE_snd_res i (le_iSup U k) g] at this
  change T.presheaf.map _ _ = T.presheaf.map _ _
  rw [this, map_mul, unit_res u]

theorem nodeFamily_glue
    (hν : ∀ i : Fin s, nodeSectionFst M₁ a h i ≫ curveChange i₁ hi₁ h =
      nodeSectionSnd M₂ b h i ≫ curveChange i₂ hi₂ h)
    {ι : Type u} (U : ι → (XT).Opens) (p : Γ(P¹, iSup U) × Γ(P², iSup U))
    (hp : ∀ k, resPair (le_iSup U k) p ∈ nodeFamily (hi₁ := hi₁) (hi₂ := hi₂) (a := a) (b := b) u (U k)) :
    p ∈ nodeFamily (hi₁ := hi₁) (hi₂ := hi₂) (a := a) (b := b) u (iSup U) := by
  intro i
  refine nodeCondition_glue u hν i U (fn₁ _ p.1) (fn₂ _ p.2) fun k => ?_
  rw [← fn₁_map, ← fn₂_map]
  exact hp k i

theorem isLocalSubmoduleFamily_nodeFamily
    (hν : ∀ i : Fin s, nodeSectionFst M₁ a h i ≫ curveChange i₁ hi₁ h =
      nodeSectionSnd M₂ b h i ≫ curveChange i₂ hi₂ h) :
    IsLocalSubmoduleFamily (P¹) (P²) (nodeFamily (hi₁ := hi₁) (hi₂ := hi₂) (a := a) (b := b) u) where
  zero_mem := nodeFamily_zero u
  add_mem := nodeFamily_add u
  smul_mem := nodeFamily_smul u hν
  res := nodeFamily_res u
  glue := nodeFamily_glue u hν

theorem nodeSectionFst_comp_eq_nodeSectionSnd_comp
    (hpts : ∀ i, (pointAt M₁ (a i : κ)).1 ≫ i₁ = (pointAt M₂ (b i : κ)).1 ≫ i₂) (i : Fin s) :
    nodeSectionFst M₁ a h i ≫ curveChange i₁ hi₁ h = nodeSectionSnd M₂ b h i ≫ curveChange i₂ hi₂ h := by
  let ν : SchemeHomOver (𝟙 (Spec (.of κ))) x :=
    ⟨(pointAt M₁ (a i : κ)).1 ≫ i₁, by rw [Category.assoc, hi₁, (pointAt M₁ (a i : κ)).2]⟩
  have h1 : nodeSectionFst M₁ a h i ≫ curveChange i₁ hi₁ h = rigSection x h ν :=
    rigSection_curveChange i₁ hi₁ (ε' := pointAt M₁ (a i : κ)) (ε := ν) rfl h
  have h2 : nodeSectionSnd M₂ b h i ≫ curveChange i₂ hi₂ h = rigSection x h ν :=
    rigSection_curveChange i₂ hi₂ (ε' := pointAt M₂ (b i : κ)) (ε := ν) (hpts i).symm h
  rw [h1, h2]

theorem exists_isNodeUnitModule
    (hpts : ∀ i, (pointAt M₁ (a i : κ)).1 ≫ i₁ = (pointAt M₂ (b i : κ)).1 ≫ i₂) :
    ∃ M : (XT).Modules, IsNodeUnitModule x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h u M := by
  have hν := nodeSectionFst_comp_eq_nodeSectionSnd_comp (x := x) (hi₁ := hi₁) (hi₂ := hi₂) (h := h) hpts
  obtain ⟨M, j₁, j₂, hj⟩ := TwoGluedLinesSubsheafAux.exists_injective_and_range_eq _
    (isLocalSubmoduleFamily_nodeFamily u hν)
  exact ⟨M, j₁, j₂, fun W => hj W⟩

section Conductor

variable (hO : IsNodeUnitModule x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h 1 (unitMod (pullback x h)))

omit [IsAlgClosed κ] in

lemma app_ofFun {P : (XT).Modules} (j : unitMod XT ⟶ P) (W : (XT).Opens) (r : Γ(XT, W)) :
    j.app W (ofFun W r) = r • j.app W (ofFun W 1) := by
  rw [← Scheme.Modules.Hom.app_smul, ← ofFun_mul, mul_one]

include hO in

theorem conductor (W : (XT).Opens) :
    Function.Injective (fun r : Γ(XT, W) => ((i₁T).app W r, (i₂T).app W r)) ∧
      ∀ (f : Γ(C₁T, (i₁T) ⁻¹ᵁ W)) (g : Γ(C₂T, (i₂T) ⁻¹ᵁ W)),
        (∀ i, NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h 1 W i f g) →
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
      (∀ i, NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h 1 W i f g) →
        ∃ r : Γ(XT, W), fn₁ W (j₁.app W (ofFun W r)) = f ∧ fn₂ W (j₂.app W (ofFun W r)) = g := by
    intro f g hfg
    have : (ofFn₁ W f, ofFn₂ W g) ∈ Set.range (fun m : Γ(unitMod XT, W) => (j₁.app W m, j₂.app W m)) := by
      rw [hrange]; exact hfg
    obtain ⟨m, hm⟩ := this
    refine ⟨toFun' W m, ?_, ?_⟩
    · rw [ofFun_toFun']; exact congrArg (fn₁ W) (congrArg Prod.fst hm)
    · rw [ofFun_toFun']; exact congrArg (fn₂ W) (congrArg Prod.snd hm)
  have hsat : ∀ (r : Γ(XT, W)) (i : Fin s), NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h 1 W i
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
  have hεν : ∀ i, NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h 1 W i ε₁ ε₂ := hsat 1
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
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_exists_isInvertible_isNodeUnitModule.TwoGluedLinesSubsheafAux P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_exists_isInvertible_isNodeUnitModule.TwoGluedLinesFrameAux"

def nodePt (i₁ : M₁.C ⟶ X) (a : Fin s → κˣ) (i : Fin s) : X :=
  i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (a i : κ))).1

lemma pointAt_apply (M : CurveModel κ (RatFunc κ)) (c : κ) (t : Spec (.of κ)) :
    (pointAt M c).1.base t = (M.placeEquiv.symm (RationalFunctionField.placeOfPoint κ c)).1 := by
  obtain rfl : t = IsLocalRing.closedPoint κ := Subsingleton.elim _ _
  change ((pointEquivClosedPoint M.toBase) (pointAt M c)).1 = _
  rw [pointAt, CurveModel.pointEquivPlace, Equiv.symm_trans_apply, Equiv.apply_symm_apply]

lemma nodeSectionFst_curveChange_fst (i : Fin s) :
    σ¹ i ≫ (i₁T) ≫ pullback.fst x h = h ≫ (pointAt M₁ (a i : κ)).1 ≫ i₁ := by
  simp only [nodeSectionFst, rigSection, curveChange, pullback.lift_fst, pullback.lift_fst_assoc,
    Category.assoc]

lemma nodeSectionFst_curveChange_fst_apply (i : Fin s) (t : T) :
    (pullback.fst x h).base ((i₁T).base ((σ¹ i).base t)) = nodePt i₁ a i := by
  have e := nodeSectionFst_curveChange_fst (x := x) (hi₁ := hi₁) (a := a) (h := h) i
  have := congrArg (fun φ : T ⟶ X => φ.base t) e
  simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply] at this
  rw [this]
  exact congrArg i₁.base (pointAt_apply M₁ (a i : κ) _)

lemma nodeLocus_eq_bot {V : X.Opens} {i : Fin s} (hi : nodePt i₁ a i ∉ V) {W : (XT).Opens}
    (hW : W ≤ (pullback.fst x h) ⁻¹ᵁ V) : nl i W = ⊥ := by
  rw [eq_bot_iff]
  intro t ht
  have h1 : (i₁T).base ((σ¹ i).base t) ∈ W := ht.1
  have h2 := hW h1
  change (pullback.fst x h).base ((i₁T).base ((σ¹ i).base t)) ∈ V at h2
  rw [nodeSectionFst_curveChange_fst_apply] at h2
  exact (hi h2).elim

lemma nodeCondition_of_eq_bot (u' : Fin s → Γ(T, ⊤)ˣ) {W : (XT).Opens} {i : Fin s} (hbot : nl i W = ⊥)
    (f : Γ(C₁T, (i₁T) ⁻¹ᵁ W)) (g : Γ(C₂T, (i₂T) ⁻¹ᵁ W)) :
    NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h u' W i f g := by
  haveI : Subsingleton Γ(T, nl i W) :=
    CommRingCat.subsingleton_of_isTerminal (T.sheaf.isTerminalOfEqEmpty hbot)
  exact Subsingleton.elim _ _

def sndFun (c : Γ(T, ⊤)) (W : (XT).Opens) : Γ(C₂T, (i₂T) ⁻¹ᵁ W) :=
  (pullback.snd M₂.toBase h).appLE ⊤ ((i₂T) ⁻¹ᵁ W) le_top c

omit [IsAlgClosed κ] in
lemma sndFun_mul (c c' : Γ(T, ⊤)) (W : (XT).Opens) :
    sndFun (hi₂ := hi₂) (c * c') W = sndFun c W * sndFun c' W := map_mul _ _ _

omit [IsAlgClosed κ] in
lemma sndFun_one (W : (XT).Opens) : sndFun (hi₂ := hi₂) (1 : Γ(T, ⊤)) W = 1 := map_one _

omit [IsAlgClosed κ] in
lemma sndFun_map {W W' : (XT).Opens} (hW : W' ≤ W) (c : Γ(T, ⊤)) :
    (C₂T).presheaf.map (homOfLE (preimage_mono (i₂T) hW)).op (sndFun c W) = sndFun c W' := by
  unfold sndFun
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]

omit [IsAlgClosed κ] in
lemma isUnit_sndFun (v : Γ(T, ⊤)ˣ) (W : (XT).Opens) : IsUnit (sndFun (hi₂ := hi₂) (v : Γ(T, ⊤)) W) :=
  (Units.isUnit v).map _

lemma nodeSectionSnd_snd (i : Fin s) : σ² i ≫ pullback.snd M₂.toBase h = 𝟙 T := by
  simp only [nodeSectionSnd, rigSection, pullback.lift_snd]

lemma appLE_sndFun (i : Fin s) (W : (XT).Opens) (c : Γ(T, ⊤)) :
    (σ² i).appLE ((i₂T) ⁻¹ᵁ W) (nl i W) inf_le_right (sndFun c W) =
      T.presheaf.map (homOfLE (le_top : nl i W ≤ ⊤)).op c := by
  unfold sndFun
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_comp_appLE]
  rw [appLE_congr_hom (nodeSectionSnd_snd i) ⊤ (nl i W) _ le_top]
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
  rfl

section Frame

variable {M : (pullback x h).Modules} (hM : IsNodeUnitModule x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h u M)
  (hO : IsNodeUnitModule x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h 1 (unitMod (pullback x h)))
  {V : X.Opens} {v : Γ(T, ⊤)ˣ} (hV : ∀ i, nodePt i₁ a i ∈ V → u i = v)

include hV in

lemma nodeCondition_one_vinv {W : (XT).Opens} (hW : W ≤ (pullback.fst x h) ⁻¹ᵁ V) (i : Fin s) :
    NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h u W i 1 (sndFun (v⁻¹ : Γ(T, ⊤)ˣ) W) := by
  by_cases hi : nodePt i₁ a i ∈ V
  · rw [nodeCondition_iff, map_one, appLE_sndFun, ures, hV i hi, ← map_mul, Units.mul_inv, map_one]
  · exact nodeCondition_of_eq_bot u (nodeLocus_eq_bot hi hW) _ _

include hV in

lemma nodeCondition_one_of_nodeCondition {W : (XT).Opens} (hW : W ≤ (pullback.fst x h) ⁻¹ᵁ V) (i : Fin s)
    (f : Γ(C₁T, (i₁T) ⁻¹ᵁ W)) (g : Γ(C₂T, (i₂T) ⁻¹ᵁ W))
    (hfg : NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h u W i f g) :
    NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h 1 W i f (g * sndFun (v : Γ(T, ⊤)) W) := by
  by_cases hi : nodePt i₁ a i ∈ V
  · rw [nodeCondition_one_iff, map_mul, appLE_sndFun]
    rw [nodeCondition_iff, ures, hV i hi] at hfg
    rw [hfg, mul_comm]
  · exact nodeCondition_of_eq_bot 1 (nodeLocus_eq_bot hi hW) _ _

include hM hO hV in

theorem exists_isFrame :
    ∃ m₀ : Γ(M, (pullback.fst x h) ⁻¹ᵁ V), IsFrame m₀ := by
  obtain ⟨j₁, j₂, hj⟩ := hM
  set U₀ : (XT).Opens := (pullback.fst x h) ⁻¹ᵁ V

  have hp₀ : (ofFn₁ U₀ 1, ofFn₂ U₀ (sndFun (v⁻¹ : Γ(T, ⊤)ˣ) U₀)) ∈
      Set.range (fun m : Γ(M, U₀) => (j₁.app U₀ m, j₂.app U₀ m)) := by
    rw [(hj U₀).2]
    exact fun i => nodeCondition_one_vinv u hV le_rfl i
  obtain ⟨m₀, hm₀⟩ := hp₀
  have hm₀₁ : fn₁ U₀ (j₁.app U₀ m₀) = 1 := congrArg (fn₁ U₀) (congrArg Prod.fst hm₀)
  have hm₀₂ : fn₂ U₀ (j₂.app U₀ m₀) = sndFun (v⁻¹ : Γ(T, ⊤)ˣ) U₀ := congrArg (fn₂ U₀) (congrArg Prod.snd hm₀)
  refine ⟨m₀, ?_⟩
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
  have hvv : sndFun (hi₂ := hi₂) (v : Γ(T, ⊤)) W * sndFun (v⁻¹ : Γ(T, ⊤)ˣ) W = 1 := by
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

    have hfg : ∀ i, NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h u W i (fn₁ W (j₁.app W m)) (fn₂ W (j₂.app W m)) := by
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
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_exists_isInvertible_isNodeUnitModule.TwoGluedLinesSubsheafAux P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_exists_isInvertible_isNodeUnitModule.TwoGluedLinesFrameAux"

section Cover

variable [IsClosedImmersion i₁] (ha : Function.Injective a)

include ha in
omit [IsAlgClosed κ] in
lemma nodePt_injective : Function.Injective (nodePt i₁ a) := by
  intro i j hij
  apply ha
  have h1 := i₁.isClosedEmbedding.injective hij
  have h2 := Subtype.val_injective h1
  have h3 := M₁.placeEquiv.symm.injective h2
  exact Units.val_injective (RationalFunctionField.placeOfPoint_injective κ h3)

omit [IsAlgClosed κ] in
lemma isClosed_nodePt (i : Fin s) : IsClosed ({nodePt i₁ a i} : Set X) := by
  have hc : IsClosed ({(M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (a i : κ))).1} : Set M₁.C) :=
    (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (a i : κ))).2
  have := i₁.isClosedEmbedding.isClosedMap _ hc
  rwa [Set.image_singleton] at this

def awayFrom (S : Set (Fin s)) : X.Opens :=
  ⟨(⋃ j : S, {nodePt i₁ a j.1})ᶜ, isOpen_compl_iff.2 (isClosed_iUnion_of_finite fun j => isClosed_nodePt j.1)⟩

omit [IsAlgClosed κ] in
lemma mem_awayFrom_iff (S : Set (Fin s)) (q : X) : q ∈ awayFrom (i₁ := i₁) (a := a) S ↔ ∀ j ∈ S, q ≠ nodePt i₁ a j := by
  change q ∈ (⋃ j : S, {nodePt i₁ a j.1})ᶜ ↔ _
  simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_singleton_iff, not_exists]
  exact ⟨fun H j hj => H ⟨j, hj⟩, fun H j => H j.1 j.2⟩

include ha in
omit [IsAlgClosed κ] in

theorem exists_open_sameUnit (q : X) :
    ∃ (V : X.Opens) (v : Γ(T, ⊤)ˣ), q ∈ V ∧ ∀ i, nodePt i₁ a i ∈ V → u i = v := by
  by_cases hq : ∃ i₀, q = nodePt i₁ a i₀
  · obtain ⟨i₀, rfl⟩ := hq
    refine ⟨awayFrom (i₁ := i₁) (a := a) {j | j ≠ i₀}, u i₀, ?_, ?_⟩
    · rw [mem_awayFrom_iff]
      intro j hj e
      exact hj (nodePt_injective ha e).symm
    · intro i hi
      rw [mem_awayFrom_iff] at hi
      by_contra hne
      exact hi i (fun e => hne (e ▸ rfl)) rfl
  · refine ⟨awayFrom (i₁ := i₁) (a := a) Set.univ, 1, ?_, ?_⟩
    · rw [mem_awayFrom_iff]
      intro j _ e
      exact hq ⟨j, e⟩
    · intro i hi
      rw [mem_awayFrom_iff] at hi
      exact (hi i trivial rfl).elim

end Cover
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_exists_isInvertible_isNodeUnitModule.TwoGluedLinesSubsheafAux P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_exists_isInvertible_isNodeUnitModule.TwoGluedLinesFrameAux"

theorem isInvertible_of_isNodeUnitModule [IsClosedImmersion i₁] (ha : Function.Injective a)
    (hO : IsNodeUnitModule x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h 1 (unitMod (pullback x h)))
    {M : (pullback x h).Modules} (hM : IsNodeUnitModule x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h u M) :
    Scheme.Modules.IsInvertible M := by
  refine isInvertible_of_forall_exists_isFrame fun p => ?_
  obtain ⟨V, v, hpV, hV⟩ := exists_open_sameUnit (i₁ := i₁) (T := T) u ha ((pullback.fst x h).base p)
  obtain ⟨m₀, hm₀⟩ := exists_isFrame u hM hO hV
  exact ⟨(pullback.fst x h) ⁻¹ᵁ V, m₀, hpV, hm₀⟩

end TwoGluedLinesNodeUnitAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_exists_isInvertible_isNodeUnitModule.TwoGluedLinesSubsheafAux P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_exists_isInvertible_isNodeUnitModule.TwoGluedLinesFrameAux P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_exists_isInvertible_isNodeUnitModule.TwoGluedLinesNodeUnitAux"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_exists_isInvertible_isNodeUnitModule.TwoGluedLinesSubsheafAux P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_exists_isInvertible_isNodeUnitModule.TwoGluedLinesFrameAux P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_exists_isInvertible_isNodeUnitModule.TwoGluedLinesNodeUnitAux"

open TwoGluedLinesNodeUnitAux in
theorem solution
    (κ : Type u) [Field κ] [IsAlgClosed κ]
    {X : Scheme.{u}} (x : X ⟶ Spec (.of κ)) [IsReduced X]
    (M₁ M₂ : CurveModel κ (RatFunc κ)) (i₁ : M₁.C ⟶ X) (i₂ : M₂.C ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hi₁ : i₁ ≫ x = M₁.toBase) (hi₂ : i₂ ≫ x = M₂.toBase)
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    {s : ℕ} (a b : Fin s → κˣ) (ha : Function.Injective a)
    (hnode : ∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (a i : κ))).1
                = i₂.base (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (b i : κ))).1)
    (hinter : ∀ p q, i₁.base p = i₂.base q →
      ∃ i, p = (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (a i))).1 ∧
        q = (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (b i))).1)
    (htrans : IsReduced (pullback i₁ i₂))
    {T : Scheme.{u}} (h : T ⟶ Spec (.of κ)) (u : Fin s → Γ(T, ⊤)ˣ) :
    ∃ M : (pullback x h).Modules, Scheme.Modules.IsInvertible M ∧
      IsNodeUnitModule x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h u M := by

  have hpts : ∀ i, (pointAt M₁ (a i : κ)).1 ≫ i₁ = (pointAt M₂ (b i : κ)).1 ≫ i₂ := fun i =>
    AlgebraicGeometry.TwoGluedProjectiveLines.pointAt_comp_eq_pointAt_comp κ x M₁ M₂ i₁ i₂ hi₁ hi₂ _ _ (hnode i)

  obtain ⟨M, hM⟩ := exists_isNodeUnitModule (x := x) (hi₁ := hi₁) (hi₂ := hi₂) (h := h) u hpts

  have hO := AlgebraicGeometry.TwoGluedProjectiveLines.isNodeUnitModule_one_unit κ x M₁ M₂ i₁ i₂ hi₁ hi₂ hcover
    a b ha hnode hinter htrans h
  exact ⟨M, isInvertible_of_isNodeUnitModule u ha hO hM, hM⟩

end S_AlgebraicGeometry_TwoGluedProjectiveLines_exists_isInvertible_isNodeUnitModule
end P2MW
export P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_exists_isInvertible_isNodeUnitModule (solution)
