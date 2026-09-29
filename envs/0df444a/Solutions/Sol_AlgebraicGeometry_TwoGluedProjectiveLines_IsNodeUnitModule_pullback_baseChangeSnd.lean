-- Prove2me | solution 1 for AlgebraicGeometry.TwoGluedProjectiveLines.IsNodeUnitModule.pullback_baseChangeSnd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/09930446-1512-5dd8-9ea7-1f3098e75c6c

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_TwoGluedProjectiveLinesNodeUnitModule
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit
import Theorems.Thm_AlgebraicGeometry_TwoGluedProjectiveLines_exists_isInvertible_isNodeUnitModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_IsNodeUnitModule_pullback_baseChangeSnd

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve NeronModelInfra AlgebraicGeometry.TwoGluedProjectiveLines Opposite TopologicalSpace

noncomputable section

namespace TwoGluedLinesBCGenAux

variable {Y : Scheme.{u}}

section Pair

variable {P₁ P₂ M : Y.Modules} (j₁ : M ⟶ P₁) (j₂ : M ⟶ P₂)

def pair (W : Y.Opens) (m : Γ(M, W)) : Γ(P₁, W) × Γ(P₂, W) := (j₁.app W m, j₂.app W m)

lemma pair_add (W : Y.Opens) (m m' : Γ(M, W)) :
    pair j₁ j₂ W (m + m') = pair j₁ j₂ W m + pair j₁ j₂ W m' := by
  simp only [pair, map_add, Prod.mk_add_mk]

lemma pair_smul (W : Y.Opens) (r : Γ(Y, W)) (m : Γ(M, W)) :
    pair j₁ j₂ W (r • m) = r • pair j₁ j₂ W m := by
  simp only [pair, Scheme.Modules.Hom.app_smul, Prod.smul_mk]

lemma app_map {N N' : Y.Modules} (φ : N ⟶ N') {W W' : Y.Opens} (i : W' ⟶ W) (n : Γ(N, W)) :
    φ.app W' (N.presheaf.map i.op n) = N'.presheaf.map i.op (φ.app W n) := by
  have h := φ.mapPresheaf.naturality i.op
  exact ConcreteCategory.congr_hom h n

lemma pair_map {W W' : Y.Opens} (i : W' ⟶ W) (m : Γ(M, W)) :
    pair j₁ j₂ W' (M.presheaf.map i.op m) =
      (P₁.presheaf.map i.op (pair j₁ j₂ W m).1, P₂.presheaf.map i.op (pair j₁ j₂ W m).2) := by
  simp only [pair, app_map]

end Pair

section Lift

variable {P₁ P₂ M M' : Y.Modules} (j₁ : M ⟶ P₁) (j₂ : M ⟶ P₂) (j₁' : M' ⟶ P₁) (j₂' : M' ⟶ P₂)
  (hinj' : ∀ W : Y.Opens, Function.Injective (pair j₁' j₂' W))
  (hle : ∀ W : Y.Opens, Set.range (pair j₁ j₂ W) ⊆ Set.range (pair j₁' j₂' W))

include hle in
lemma exists_pair_eq (W : Y.Opens) (m : Γ(M, W)) : ∃ m' : Γ(M', W), pair j₁' j₂' W m' = pair j₁ j₂ W m :=
  hle W ⟨m, rfl⟩

def lift (W : Y.Opens) (m : Γ(M, W)) : Γ(M', W) := (exists_pair_eq j₁ j₂ j₁' j₂' hle W m).choose

lemma pair_lift (W : Y.Opens) (m : Γ(M, W)) :
    pair j₁' j₂' W (lift j₁ j₂ j₁' j₂' hle W m) = pair j₁ j₂ W m :=
  (exists_pair_eq j₁ j₂ j₁' j₂' hle W m).choose_spec

include hinj' in
lemma lift_add (W : Y.Opens) (m n : Γ(M, W)) :
    lift j₁ j₂ j₁' j₂' hle W (m + n) = lift j₁ j₂ j₁' j₂' hle W m + lift j₁ j₂ j₁' j₂' hle W n := by
  apply hinj' W
  rw [pair_add, pair_lift, pair_lift, pair_lift, pair_add]

include hinj' in
lemma lift_smul (W : Y.Opens) (r : Γ(Y, W)) (m : Γ(M, W)) :
    lift j₁ j₂ j₁' j₂' hle W (r • m) = r • lift j₁ j₂ j₁' j₂' hle W m := by
  apply hinj' W
  rw [pair_smul, pair_lift, pair_lift, pair_smul]

include hinj' in
lemma lift_map {W W' : Y.Opens} (i : W' ⟶ W) (m : Γ(M, W)) :
    lift j₁ j₂ j₁' j₂' hle W' (M.presheaf.map i.op m) =
      M'.presheaf.map i.op (lift j₁ j₂ j₁' j₂' hle W m) := by
  apply hinj' W'
  rw [pair_lift, pair_map, pair_map, pair_lift]

def liftPresheafHom : M.presheaf ⟶ M'.presheaf where
  app W := AddCommGrpCat.ofHom
    (AddMonoidHom.mk' (lift j₁ j₂ j₁' j₂' hle W.unop) (lift_add j₁ j₂ j₁' j₂' hinj' hle W.unop))
  naturality W W' i := by
    ext m
    obtain ⟨i, rfl⟩ : ∃ i' : W'.unop ⟶ W.unop, i = i'.op := ⟨i.unop, rfl⟩
    exact lift_map j₁ j₂ j₁' j₂' hinj' hle i m

def liftHom : M ⟶ M' :=
  ⟨PresheafOfModules.homMk (liftPresheafHom j₁ j₂ j₁' j₂' hinj' hle)
    (fun W r m => lift_smul j₁ j₂ j₁' j₂' hinj' hle W.unop r m)⟩

lemma liftHom_app (W : Y.Opens) (m : Γ(M, W)) :
    (liftHom j₁ j₂ j₁' j₂' hinj' hle).app W m = lift j₁ j₂ j₁' j₂' hle W m := rfl

lemma pair_liftHom_app (W : Y.Opens) (m : Γ(M, W)) :
    pair j₁' j₂' W ((liftHom j₁ j₂ j₁' j₂' hinj' hle).app W m) = pair j₁ j₂ W m :=
  pair_lift j₁ j₂ j₁' j₂' hle W m

end Lift

section LocalBij

variable {A B : Y.Modules} (φ : A ⟶ B)

theorem bijective_app_of_locally
    (hloc : ∀ p : Y, ∃ V : Y.Opens, p ∈ V ∧ ∀ W ≤ V, Function.Bijective (φ.app W)) (W : Y.Opens) :
    Function.Bijective (φ.app W) := by
  classical
  choose V hpV hV using hloc

  let ι := W
  let U : ι → Y.Opens := fun p => W ⊓ V p.1
  have hUle : ∀ p : ι, U p ≤ W := fun p => inf_le_left
  have hcov : W ≤ iSup U := fun y hy => Opens.mem_iSup.mpr ⟨⟨y, hy⟩, ⟨hy, hpV y⟩⟩
  have hbij : ∀ p : ι, Function.Bijective (φ.app (U p)) := fun p => hV p.1 _ inf_le_right
  let FA : TopCat.Sheaf Ab Y := ⟨A.presheaf, A.isSheaf⟩
  let FB : TopCat.Sheaf Ab Y := ⟨B.presheaf, B.isSheaf⟩
  constructor
  · intro m m' hmm'
    refine TopCat.Sheaf.eq_of_locally_eq' FA U W (fun p => homOfLE (hUle p)) hcov m m' fun p => ?_
    apply (hbij p).1
    change φ.app (U p) (A.presheaf.map (homOfLE (hUle p)).op m) =
      φ.app (U p) (A.presheaf.map (homOfLE (hUle p)).op m')
    rw [app_map, app_map, hmm']
  · intro n

    have hk : ∀ p : ι, ∃ m : Γ(A, U p), φ.app (U p) m = B.presheaf.map (homOfLE (hUle p)).op n :=
      fun p => (hbij p).2 _
    choose mk hmk using hk
    have hcompat : TopCat.Presheaf.IsCompatible FA.1 U mk := by
      intro p q
      apply (hV p.1 (U p ⊓ U q) (inf_le_left.trans inf_le_right)).1
      change φ.app _ (A.presheaf.map (homOfLE inf_le_left).op (mk p)) =
        φ.app _ (A.presheaf.map (homOfLE inf_le_right).op (mk q))
      rw [app_map, app_map, hmk, hmk, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
        ← Functor.map_comp, ← Functor.map_comp]
      rfl
    obtain ⟨m, hm, -⟩ := TopCat.Sheaf.existsUnique_gluing' FA U W (fun p => homOfLE (hUle p)) hcov mk hcompat
    refine ⟨m, ?_⟩
    refine TopCat.Sheaf.eq_of_locally_eq' FB U W (fun p => homOfLE (hUle p)) hcov _ _ fun p => ?_
    change B.presheaf.map (homOfLE (hUle p)).op (φ.app W m) = B.presheaf.map (homOfLE (hUle p)).op n
    rw [← app_map, ← hmk p]
    exact congrArg _ (hm p)

theorem isIso_of_bijective_app (h : ∀ W : Y.Opens, Function.Bijective (φ.app W)) : IsIso φ := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro W
  exact (ConcreteCategory.isIso_iff_bijective _).2 (h W)

end LocalBij

section Frames

p2m_open "AlgebraicGeometry.Scheme.Modules"

variable {M : Y.Modules}

lemma isFrameOn_smul {U V : Y.Opens} {s : Γ(M, U)} (hs : IsFrameOn s V) {c : Γ(Y, U)} (hc : IsUnit c) :
    IsFrameOn (c • s) V := by
  intro W hWU hWV
  have e : M.presheaf.map (homOfLE hWU).op (c • s) =
      Y.presheaf.map (homOfLE hWU).op c • M.presheaf.map (homOfLE hWU).op s := Scheme.Modules.map_smul _ _ _ _
  simp only [e]
  have hc' : IsUnit (Y.presheaf.map (homOfLE hWU).op c) := hc.map _
  have : (fun g : Γ(Y, W) => g • (Y.presheaf.map (homOfLE hWU).op c • M.presheaf.map (homOfLE hWU).op s)) =
      (fun g : Γ(Y, W) => g • M.presheaf.map (homOfLE hWU).op s) ∘
        fun g : Γ(Y, W) => g * Y.presheaf.map (homOfLE hWU).op c := by
    funext g
    simp only [Function.comp_apply, mul_smul]
  rw [this]
  exact (hs hWU hWV).comp (IsUnit.isUnit_iff_mulRight_bijective.mp hc')

lemma isUnit_of_isFrameOn_smul {W : Y.Opens} {s : Γ(M, W)} (hs : IsFrameOn s W) {r : Γ(Y, W)}
    (hrs : IsFrameOn (r • s) W) : IsUnit r := by

  obtain ⟨d, hd⟩ := (hrs le_rfl le_rfl).2 (M.presheaf.map (homOfLE le_rfl).op s)
  have hd' : (d * r) • M.presheaf.map (homOfLE (le_refl W)).op s =
      (1 : Γ(Y, W)) • M.presheaf.map (homOfLE (le_refl W)).op s := by
    rw [one_smul, mul_smul]
    have e : M.presheaf.map (homOfLE (le_refl W)).op (r • s) =
        Y.presheaf.map (homOfLE (le_refl W)).op r • M.presheaf.map (homOfLE (le_refl W)).op s :=
      Scheme.Modules.map_smul _ _ _ _
    have er : Y.presheaf.map (homOfLE (le_refl W)).op r = r := by
      have : (homOfLE (le_refl W)).op = 𝟙 (op W) := rfl
      rw [this, Y.presheaf.map_id]; rfl
    rw [er] at e
    rw [← e]
    exact hd
  have := (hs le_rfl le_rfl).1 hd'
  exact IsUnit.of_mul_eq_one_right d this

lemma exists_eq_smul_of_isFrameOn {U V W : Y.Opens} {s : Γ(M, U)} (hs : IsFrameOn s V) (hWU : W ≤ U)
    (hWV : W ≤ V) (m : Γ(M, W)) : ∃ g : Γ(Y, W), m = g • M.presheaf.map (homOfLE hWU).op s := by
  obtain ⟨g, hg⟩ := (hs hWU hWV).2 m
  exact ⟨g, hg.symm⟩

end Frames

section IsoCriterion

p2m_open "AlgebraicGeometry.Scheme.Modules"

variable {A B : Y.Modules} (θ : A ⟶ B)

lemma app_res {V W : Y.Opens} (h : W ≤ V) (t : Γ(A, V)) :
    θ.app W (A.presheaf.map (homOfLE h).op t) = B.presheaf.map (homOfLE h).op (θ.app V t) :=
  app_map θ (homOfLE h) t

theorem isIso_of_locally_isFrameOn_app (hA : IsInvertible A)
    (hcov : ∀ p : Y, ∃ V : Y.Opens, p ∈ V ∧ ∃ t : Γ(A, V), IsFrameOn (θ.app V t) V) : IsIso θ := by
  apply isIso_of_bijective_app
  apply bijective_app_of_locally
  intro p
  obtain ⟨V, hpV, t, ht⟩ := hcov p
  obtain ⟨Ua, hpUa, ⟨eUa⟩⟩ := hA.1 p
  obtain ⟨a, ha⟩ := Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit Ua eUa

  let W₀ : Y.Opens := V ⊓ Ua
  have hW₀V : W₀ ≤ V := inf_le_left
  have hW₀U : W₀ ≤ Ua := inf_le_right
  let a₀ : Γ(A, W₀) := A.presheaf.map (homOfLE hW₀U).op a
  let t₀ : Γ(A, W₀) := A.presheaf.map (homOfLE hW₀V).op t
  have ha₀ : IsFrameOn a₀ W₀ := (ha.map (homOfLE hW₀U)).mono hW₀U
  have hθt₀ : IsFrameOn (θ.app W₀ t₀) W₀ := by
    have : θ.app W₀ t₀ = B.presheaf.map (homOfLE hW₀V).op (θ.app V t) := app_res θ hW₀V t
    rw [this]
    exact (ht.map (homOfLE hW₀V)).mono hW₀V

  obtain ⟨r, hr⟩ : ∃ r : Γ(Y, W₀), t₀ = r • a₀ := by
    obtain ⟨r, hr⟩ := exists_eq_smul_of_isFrameOn ha₀ le_rfl le_rfl t₀
    refine ⟨r, hr.trans ?_⟩
    have : (homOfLE (le_refl W₀)).op = 𝟙 (op W₀) := rfl
    rw [this, A.presheaf.map_id]; rfl

  have hθa₀ : IsFrameOn (θ.app W₀ a₀) W₀ := by
    have e1 : θ.app W₀ t₀ = r • θ.app W₀ a₀ := by rw [hr, Scheme.Modules.Hom.app_smul]

    obtain ⟨d, hd⟩ : ∃ d : Γ(Y, W₀), θ.app W₀ a₀ = d • θ.app W₀ t₀ := by
      obtain ⟨d, hd⟩ := exists_eq_smul_of_isFrameOn hθt₀ le_rfl le_rfl (θ.app W₀ a₀)
      refine ⟨d, hd.trans ?_⟩
      have : (homOfLE (le_refl W₀)).op = 𝟙 (op W₀) := rfl
      rw [this, B.presheaf.map_id]; rfl
    have hunit : IsUnit (r * d) := by
      apply isUnit_of_isFrameOn_smul hθt₀
      rw [mul_smul, ← hd, ← e1]
      exact hθt₀
    have hd_unit : IsUnit d := isUnit_of_mul_isUnit_right hunit
    rw [hd]
    exact isFrameOn_smul hθt₀ hd_unit
  refine ⟨W₀, ⟨hpV, hpUa⟩, fun W hW => ?_⟩

  have hcomp : (θ.app W) ∘ (fun g : Γ(Y, W) => g • A.presheaf.map (homOfLE hW).op a₀) =
      fun g : Γ(Y, W) => g • B.presheaf.map (homOfLE hW).op (θ.app W₀ a₀) := by
    funext g
    simp only [Function.comp_apply, Scheme.Modules.Hom.app_smul, app_res]
  have h1 : Function.Bijective (fun g : Γ(Y, W) => g • A.presheaf.map (homOfLE hW).op a₀) := ha₀ hW hW
  have h2 : Function.Bijective (fun g : Γ(Y, W) => g • B.presheaf.map (homOfLE hW).op (θ.app W₀ a₀)) :=
    hθa₀ hW hW
  rw [← hcomp] at h2
  exact (Function.Bijective.of_comp_iff (θ.app W) h1).mp h2

end IsoCriterion

lemma pushforward_smul {Z : Scheme.{u}} (f : Z ⟶ Y) (N : Z.Modules) (W : Y.Opens) (r : Γ(Y, W))
    (n : Γ((Scheme.Modules.pushforward f).obj N, W)) :
    r • n = (show Γ(N, f ⁻¹ᵁ W) from f.app W r • (show Γ(N, f ⁻¹ᵁ W) from n)) := rfl

lemma unit_smul (W : Y.Opens) (r : Γ(Y, W)) (n : Γ(SheafOfModules.unit Y.ringCatSheaf, W)) :
    r • n = (show Γ(Y, W) from r * (show Γ(Y, W) from n)) := rfl

lemma pushforward_unit_smul {Z : Scheme.{u}} (f : Z ⟶ Y) (W : Y.Opens) (r : Γ(Y, W))
    (F : Γ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit Z.ringCatSheaf), W)) :
    r • F = (show Γ(Z, f ⁻¹ᵁ W) from f.app W r * (show Γ(Z, f ⁻¹ᵁ W) from F)) := rfl

section PushUnitBC

variable {Z Z' X' : Scheme.{u}} (φ : Z' ⟶ Z) (ι : Z ⟶ Y) (ι' : Z' ⟶ X') (Ψ : X' ⟶ Y)
  (comm : ι' ≫ Ψ = φ ≫ ι)

def pushUnitBC : (Scheme.Modules.pushforward ι).obj (SheafOfModules.unit Z.ringCatSheaf) ⟶
    (Scheme.Modules.pushforward Ψ).obj
      ((Scheme.Modules.pushforward ι').obj (SheafOfModules.unit Z'.ringCatSheaf)) :=
  (Scheme.Modules.pushforward ι).map
      (show (SheafOfModules.unit Z.ringCatSheaf : Z.Modules) ⟶
          (Scheme.Modules.pushforward φ).obj (SheafOfModules.unit Z'.ringCatSheaf) from
        SheafOfModules.unitToPushforwardObjUnit φ.toRingCatSheafHom) ≫
    (Scheme.Modules.pushforwardComp φ ι).hom.app _ ≫
    (Scheme.Modules.pushforwardCongr comm.symm).hom.app _ ≫
    (Scheme.Modules.pushforwardComp ι' Ψ).inv.app _

include comm in
lemma preimage_preimage_eq (W : Y.Opens) : ι' ⁻¹ᵁ (Ψ ⁻¹ᵁ W) = φ ⁻¹ᵁ (ι ⁻¹ᵁ W) := by
  change (ι' ≫ Ψ) ⁻¹ᵁ W = (φ ≫ ι) ⁻¹ᵁ W
  rw [comm]

lemma pushUnitBC_app (W : Y.Opens) (F : Γ((Scheme.Modules.pushforward ι).obj (SheafOfModules.unit Z.ringCatSheaf), W)) :
    (show Γ(Z', ι' ⁻¹ᵁ (Ψ ⁻¹ᵁ W)) from (pushUnitBC φ ι ι' Ψ comm).app W F) =
      φ.appLE (ι ⁻¹ᵁ W) (ι' ⁻¹ᵁ (Ψ ⁻¹ᵁ W)) (preimage_preimage_eq φ ι ι' Ψ comm W).le
        (show Γ(Z, ι ⁻¹ᵁ W) from F) := by
  rfl

end PushUnitBC
end TwoGluedLinesBCGenAux

namespace TwoGluedLinesBCAux

lemma appLE_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g) {U : Y.Opens} {V : X.Opens}
    (h₁ : V ≤ f ⁻¹ᵁ U) : f.appLE U V h₁ = g.appLE U V (e ▸ h₁) := by
  subst e; rfl

lemma appLE_appLE_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens) (V : Y.Opens)
    (W : X.Opens) (e₁ : V ≤ g ⁻¹ᵁ U) (e₂ : W ≤ f ⁻¹ᵁ V) (r : Γ(Z, U)) :
    f.appLE V W e₂ (g.appLE U V e₁ r) =
      (f ≫ g).appLE U W (e₂.trans ((Opens.map f.base).map (homOfLE e₁)).le) r := by
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_comp_appLE]

lemma map_appLE_apply {X Y : Scheme.{u}} (f : X ⟶ Y) {U U' : Y.Opens} (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U)
    (hU : U ≤ U') (r : Γ(Y, U')) :
    f.appLE U V e (Y.presheaf.map (homOfLE hU).op r) = f.appLE U' V (e.trans (f.preimage_mono hU)) r := by
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE]

lemma appLE_map_apply {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) {V V' : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (hV : V' ≤ V) (r : Γ(Y, U)) :
    X.presheaf.map (homOfLE hV).op (f.appLE U V e r) = f.appLE U V' (hV.trans e) r := by
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]

lemma appTop_res_eq_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) (V : X.Opens) (r : Γ(Y, ⊤)) :
    X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (f.appTop r) = f.appLE ⊤ V le_top r := rfl

variable {κ : Type u} [Field κ] [IsAlgClosed κ]
  {X : Scheme.{u}} (x : X ⟶ Spec (.of κ))
  (M₁ M₂ : CurveModel κ (RatFunc κ)) (i₁ : M₁.C ⟶ X) (i₂ : M₂.C ⟶ X)
  (hi₁ : i₁ ≫ x = M₁.toBase) (hi₂ : i₂ ≫ x = M₂.toBase)
  {s : ℕ} (a b : Fin s → κˣ)
  {T T' : Scheme.{u}} {h : T ⟶ Spec (.of κ)} {h' : T' ⟶ Spec (.of κ)} (ψ : SchemeHomOver h' h)

local notation "XT" => pullback x h
local notation "XT'" => pullback x h'
local notation "Ψ" => baseChangeSnd x ψ
local notation "ι₁" => curveChange i₁ hi₁ h
local notation "ι₂" => curveChange i₂ hi₂ h
local notation "ι₁'" => curveChange i₁ hi₁ h'
local notation "ι₂'" => curveChange i₂ hi₂ h'
local notation "φ₁" => baseChangeSnd M₁.toBase ψ
local notation "φ₂" => baseChangeSnd M₂.toBase ψ
local notation "σ¹" => nodeSectionFst M₁ a h
local notation "σ²" => nodeSectionSnd M₂ b h
local notation "σ¹'" => nodeSectionFst M₁ a h'
local notation "σ²'" => nodeSectionSnd M₂ b h'
local notation "nl" => nodeLocus x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h
local notation "nl'" => nodeLocus x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h'

def unitsBC (u : Fin s → Γ(T, ⊤)ˣ) : Fin s → Γ(T', ⊤)ˣ :=
  fun i => Units.map ψ.1.appTop.hom.toMonoidHom (u i)

omit [IsAlgClosed κ] in
lemma comm₁ : ι₁' ≫ Ψ = φ₁ ≫ ι₁ := curveChange_baseChangeSnd i₁ hi₁ ψ

omit [IsAlgClosed κ] in
lemma comm₂ : ι₂' ≫ Ψ = φ₂ ≫ ι₂ := curveChange_baseChangeSnd i₂ hi₂ ψ

lemma nodeSectionFst_comp (i : Fin s) : σ¹' i ≫ φ₁ = ψ.1 ≫ σ¹ i :=
  rigSection_baseChangeSnd M₁.toBase (pointAt M₁ (a i : κ)) ψ

lemma nodeSectionSnd_comp (i : Fin s) : σ²' i ≫ φ₂ = ψ.1 ≫ σ² i :=
  rigSection_baseChangeSnd M₂.toBase (pointAt M₂ (b i : κ)) ψ

omit [IsAlgClosed κ] in
lemma pre₁ (W : (XT).Opens) : ι₁' ⁻¹ᵁ (Ψ ⁻¹ᵁ W) = φ₁ ⁻¹ᵁ (ι₁ ⁻¹ᵁ W) := by
  change (ι₁' ≫ Ψ) ⁻¹ᵁ W = (φ₁ ≫ ι₁) ⁻¹ᵁ W
  rw [comm₁]

omit [IsAlgClosed κ] in
lemma pre₂ (W : (XT).Opens) : ι₂' ⁻¹ᵁ (Ψ ⁻¹ᵁ W) = φ₂ ⁻¹ᵁ (ι₂ ⁻¹ᵁ W) := by
  change (ι₂' ≫ Ψ) ⁻¹ᵁ W = (φ₂ ≫ ι₂) ⁻¹ᵁ W
  rw [comm₂]

lemma nodeLocus_bc (i : Fin s) (W : (XT).Opens) : nl' i (Ψ ⁻¹ᵁ W) = ψ.1 ⁻¹ᵁ (nl i W) := by
  change (σ¹' i ≫ ι₁' ≫ Ψ) ⁻¹ᵁ W ⊓ (σ²' i ≫ ι₂' ≫ Ψ) ⁻¹ᵁ W =
    ψ.1 ⁻¹ᵁ ((σ¹ i ≫ ι₁) ⁻¹ᵁ W ⊓ (σ² i ≫ ι₂) ⁻¹ᵁ W)
  rw [comm₁, comm₂, ← Category.assoc, ← Category.assoc, nodeSectionFst_comp, nodeSectionSnd_comp,
    Category.assoc, Category.assoc]
  rfl

def bcFst (W : (XT).Opens) (f : Γ(pullback M₁.toBase h, ι₁ ⁻¹ᵁ W)) :
    Γ(pullback M₁.toBase h', ι₁' ⁻¹ᵁ (Ψ ⁻¹ᵁ W)) :=
  (φ₁).appLE (ι₁ ⁻¹ᵁ W) (ι₁' ⁻¹ᵁ (Ψ ⁻¹ᵁ W)) (pre₁ x M₁ i₁ hi₁ ψ W).le f

def bcSnd (W : (XT).Opens) (g : Γ(pullback M₂.toBase h, ι₂ ⁻¹ᵁ W)) :
    Γ(pullback M₂.toBase h', ι₂' ⁻¹ᵁ (Ψ ⁻¹ᵁ W)) :=
  (φ₂).appLE (ι₂ ⁻¹ᵁ W) (ι₂' ⁻¹ᵁ (Ψ ⁻¹ᵁ W)) (pre₂ x M₂ i₂ hi₂ ψ W).le g

lemma nl'_le (i : Fin s) (W : (XT).Opens) : nl' i (Ψ ⁻¹ᵁ W) ≤ ψ.1 ⁻¹ᵁ (nl i W) :=
  (nodeLocus_bc x M₁ M₂ i₁ i₂ hi₁ hi₂ a b ψ i W).le

lemma appLE_fst_bcFst (i : Fin s) (W : (XT).Opens) (f : Γ(pullback M₁.toBase h, ι₁ ⁻¹ᵁ W)) :
    (σ¹' i).appLE (ι₁' ⁻¹ᵁ (Ψ ⁻¹ᵁ W)) (nl' i (Ψ ⁻¹ᵁ W)) inf_le_left (bcFst x M₁ i₁ hi₁ ψ W f) =
      ψ.1.appLE (nl i W) (nl' i (Ψ ⁻¹ᵁ W)) (nl'_le x M₁ M₂ i₁ i₂ hi₁ hi₂ a b ψ i W)
        ((σ¹ i).appLE (ι₁ ⁻¹ᵁ W) (nl i W) inf_le_left f) := by
  unfold bcFst
  rw [appLE_appLE_apply, appLE_appLE_apply, appLE_congr_hom (nodeSectionFst_comp M₁ a ψ i)]

lemma appLE_snd_bcSnd (i : Fin s) (W : (XT).Opens) (g : Γ(pullback M₂.toBase h, ι₂ ⁻¹ᵁ W)) :
    (σ²' i).appLE (ι₂' ⁻¹ᵁ (Ψ ⁻¹ᵁ W)) (nl' i (Ψ ⁻¹ᵁ W)) inf_le_right (bcSnd x M₂ i₂ hi₂ ψ W g) =
      ψ.1.appLE (nl i W) (nl' i (Ψ ⁻¹ᵁ W)) (nl'_le x M₁ M₂ i₁ i₂ hi₁ hi₂ a b ψ i W)
        ((σ² i).appLE (ι₂ ⁻¹ᵁ W) (nl i W) inf_le_right g) := by
  unfold bcSnd
  rw [appLE_appLE_apply, appLE_appLE_apply, appLE_congr_hom (nodeSectionSnd_comp M₂ b ψ i)]

lemma unitsBC_res (u : Fin s → Γ(T, ⊤)ˣ) (i : Fin s) (W : (XT).Opens) :
    T'.presheaf.map (homOfLE le_top).op (unitsBC ψ u i : Γ(T', ⊤)) =
      ψ.1.appLE (nl i W) (nl' i (Ψ ⁻¹ᵁ W)) (nl'_le x M₁ M₂ i₁ i₂ hi₁ hi₂ a b ψ i W)
        (T.presheaf.map (homOfLE le_top).op (u i : Γ(T, ⊤))) := by
  change T'.presheaf.map (homOfLE le_top).op (ψ.1.appTop (u i : Γ(T, ⊤))) = _
  rw [appTop_res_eq_appLE, map_appLE_apply]

theorem nodeCondition_bc (u : Fin s → Γ(T, ⊤)ˣ) (W : (XT).Opens) (i : Fin s)
    (f : Γ(pullback M₁.toBase h, ι₁ ⁻¹ᵁ W)) (g : Γ(pullback M₂.toBase h, ι₂ ⁻¹ᵁ W))
    (hfg : NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h u W i f g) :
    NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h' (unitsBC ψ u) (Ψ ⁻¹ᵁ W) i
      (bcFst x M₁ i₁ hi₁ ψ W f) (bcSnd x M₂ i₂ hi₂ ψ W g) := by
  unfold NodeCondition at hfg ⊢
  rw [appLE_fst_bcFst, appLE_snd_bcSnd, unitsBC_res x M₁ M₂ i₁ i₂ hi₁ hi₂ a b ψ u i W, hfg, map_mul]

open TwoGluedLinesBCGenAux

abbrev PFst (T₀ : Scheme.{u}) (h₀ : T₀ ⟶ Spec (.of κ)) : (pullback x h₀).Modules :=
  (Scheme.Modules.pushforward (curveChange i₁ hi₁ h₀)).obj
    (SheafOfModules.unit (pullback M₁.toBase h₀).ringCatSheaf)

abbrev PSnd (T₀ : Scheme.{u}) (h₀ : T₀ ⟶ Spec (.of κ)) : (pullback x h₀).Modules :=
  (Scheme.Modules.pushforward (curveChange i₂ hi₂ h₀)).obj
    (SheafOfModules.unit (pullback M₂.toBase h₀).ringCatSheaf)

def nodeSet (T₀ : Scheme.{u}) (h₀ : T₀ ⟶ Spec (.of κ)) (u₀ : Fin s → Γ(T₀, ⊤)ˣ) (W : (pullback x h₀).Opens) :
    Set (Γ(PFst x M₁ i₁ hi₁ T₀ h₀, W) × Γ(PSnd x M₂ i₂ hi₂ T₀ h₀, W)) :=
  {fg | ∀ i : Fin s, NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h₀ u₀ W i fg.1 fg.2}

lemma isNodeUnitModule_iff (T₀ : Scheme.{u}) (h₀ : T₀ ⟶ Spec (.of κ)) (u₀ : Fin s → Γ(T₀, ⊤)ˣ)
    (N : (pullback x h₀).Modules) :
    IsNodeUnitModule x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h₀ u₀ N ↔
      ∃ (j₁ : N ⟶ PFst x M₁ i₁ hi₁ T₀ h₀) (j₂ : N ⟶ PSnd x M₂ i₂ hi₂ T₀ h₀),
        ∀ W, Function.Injective (pair j₁ j₂ W) ∧
          Set.range (pair j₁ j₂ W) = nodeSet x M₁ M₂ i₁ i₂ hi₁ hi₂ a b T₀ h₀ u₀ W :=
  Iff.rfl

section Alpha

variable {u : Fin s → Γ(T, ⊤)ˣ}
  {M : (pullback x h).Modules} (j₁ : M ⟶ PFst x M₁ i₁ hi₁ T h) (j₂ : M ⟶ PSnd x M₂ i₂ hi₂ T h)
  (hj : ∀ W, Function.Injective (pair j₁ j₂ W) ∧
    Set.range (pair j₁ j₂ W) = nodeSet x M₁ M₂ i₁ i₂ hi₁ hi₂ a b T h u W)
  {M' : (pullback x h').Modules} (j₁' : M' ⟶ PFst x M₁ i₁ hi₁ T' h') (j₂' : M' ⟶ PSnd x M₂ i₂ hi₂ T' h')
  (hj' : ∀ W', Function.Injective (pair j₁' j₂' W') ∧
    Set.range (pair j₁' j₂' W') = nodeSet x M₁ M₂ i₁ i₂ hi₁ hi₂ a b T' h' (unitsBC ψ u) W')

def τFst : PFst x M₁ i₁ hi₁ T h ⟶ (Scheme.Modules.pushforward Ψ).obj (PFst x M₁ i₁ hi₁ T' h') :=
  pushUnitBC (φ₁) (ι₁) (ι₁') (Ψ) (comm₁ x M₁ i₁ hi₁ ψ)

def τSnd : PSnd x M₂ i₂ hi₂ T h ⟶ (Scheme.Modules.pushforward Ψ).obj (PSnd x M₂ i₂ hi₂ T' h') :=
  pushUnitBC (φ₂) (ι₂) (ι₂') (Ψ) (comm₂ x M₂ i₂ hi₂ ψ)

omit [IsAlgClosed κ] in
lemma τFst_app (W : (XT).Opens) (F : Γ(PFst x M₁ i₁ hi₁ T h, W)) :
    (show Γ(pullback M₁.toBase h', ι₁' ⁻¹ᵁ (Ψ ⁻¹ᵁ W)) from (τFst x M₁ i₁ hi₁ ψ).app W F) =
      bcFst x M₁ i₁ hi₁ ψ W F :=
  pushUnitBC_app _ _ _ _ _ W F

omit [IsAlgClosed κ] in
lemma τSnd_app (W : (XT).Opens) (G : Γ(PSnd x M₂ i₂ hi₂ T h, W)) :
    (show Γ(pullback M₂.toBase h', ι₂' ⁻¹ᵁ (Ψ ⁻¹ᵁ W)) from (τSnd x M₂ i₂ hi₂ ψ).app W G) =
      bcSnd x M₂ i₂ hi₂ ψ W G :=
  pushUnitBC_app _ _ _ _ _ W G

abbrev lFst : (Scheme.Modules.pushforward Ψ).obj M' ⟶ (Scheme.Modules.pushforward Ψ).obj (PFst x M₁ i₁ hi₁ T' h') :=
  (Scheme.Modules.pushforward Ψ).map j₁'

abbrev lSnd : (Scheme.Modules.pushforward Ψ).obj M' ⟶ (Scheme.Modules.pushforward Ψ).obj (PSnd x M₂ i₂ hi₂ T' h') :=
  (Scheme.Modules.pushforward Ψ).map j₂'

omit [IsAlgClosed κ] in
lemma pair_l (W : (XT).Opens) (m' : Γ((Scheme.Modules.pushforward Ψ).obj M', W)) :
    pair (lFst x M₁ i₁ hi₁ ψ j₁') (lSnd x M₂ i₂ hi₂ ψ j₂') W m' =
      pair j₁' j₂' (Ψ ⁻¹ᵁ W) (show Γ(M', Ψ ⁻¹ᵁ W) from m') := rfl

include hj' in
lemma injective_pair_l (W : (XT).Opens) :
    Function.Injective (pair (lFst x M₁ i₁ hi₁ ψ j₁') (lSnd x M₂ i₂ hi₂ ψ j₂') W) :=
  (hj' (Ψ ⁻¹ᵁ W)).1

include hj hj' in
lemma range_pair_k_le (W : (XT).Opens) :
    Set.range (pair (j₁ ≫ τFst x M₁ i₁ hi₁ ψ) (j₂ ≫ τSnd x M₂ i₂ hi₂ ψ) W) ⊆
      Set.range (pair (lFst x M₁ i₁ hi₁ ψ j₁') (lSnd x M₂ i₂ hi₂ ψ j₂') W) := by
  rintro _ ⟨m, rfl⟩
  have hm : pair j₁ j₂ W m ∈ nodeSet x M₁ M₂ i₁ i₂ hi₁ hi₂ a b T h u W := by
    rw [← (hj W).2]; exact ⟨m, rfl⟩
  have : (bcFst x M₁ i₁ hi₁ ψ W (j₁.app W m), bcSnd x M₂ i₂ hi₂ ψ W (j₂.app W m)) ∈
      nodeSet x M₁ M₂ i₁ i₂ hi₁ hi₂ a b T' h' (unitsBC ψ u) (Ψ ⁻¹ᵁ W) :=
    fun i => nodeCondition_bc x M₁ M₂ i₁ i₂ hi₁ hi₂ a b ψ u W i _ _ (hm i)
  rw [← (hj' (Ψ ⁻¹ᵁ W)).2] at this
  obtain ⟨m', hm'⟩ := this
  refine ⟨m', ?_⟩
  rw [pair_l]
  rw [hm']
  rfl

def α : M ⟶ (Scheme.Modules.pushforward Ψ).obj M' :=
  liftHom (j₁ ≫ τFst x M₁ i₁ hi₁ ψ) (j₂ ≫ τSnd x M₂ i₂ hi₂ ψ)
    (lFst x M₁ i₁ hi₁ ψ j₁') (lSnd x M₂ i₂ hi₂ ψ j₂')
    (injective_pair_l x M₁ M₂ i₁ i₂ hi₁ hi₂ a b ψ j₁' j₂' hj')
    (range_pair_k_le x M₁ M₂ i₁ i₂ hi₁ hi₂ a b ψ j₁ j₂ hj j₁' j₂' hj')

lemma jFst_α_app (W : (XT).Opens) (m : Γ(M, W)) :
    (show Γ(pullback M₁.toBase h', ι₁' ⁻¹ᵁ (Ψ ⁻¹ᵁ W)) from
      j₁'.app (Ψ ⁻¹ᵁ W) (show Γ(M', Ψ ⁻¹ᵁ W) from
        (α x M₁ M₂ i₁ i₂ hi₁ hi₂ a b ψ j₁ j₂ hj j₁' j₂' hj').app W m)) =
      bcFst x M₁ i₁ hi₁ ψ W (j₁.app W m) := by
  have := congrArg Prod.fst (pair_liftHom_app (j₁ ≫ τFst x M₁ i₁ hi₁ ψ) (j₂ ≫ τSnd x M₂ i₂ hi₂ ψ)
    (lFst x M₁ i₁ hi₁ ψ j₁') (lSnd x M₂ i₂ hi₂ ψ j₂')
    (injective_pair_l x M₁ M₂ i₁ i₂ hi₁ hi₂ a b ψ j₁' j₂' hj')
    (range_pair_k_le x M₁ M₂ i₁ i₂ hi₁ hi₂ a b ψ j₁ j₂ hj j₁' j₂' hj') W m)
  exact this

lemma jSnd_α_app (W : (XT).Opens) (m : Γ(M, W)) :
    (show Γ(pullback M₂.toBase h', ι₂' ⁻¹ᵁ (Ψ ⁻¹ᵁ W)) from
      j₂'.app (Ψ ⁻¹ᵁ W) (show Γ(M', Ψ ⁻¹ᵁ W) from
        (α x M₁ M₂ i₁ i₂ hi₁ hi₂ a b ψ j₁ j₂ hj j₁' j₂' hj').app W m)) =
      bcSnd x M₂ i₂ hi₂ ψ W (j₂.app W m) := by
  have := congrArg Prod.snd (pair_liftHom_app (j₁ ≫ τFst x M₁ i₁ hi₁ ψ) (j₂ ≫ τSnd x M₂ i₂ hi₂ ψ)
    (lFst x M₁ i₁ hi₁ ψ j₁') (lSnd x M₂ i₂ hi₂ ψ j₂')
    (injective_pair_l x M₁ M₂ i₁ i₂ hi₁ hi₂ a b ψ j₁' j₂' hj')
    (range_pair_k_le x M₁ M₂ i₁ i₂ hi₁ hi₂ a b ψ j₁ j₂ hj j₁' j₂' hj') W m)
  exact this

def θ : (Scheme.Modules.pullback Ψ).obj M ⟶ M' :=
  ((Scheme.Modules.pullbackPushforwardAdjunction Ψ).homEquiv M M').symm
    (α x M₁ M₂ i₁ i₂ hi₁ hi₂ a b ψ j₁ j₂ hj j₁' j₂' hj')

abbrev η : M ⟶ (Scheme.Modules.pushforward Ψ).obj ((Scheme.Modules.pullback Ψ).obj M) :=
  (Scheme.Modules.pullbackPushforwardAdjunction Ψ).unit.app M

lemma θ_app_η_app (W : (XT).Opens) (m : Γ(M, W)) :
    (θ x M₁ M₂ i₁ i₂ hi₁ hi₂ a b ψ j₁ j₂ hj j₁' j₂' hj').app (Ψ ⁻¹ᵁ W)
        (show Γ((Scheme.Modules.pullback Ψ).obj M, Ψ ⁻¹ᵁ W) from (η x ψ (M := M)).app W m) =
      (show Γ(M', Ψ ⁻¹ᵁ W) from (α x M₁ M₂ i₁ i₂ hi₁ hi₂ a b ψ j₁ j₂ hj j₁' j₂' hj').app W m) := by
  have key : η x ψ (M := M) ≫ (Scheme.Modules.pushforward Ψ).map (θ x M₁ M₂ i₁ i₂ hi₁ hi₂ a b ψ j₁ j₂ hj j₁' j₂' hj') =
      α x M₁ M₂ i₁ i₂ hi₁ hi₂ a b ψ j₁ j₂ hj j₁' j₂' hj' := by
    rw [θ]
    exact ((Scheme.Modules.pullbackPushforwardAdjunction Ψ).homEquiv_unit _ _ _).symm.trans
      (Equiv.apply_symm_apply _ _)
  exact congrFun (congrArg (fun k => (ConcreteCategory.hom (Scheme.Modules.Hom.app k W) : Γ(M, W) → _)) key) m

end Alpha

section NodePoints

def αPt (i : Fin s) : closedPoints M₁.C :=
  M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (a i : κ))

def nodePt (i : Fin s) : X := i₁.base (αPt M₁ a i).1

lemma nodePt_injective [IsClosedImmersion i₁] (ha : Function.Injective a) :
    Function.Injective (nodePt M₁ i₁ a) := by
  intro i k hik
  have h1 : (αPt M₁ a i).1 = (αPt M₁ a k).1 := i₁.isClosedEmbedding.injective hik
  have h2 : αPt M₁ a i = αPt M₁ a k := Subtype.ext h1
  have h3 : RationalFunctionField.placeOfPoint κ (a i : κ) = RationalFunctionField.placeOfPoint κ (a k : κ) :=
    M₁.placeEquiv.symm.injective h2
  exact ha (Units.val_injective (RationalFunctionField.placeOfPoint_injective κ h3))

lemma isClosed_nodePt [IsClosedImmersion i₁] (i : Fin s) : IsClosed ({nodePt M₁ i₁ a i} : Set X) := by
  have : IsClosed ({(αPt M₁ a i).1} : Set M₁.C) := (αPt M₁ a i).2
  simpa only [nodePt, Set.image_singleton] using i₁.isClosedEmbedding.isClosedMap _ this

omit [IsAlgClosed κ] in
lemma pointAt_base [IsAlgClosed κ] (M : CurveModel κ (RatFunc κ)) (c : κ) (t : Spec (.of κ)) :
    (pointAt M c).1.base t = (M.placeEquiv.symm (RationalFunctionField.placeOfPoint κ c)).1 := by
  change (pointOfClosedPoint M.toBase _ (M.placeEquiv.symm (RationalFunctionField.placeOfPoint κ c)).2).base t = _
  exact pointOfClosedPoint_apply _ _ _ t

lemma fst_curveChange_nodeSectionFst (k : Fin s) (t : T) :
    (pullback.fst x h).base ((ι₁).base ((σ¹ k).base t)) = nodePt M₁ i₁ a k := by
  have e : σ¹ k ≫ ι₁ ≫ pullback.fst x h = (h ≫ (pointAt M₁ (a k : κ)).1) ≫ i₁ := by
    rw [curveChange, pullback.lift_fst, ← Category.assoc, nodeSectionFst, rigSection, pullback.lift_fst]
  change (σ¹ k ≫ ι₁ ≫ pullback.fst x h) t = _
  rw [e, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  rw [pointAt_base]
  rfl

lemma nodeLocus_eq_bot (k : Fin s) {W : (XT).Opens} {V : X.Opens} (hW : W ≤ (pullback.fst x h) ⁻¹ᵁ V)
    (hk : nodePt M₁ i₁ a k ∉ V) : nl k W = ⊥ := by
  rw [eq_bot_iff]
  intro t ht
  exfalso
  apply hk
  have h1 : (ι₁).base ((σ¹ k).base t) ∈ W := ht.1
  have h2 := hW h1
  rw [← fst_curveChange_nodeSectionFst x M₁ i₁ hi₁ a k t]
  exact h2

lemma nodeCondition_of_eq_bot (u : Fin s → Γ(T, ⊤)ˣ) (k : Fin s) (W : (XT).Opens) (hbot : nl k W = ⊥)
    (F : Γ(pullback M₁.toBase h, ι₁ ⁻¹ᵁ W)) (G : Γ(pullback M₂.toBase h, ι₂ ⁻¹ᵁ W)) :
    NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h u W k F G := by
  haveI : Subsingleton Γ(T, nl k W) :=
    CommRingCat.subsingleton_of_isTerminal (T.sheaf.isTerminalOfEqEmpty hbot)
  exact Subsingleton.elim _ _

def unitFn (u : Fin s → Γ(T, ⊤)ˣ) (i : Fin s) (W : (XT).Opens) : Γ(pullback M₁.toBase h, ι₁ ⁻¹ᵁ W) :=
  (pullback M₁.toBase h).presheaf.map (homOfLE le_top).op ((pullback.snd M₁.toBase h).appTop (u i : Γ(T, ⊤)))

omit [IsAlgClosed κ] in
lemma isUnit_unitFn [IsAlgClosed κ] (u : Fin s → Γ(T, ⊤)ˣ) (i : Fin s) (W : (XT).Opens) :
    IsUnit (unitFn x M₁ i₁ hi₁ u i W) :=
  ((u i).isUnit.map _).map _

lemma id_appLE {Y : Scheme.{u}} (U V : Y.Opens) (e : V ≤ U) :
    (𝟙 Y : Y ⟶ Y).appLE U V e = Y.presheaf.map (homOfLE e).op := by
  rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
  exact Category.id_comp _

lemma nodeCondition_unitFn_one (u : Fin s → Γ(T, ⊤)ˣ) (i : Fin s) (W : (XT).Opens) :
    NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h u W i (unitFn x M₁ i₁ hi₁ u i W) 1 := by
  unfold NodeCondition unitFn
  rw [map_one, mul_one, appTop_res_eq_appLE, appLE_appLE_apply,
    appLE_congr_hom (show σ¹ i ≫ pullback.snd M₁.toBase h = 𝟙 T from pullback.lift_snd _ _ _), id_appLE]

theorem exists_unit_pair [IsClosedImmersion i₁] (ha : Function.Injective a) (u : Fin s → Γ(T, ⊤)ˣ)
    (n : ↥(pullback x h)) :
    ∃ W : (XT).Opens, n ∈ W ∧ ∃ (F : Γ(pullback M₁.toBase h, ι₁ ⁻¹ᵁ W)) (G : Γ(pullback M₂.toBase h, ι₂ ⁻¹ᵁ W)),
      IsUnit F ∧ IsUnit G ∧ ∀ k, NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h u W k F G := by
  classical
  let x₀ : X := (pullback.fst x h).base n

  let S : Set X := ⋃ k ∈ ({k : Fin s | nodePt M₁ i₁ a k ≠ x₀} : Set (Fin s)), {nodePt M₁ i₁ a k}
  have hS : IsClosed S := Set.Finite.isClosed_biUnion (Set.toFinite _) fun k _ => isClosed_nodePt M₁ i₁ a k
  let V : X.Opens := ⟨Sᶜ, hS.isOpen_compl⟩
  have hx₀V : x₀ ∈ V := by
    change x₀ ∉ S
    simp only [S, Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_setOf_eq, not_exists]
    exact fun k hk e => hk e.symm
  have hV : ∀ k, nodePt M₁ i₁ a k ∈ V → nodePt M₁ i₁ a k = x₀ := by
    intro k hk
    by_contra hne
    exact hk (Set.mem_biUnion (show k ∈ {k : Fin s | nodePt M₁ i₁ a k ≠ x₀} from hne) rfl)
  let W : (XT).Opens := (pullback.fst x h) ⁻¹ᵁ V
  refine ⟨W, hx₀V, ?_⟩
  by_cases hex : ∃ i, nodePt M₁ i₁ a i = x₀
  · obtain ⟨i, hi⟩ := hex
    refine ⟨unitFn x M₁ i₁ hi₁ u i W, 1, isUnit_unitFn x M₁ i₁ hi₁ u i W, isUnit_one, fun k => ?_⟩
    by_cases hk : nodePt M₁ i₁ a k ∈ V
    · obtain rfl : k = i := nodePt_injective M₁ i₁ a ha ((hV k hk).trans hi.symm)
      exact nodeCondition_unitFn_one x M₁ M₂ i₁ i₂ hi₁ hi₂ a b u k W
    · exact nodeCondition_of_eq_bot x M₁ M₂ i₁ i₂ hi₁ hi₂ a b u k W
        (nodeLocus_eq_bot x M₁ M₂ i₁ i₂ hi₁ hi₂ a b k le_rfl hk) _ _
  · refine ⟨1, 1, isUnit_one, isUnit_one, fun k => ?_⟩
    have hk : nodePt M₁ i₁ a k ∉ V := fun hk => hex ⟨k, hV k hk⟩
    exact nodeCondition_of_eq_bot x M₁ M₂ i₁ i₂ hi₁ hi₂ a b u k W
      (nodeLocus_eq_bot x M₁ M₂ i₁ i₂ hi₁ hi₂ a b k le_rfl hk) _ _

end NodePoints

section Res

variable (u : Fin s → Γ(T, ⊤)ˣ)

lemma nodeLocus_mono (i : Fin s) {W W' : (XT).Opens} (hW : W' ≤ W) : nl i W' ≤ nl i W :=
  inf_le_inf (Scheme.Hom.preimage_mono _ (Scheme.Hom.preimage_mono _ hW))
    (Scheme.Hom.preimage_mono _ (Scheme.Hom.preimage_mono _ hW))

lemma appLE_fst_res (i : Fin s) {W W' : (XT).Opens} (hW : W' ≤ W)
    (f : Γ(pullback M₁.toBase h, ι₁ ⁻¹ᵁ W)) :
    (σ¹ i).appLE (ι₁ ⁻¹ᵁ W') (nl i W') inf_le_left
        ((pullback M₁.toBase h).presheaf.map (homOfLE (Scheme.Hom.preimage_mono ι₁ hW)).op f) =
      T.presheaf.map (homOfLE (nodeLocus_mono x M₁ M₂ i₁ i₂ hi₁ hi₂ a b i hW)).op
        ((σ¹ i).appLE (ι₁ ⁻¹ᵁ W) (nl i W) inf_le_left f) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE,
    Scheme.Hom.appLE_map]

lemma appLE_snd_res (i : Fin s) {W W' : (XT).Opens} (hW : W' ≤ W)
    (g : Γ(pullback M₂.toBase h, ι₂ ⁻¹ᵁ W)) :
    (σ² i).appLE (ι₂ ⁻¹ᵁ W') (nl i W') inf_le_right
        ((pullback M₂.toBase h).presheaf.map (homOfLE (Scheme.Hom.preimage_mono ι₂ hW)).op g) =
      T.presheaf.map (homOfLE (nodeLocus_mono x M₁ M₂ i₁ i₂ hi₁ hi₂ a b i hW)).op
        ((σ² i).appLE (ι₂ ⁻¹ᵁ W) (nl i W) inf_le_right g) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE,
    Scheme.Hom.appLE_map]

omit [IsAlgClosed κ] in
lemma unit_res {V V' : T.Opens} (hV : V' ≤ V) (i : Fin s) :
    T.presheaf.map (homOfLE hV).op (T.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (u i : Γ(T, ⊤))) =
      T.presheaf.map (homOfLE (le_top : V' ≤ ⊤)).op (u i : Γ(T, ⊤)) := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl

theorem nodeCondition_res (i : Fin s) {W W' : (XT).Opens} (hW : W' ≤ W)
    (f : Γ(pullback M₁.toBase h, ι₁ ⁻¹ᵁ W)) (g : Γ(pullback M₂.toBase h, ι₂ ⁻¹ᵁ W))
    (hfg : NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h u W i f g) :
    NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h u W' i
      ((pullback M₁.toBase h).presheaf.map (homOfLE (Scheme.Hom.preimage_mono ι₁ hW)).op f)
      ((pullback M₂.toBase h).presheaf.map (homOfLE (Scheme.Hom.preimage_mono ι₂ hW)).op g) := by
  unfold NodeCondition at hfg ⊢
  rw [appLE_fst_res x M₁ M₂ i₁ i₂ hi₁ hi₂ a b i hW f, appLE_snd_res x M₁ M₂ i₁ i₂ hi₁ hi₂ a b i hW g, hfg,
    map_mul, unit_res]

end Res

section FrameUnits

variable {u : Fin s → Γ(T, ⊤)ˣ}
  {M : (pullback x h).Modules} (j₁ : M ⟶ PFst x M₁ i₁ hi₁ T h) (j₂ : M ⟶ PSnd x M₂ i₂ hi₂ T h)
  (hj : ∀ W, Function.Injective (pair j₁ j₂ W) ∧
    Set.range (pair j₁ j₂ W) = nodeSet x M₁ M₂ i₁ i₂ hi₁ hi₂ a b T h u W)

include hj in

theorem isUnit_germ_of_isFrameOn [IsClosedImmersion i₁] (ha : Function.Injective a)
    {U : (XT).Opens} {e : Γ(M, U)} (he : Scheme.Modules.IsFrameOn e U) :
    (∀ (q : ↥(pullback M₁.toBase h)) (hq : q ∈ ι₁ ⁻¹ᵁ U),
      IsUnit ((pullback M₁.toBase h).presheaf.germ (ι₁ ⁻¹ᵁ U) q hq
        (show Γ(pullback M₁.toBase h, ι₁ ⁻¹ᵁ U) from j₁.app U e))) ∧
    (∀ (q : ↥(pullback M₂.toBase h)) (hq : q ∈ ι₂ ⁻¹ᵁ U),
      IsUnit ((pullback M₂.toBase h).presheaf.germ (ι₂ ⁻¹ᵁ U) q hq
        (show Γ(pullback M₂.toBase h, ι₂ ⁻¹ᵁ U) from j₂.app U e))) := by

  have key : ∀ n ∈ U, ∃ (W₀ : (XT).Opens) (hW₀ : W₀ ≤ U), n ∈ W₀ ∧ ∃ (r : Γ(XT, W₀))
      (F₀ : Γ(pullback M₁.toBase h, ι₁ ⁻¹ᵁ W₀)) (G₀ : Γ(pullback M₂.toBase h, ι₂ ⁻¹ᵁ W₀)),
      IsUnit F₀ ∧ IsUnit G₀ ∧
      F₀ = (ι₁).app W₀ r * (pullback M₁.toBase h).presheaf.map (homOfLE (Scheme.Hom.preimage_mono ι₁ hW₀)).op
          (show Γ(pullback M₁.toBase h, ι₁ ⁻¹ᵁ U) from j₁.app U e) ∧
      G₀ = (ι₂).app W₀ r * (pullback M₂.toBase h).presheaf.map (homOfLE (Scheme.Hom.preimage_mono ι₂ hW₀)).op
          (show Γ(pullback M₂.toBase h, ι₂ ⁻¹ᵁ U) from j₂.app U e) := by
    intro n hn
    obtain ⟨W, hnW, F, G, hF, hG, hFG⟩ := exists_unit_pair x M₁ M₂ i₁ i₂ hi₁ hi₂ a b ha u n
    let W₀ : (XT).Opens := U ⊓ W
    have hW₀U : W₀ ≤ U := inf_le_left
    have hW₀W : W₀ ≤ W := inf_le_right
    let F₀ := (pullback M₁.toBase h).presheaf.map (homOfLE (Scheme.Hom.preimage_mono ι₁ hW₀W)).op F
    let G₀ := (pullback M₂.toBase h).presheaf.map (homOfLE (Scheme.Hom.preimage_mono ι₂ hW₀W)).op G
    have hFG₀ : (F₀, G₀) ∈ nodeSet x M₁ M₂ i₁ i₂ hi₁ hi₂ a b T h u W₀ :=
      fun k => nodeCondition_res x M₁ M₂ i₁ i₂ hi₁ hi₂ a b u k hW₀W F G (hFG k)
    rw [← (hj W₀).2] at hFG₀
    obtain ⟨m, hm⟩ := hFG₀
    obtain ⟨r, hr⟩ := exists_eq_smul_of_isFrameOn he hW₀U hW₀U m
    refine ⟨W₀, hW₀U, ⟨hn, hnW⟩, r, F₀, G₀, hF.map _, hG.map _, ?_, ?_⟩
    · have h1 : F₀ = (pair j₁ j₂ W₀ m).1 := (congrArg Prod.fst hm).symm
      rw [h1, hr, pair_smul]
      change (ι₁).app W₀ r * (show Γ(pullback M₁.toBase h, ι₁ ⁻¹ᵁ W₀) from
        j₁.app W₀ (M.presheaf.map (homOfLE hW₀U).op e)) = _
      rw [app_map]
      rfl
    · have h1 : G₀ = (pair j₁ j₂ W₀ m).2 := (congrArg Prod.snd hm).symm
      rw [h1, hr, pair_smul]
      change (ι₂).app W₀ r * (show Γ(pullback M₂.toBase h, ι₂ ⁻¹ᵁ W₀) from
        j₂.app W₀ (M.presheaf.map (homOfLE hW₀U).op e)) = _
      rw [app_map]
      rfl
  constructor
  · intro q hq
    obtain ⟨W₀, hW₀, hnW₀, r, F₀, G₀, hF₀, -, hF, -⟩ := key _ hq
    have hq₀ : q ∈ ι₁ ⁻¹ᵁ W₀ := hnW₀
    have hgerm := hF₀.map ((pullback M₁.toBase h).presheaf.germ (ι₁ ⁻¹ᵁ W₀) q hq₀).hom
    rw [hF, map_mul, TopCat.Presheaf.germ_res_apply] at hgerm
    exact isUnit_of_mul_isUnit_right hgerm
  · intro q hq
    obtain ⟨W₀, hW₀, hnW₀, r, F₀, G₀, -, hG₀, -, hG⟩ := key _ hq
    have hq₀ : q ∈ ι₂ ⁻¹ᵁ W₀ := hnW₀
    have hgerm := hG₀.map ((pullback M₂.toBase h).presheaf.germ (ι₂ ⁻¹ᵁ W₀) q hq₀).hom
    rw [hG, map_mul, TopCat.Presheaf.germ_res_apply] at hgerm
    exact isUnit_of_mul_isUnit_right hgerm

end FrameUnits

section Cover

omit [IsAlgClosed κ] in
lemma isPullback_curveChange_fst :
    IsPullback (pullback.fst M₁.toBase h) (ι₁) i₁ (pullback.fst x h) := by
  refine IsPullback.of_bot ?_ (by rw [curveChange, pullback.lift_fst]) (IsPullback.of_hasPullback x h)
  rw [curveChange_snd, hi₁]
  exact IsPullback.of_hasPullback _ _

omit [IsAlgClosed κ] in
lemma isPullback_curveChange_snd :
    IsPullback (pullback.fst M₂.toBase h) (ι₂) i₂ (pullback.fst x h) := by
  refine IsPullback.of_bot ?_ (by rw [curveChange, pullback.lift_fst]) (IsPullback.of_hasPullback x h)
  rw [curveChange_snd, hi₂]
  exact IsPullback.of_hasPullback _ _

omit [IsAlgClosed κ] in
lemma exists_preimage_of_isPullback {P A B C : Scheme.{u}} {fst : P ⟶ A} {snd : P ⟶ B} {f : A ⟶ C}
    {g : B ⟶ C} (H : IsPullback fst snd f g) (a₀ : A) (b₀ : B) (e : f.base a₀ = g.base b₀) :
    ∃ p : P, snd.base p = b₀ := by
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) a₀ b₀ e
  refine ⟨H.isoPullback.inv.base z, ?_⟩
  change (H.isoPullback.inv ≫ snd) z = b₀
  rw [H.isoPullback_inv_snd]
  exact hz

omit [IsAlgClosed κ] in

theorem exists_preimage_curveChange (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (p : ↥(pullback x h)) :
    (∃ q, (ι₁).base q = p) ∨ (∃ q, (ι₂).base q = p) := by
  have hx₀ : (pullback.fst x h).base p ∈ Set.range i₁.base ∪ Set.range i₂.base := by
    rw [hcover]; trivial
  rcases hx₀ with ⟨q₀, hq₀⟩ | ⟨q₀, hq₀⟩
  · exact Or.inl (exists_preimage_of_isPullback (isPullback_curveChange_fst x M₁ i₁ hi₁) q₀ p hq₀)
  · exact Or.inr (exists_preimage_of_isPullback (isPullback_curveChange_snd x M₂ i₂ hi₂) q₀ p hq₀)

end Cover

section OfIso

lemma isNodeUnitModule_of_iso {T₀ : Scheme.{u}} {h₀ : T₀ ⟶ Spec (.of κ)} {u₀ : Fin s → Γ(T₀, ⊤)ˣ}
    {N N' : (pullback x h₀).Modules} (e : N ≅ N') (hN' : IsNodeUnitModule x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h₀ u₀ N') :
    IsNodeUnitModule x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h₀ u₀ N := by
  obtain ⟨j₁, j₂, hj⟩ := hN'
  refine ⟨e.hom ≫ j₁, e.hom ≫ j₂, fun W => ?_⟩
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

end OfIso

section Main

variable {u : Fin s → Γ(T, ⊤)ˣ}
  {M : (pullback x h).Modules} (j₁ : M ⟶ PFst x M₁ i₁ hi₁ T h) (j₂ : M ⟶ PSnd x M₂ i₂ hi₂ T h)
  (hj : ∀ W, Function.Injective (pair j₁ j₂ W) ∧
    Set.range (pair j₁ j₂ W) = nodeSet x M₁ M₂ i₁ i₂ hi₁ hi₂ a b T h u W)
  {M' : (pullback x h').Modules} (j₁' : M' ⟶ PFst x M₁ i₁ hi₁ T' h') (j₂' : M' ⟶ PSnd x M₂ i₂ hi₂ T' h')
  (hj' : ∀ W', Function.Injective (pair j₁' j₂' W') ∧
    Set.range (pair j₁' j₂' W') = nodeSet x M₁ M₂ i₁ i₂ hi₁ hi₂ a b T' h' (unitsBC ψ u) W')

local notation "θ₀" => θ x M₁ M₂ i₁ i₂ hi₁ hi₂ a b ψ j₁ j₂ hj j₁' j₂' hj'
local notation "α₀" => α x M₁ M₂ i₁ i₂ hi₁ hi₂ a b ψ j₁ j₂ hj j₁' j₂' hj'

lemma germ_appLE {Y Z : Scheme.{u}} (f : Z ⟶ Y) (U : Y.Opens) (V : Z.Opens) (e : V ≤ f ⁻¹ᵁ U) (z : Z)
    (hz : z ∈ V) (r : Γ(Y, U)) :
    Z.presheaf.germ V z hz (f.appLE U V e r) = f.stalkMap z (Y.presheaf.germ U (f z) (e hz) r) := by
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE, CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]

include hj hj' in

theorem exists_isFrameOn_α_app [IsClosedImmersion i₁] (ha : Function.Injective a)
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (hM' : Scheme.Modules.IsInvertible M') {U : (XT).Opens} {e : Γ(M, U)}
    (he : Scheme.Modules.IsFrameOn e U) (p : ↥(pullback x h')) (hp : p ∈ Ψ ⁻¹ᵁ U) :
    ∃ (V₀ : (XT').Opens) (hV₀ : V₀ ≤ Ψ ⁻¹ᵁ U), p ∈ V₀ ∧
      Scheme.Modules.IsFrameOn (M'.presheaf.map (homOfLE hV₀).op
        (show Γ(M', Ψ ⁻¹ᵁ U) from (α₀).app U e)) V₀ := by

  obtain ⟨U', hpU', ⟨eU'⟩⟩ := hM'.1 p
  obtain ⟨e', he'⟩ := Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit U' eU'
  let m : Γ(M', Ψ ⁻¹ᵁ U) := (α₀).app U e
  let V : (XT').Opens := Ψ ⁻¹ᵁ U ⊓ U'
  have hVU : V ≤ Ψ ⁻¹ᵁ U := inf_le_left
  have hVU' : V ≤ U' := inf_le_right
  have hpV : p ∈ V := ⟨hp, hpU'⟩

  obtain ⟨c, hc⟩ := exists_eq_smul_of_isFrameOn he' hVU' hVU' (M'.presheaf.map (homOfLE hVU).op m)

  have hunits := isUnit_germ_of_isFrameOn x M₁ M₂ i₁ i₂ hi₁ hi₂ a b j₁ j₂ hj ha he

  have hcp : IsUnit ((XT').presheaf.germ V p hpV c) := by
    rcases exists_preimage_curveChange x M₁ M₂ i₁ i₂ hi₁ hi₂ hcover p with ⟨q', rfl⟩ | ⟨q', rfl⟩
    ·
      have hq'V : q' ∈ ι₁' ⁻¹ᵁ V := hpV

      have h1 : (show Γ(pullback M₁.toBase h', ι₁' ⁻¹ᵁ V) from j₁'.app V (M'.presheaf.map (homOfLE hVU).op m)) =
          (ι₁').app V c * (show Γ(pullback M₁.toBase h', ι₁' ⁻¹ᵁ V) from
            j₁'.app V (M'.presheaf.map (homOfLE hVU').op e')) := by
        rw [hc, Scheme.Modules.Hom.app_smul]; rfl
      have h2 : (show Γ(pullback M₁.toBase h', ι₁' ⁻¹ᵁ V) from j₁'.app V (M'.presheaf.map (homOfLE hVU).op m)) =
          (φ₁).appLE (ι₁ ⁻¹ᵁ U) (ι₁' ⁻¹ᵁ V) ((Scheme.Hom.preimage_mono _ hVU).trans (pre₁ x M₁ i₁ hi₁ ψ U).le)
            (show Γ(pullback M₁.toBase h, ι₁ ⁻¹ᵁ U) from j₁.app U e) := by
        rw [app_map]
        change (pullback M₁.toBase h').presheaf.map (homOfLE (Scheme.Hom.preimage_mono _ hVU)).op
          (show Γ(pullback M₁.toBase h', ι₁' ⁻¹ᵁ (Ψ ⁻¹ᵁ U)) from j₁'.app (Ψ ⁻¹ᵁ U) m) = _
        rw [jFst_α_app, bcFst, appLE_map_apply]
      have hmem : (φ₁).base q' ∈ ι₁ ⁻¹ᵁ U :=
        ((Scheme.Hom.preimage_mono _ hVU).trans (pre₁ x M₁ i₁ hi₁ ψ U).le) hq'V
      have hu1 := hunits.1 ((φ₁).base q') hmem
      have hu2 : IsUnit ((pullback M₁.toBase h').presheaf.germ (ι₁' ⁻¹ᵁ V) q' hq'V
          ((φ₁).appLE (ι₁ ⁻¹ᵁ U) (ι₁' ⁻¹ᵁ V) ((Scheme.Hom.preimage_mono _ hVU).trans (pre₁ x M₁ i₁ hi₁ ψ U).le)
            (show Γ(pullback M₁.toBase h, ι₁ ⁻¹ᵁ U) from j₁.app U e))) := by
        rw [germ_appLE]
        exact hu1.map _
      rw [← h2, h1, map_mul] at hu2
      have hu3 := isUnit_of_mul_isUnit_left hu2
      rw [Scheme.Hom.app_eq_appLE, germ_appLE] at hu3
      exact (isUnit_map_iff ((ι₁').stalkMap q').hom _).1 hu3
    ·
      have hq'V : q' ∈ ι₂' ⁻¹ᵁ V := hpV
      have h1 : (show Γ(pullback M₂.toBase h', ι₂' ⁻¹ᵁ V) from j₂'.app V (M'.presheaf.map (homOfLE hVU).op m)) =
          (ι₂').app V c * (show Γ(pullback M₂.toBase h', ι₂' ⁻¹ᵁ V) from
            j₂'.app V (M'.presheaf.map (homOfLE hVU').op e')) := by
        rw [hc, Scheme.Modules.Hom.app_smul]; rfl
      have h2 : (show Γ(pullback M₂.toBase h', ι₂' ⁻¹ᵁ V) from j₂'.app V (M'.presheaf.map (homOfLE hVU).op m)) =
          (φ₂).appLE (ι₂ ⁻¹ᵁ U) (ι₂' ⁻¹ᵁ V) ((Scheme.Hom.preimage_mono _ hVU).trans (pre₂ x M₂ i₂ hi₂ ψ U).le)
            (show Γ(pullback M₂.toBase h, ι₂ ⁻¹ᵁ U) from j₂.app U e) := by
        rw [app_map]
        change (pullback M₂.toBase h').presheaf.map (homOfLE (Scheme.Hom.preimage_mono _ hVU)).op
          (show Γ(pullback M₂.toBase h', ι₂' ⁻¹ᵁ (Ψ ⁻¹ᵁ U)) from j₂'.app (Ψ ⁻¹ᵁ U) m) = _
        rw [jSnd_α_app, bcSnd, appLE_map_apply]
      have hmem : (φ₂).base q' ∈ ι₂ ⁻¹ᵁ U :=
        ((Scheme.Hom.preimage_mono _ hVU).trans (pre₂ x M₂ i₂ hi₂ ψ U).le) hq'V
      have hu1 := hunits.2 ((φ₂).base q') hmem
      have hu2 : IsUnit ((pullback M₂.toBase h').presheaf.germ (ι₂' ⁻¹ᵁ V) q' hq'V
          ((φ₂).appLE (ι₂ ⁻¹ᵁ U) (ι₂' ⁻¹ᵁ V) ((Scheme.Hom.preimage_mono _ hVU).trans (pre₂ x M₂ i₂ hi₂ ψ U).le)
            (show Γ(pullback M₂.toBase h, ι₂ ⁻¹ᵁ U) from j₂.app U e))) := by
        rw [germ_appLE]
        exact hu1.map _
      rw [← h2, h1, map_mul] at hu2
      have hu3 := isUnit_of_mul_isUnit_left hu2
      rw [Scheme.Hom.app_eq_appLE, germ_appLE] at hu3
      exact (isUnit_map_iff ((ι₂').stalkMap q').hom _).1 hu3

  let V₀ : (XT').Opens := (XT').basicOpen c
  have hV₀V : V₀ ≤ V := (XT').basicOpen_le c
  have hpV₀ : p ∈ V₀ := (Scheme.mem_basicOpen (XT') c p hpV).2 hcp
  have hcunit : IsUnit ((XT').presheaf.map (homOfLE hV₀V).op c) :=
    (XT').toLocallyRingedSpace.toRingedSpace.isUnit_res_basicOpen c
  refine ⟨V₀, hV₀V.trans hVU, hpV₀, ?_⟩
  have hres : M'.presheaf.map (homOfLE (hV₀V.trans hVU)).op m =
      (XT').presheaf.map (homOfLE hV₀V).op c • M'.presheaf.map (homOfLE (hV₀V.trans hVU')).op e' := by
    have : M'.presheaf.map (homOfLE (hV₀V.trans hVU)).op m =
        M'.presheaf.map (homOfLE hV₀V).op (M'.presheaf.map (homOfLE hVU).op m) := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl
    rw [this, hc, Scheme.Modules.map_smul, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  change Scheme.Modules.IsFrameOn (M'.presheaf.map (homOfLE (hV₀V.trans hVU)).op m) V₀
  rw [hres]
  exact isFrameOn_smul ((he'.map (homOfLE (hV₀V.trans hVU'))).mono (hV₀V.trans hVU')) hcunit

include hj hj' in

theorem isIso_θ [IsClosedImmersion i₁] (ha : Function.Injective a)
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (hM : Scheme.Modules.IsInvertible M) (hM' : Scheme.Modules.IsInvertible M') : IsIso (θ₀) := by
  refine isIso_of_locally_isFrameOn_app (θ₀) (hM.pullback _) fun p => ?_

  obtain ⟨U, hyU, ⟨eU⟩⟩ := hM.1 ((Ψ).base p)
  obtain ⟨e, he⟩ := Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit U eU
  obtain ⟨V₀, hV₀, hpV₀, hfr⟩ :=
    exists_isFrameOn_α_app x M₁ M₂ i₁ i₂ hi₁ hi₂ a b ψ j₁ j₂ hj j₁' j₂' hj' ha hcover hM' he p hyU
  refine ⟨V₀, hpV₀, ((Scheme.Modules.pullback Ψ).obj M).presheaf.map (homOfLE hV₀).op
    (show Γ((Scheme.Modules.pullback Ψ).obj M, Ψ ⁻¹ᵁ U) from (η x ψ (M := M)).app U e), ?_⟩
  rw [app_res, θ_app_η_app]
  exact hfr

end Main

end TwoGluedLinesBCAux

end

open TwoGluedLinesBCGenAux TwoGluedLinesBCAux in

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
    {T : Scheme.{u}} {h : T ⟶ Spec (.of κ)} {u : Fin s → Γ(T, ⊤)ˣ} {M : (pullback x h).Modules}
    (hM : Scheme.Modules.IsInvertible M) (hu : IsNodeUnitModule x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h u M)
    {T' : Scheme.{u}} {h' : T' ⟶ Spec (.of κ)} (ψ : SchemeHomOver h' h) :
    IsNodeUnitModule x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h'
      (fun i => Units.map ψ.1.appTop.hom.toMonoidHom (u i))
      ((Scheme.Modules.pullback (baseChangeSnd x ψ)).obj M) := by

  obtain ⟨M', hM', hM'nu⟩ := AlgebraicGeometry.TwoGluedProjectiveLines.exists_isInvertible_isNodeUnitModule
    κ x M₁ M₂ i₁ i₂ hi₁ hi₂ hcover a b ha hnode hinter htrans h' (fun i => Units.map ψ.1.appTop.hom.toMonoidHom (u i))
  obtain ⟨j₁, j₂, hj⟩ := hu
  obtain ⟨j₁', j₂', hj'⟩ := hM'nu
  haveI := isIso_θ x M₁ M₂ i₁ i₂ hi₁ hi₂ a b ψ j₁ j₂ hj j₁' j₂' hj' ha hcover hM hM'
  exact isNodeUnitModule_of_iso x M₁ M₂ i₁ i₂ hi₁ hi₂ a b
    (asIso (θ x M₁ M₂ i₁ i₂ hi₁ hi₂ a b ψ j₁ j₂ hj j₁' j₂' hj')) ⟨j₁', j₂', hj'⟩

end S_AlgebraicGeometry_TwoGluedProjectiveLines_IsNodeUnitModule_pullback_baseChangeSnd
end P2MW
export P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_IsNodeUnitModule_pullback_baseChangeSnd (solution)
