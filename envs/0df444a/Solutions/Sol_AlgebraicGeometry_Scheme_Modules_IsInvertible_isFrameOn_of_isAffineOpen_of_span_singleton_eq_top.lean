-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.isFrameOn_of_isAffineOpen_of_span_singleton_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/c177c968-9fc4-56ba-a68d-e8ad0e4e58a0

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafSectionsLinearRes
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isLocalizedModule_res_of_isQuasicoherent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_isFrameOn_of_isAffineOpen_of_span_singleton_eq_top

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace P2mGenFrame

variable {X : Scheme.{u}} {M : X.Modules}

theorem map_map {A B C : X.Opens} (hBA : B ≤ A) (hCB : C ≤ B) (s : Γ(M, A)) :
    M.presheaf.map (homOfLE hCB).op (M.presheaf.map (homOfLE hBA).op s) =
      M.presheaf.map (homOfLE (hCB.trans hBA)).op s := by
  rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp]; rfl

theorem rmap_rmap {A B C : X.Opens} (hBA : B ≤ A) (hCB : C ≤ B) (g : Γ(X, A)) :
    X.presheaf.map (homOfLE hCB).op (X.presheaf.map (homOfLE hBA).op g) =
      X.presheaf.map (homOfLE (hCB.trans hBA)).op g := by
  rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]; rfl

theorem map_smul' {A B : X.Opens} (h : B ≤ A) (g : Γ(X, A)) (s : Γ(M, A)) :
    M.presheaf.map (homOfLE h).op (g • s) =
      X.presheaf.map (homOfLE h).op g • M.presheaf.map (homOfLE h).op s :=
  Scheme.Modules.map_smul M (homOfLE h) g s

theorem isFrameOn_smul_of_isUnit {U V : X.Opens} {s : Γ(M, U)} (h : Scheme.Modules.IsFrameOn s V)
    {g : Γ(X, U)} (hg : IsUnit g) : Scheme.Modules.IsFrameOn (g • s) V := by
  intro W hWU hWV
  have e : (fun a : Γ(X, W) => a • M.presheaf.map (homOfLE hWU).op (g • s)) =
      (fun a : Γ(X, W) => a • M.presheaf.map (homOfLE hWU).op s) ∘
        fun a : Γ(X, W) => a * X.presheaf.map (homOfLE hWU).op g := by
    funext a
    simp only [Function.comp_apply, map_smul', mul_smul]
  rw [e]
  refine (h hWU hWV).comp ?_
  have hg' : IsUnit (X.presheaf.map (homOfLE hWU).op g) := hg.map _
  exact (Units.mulRight_bijective hg'.unit)

theorem isFrameOn_of_isFrameOn_map {U U' V : X.Opens} {s : Γ(M, U)} (hU' : U' ≤ U) (hVU' : V ≤ U')
    (h : Scheme.Modules.IsFrameOn (M.presheaf.map (homOfLE hU').op s) V) :
    Scheme.Modules.IsFrameOn s V := by
  intro W hWU hWV
  have e : M.presheaf.map (homOfLE hWU).op s =
      M.presheaf.map (homOfLE (hWV.trans hVU')).op (M.presheaf.map (homOfLE hU').op s) := by
    rw [map_map]
  rw [e]
  exact h (hWV.trans hVU') hWV

theorem isFrameOn_of_locally {U V : X.Opens} {s : Γ(M, U)}
    (h : ∀ x ∈ V, ∃ V' : X.Opens, x ∈ V' ∧ V' ≤ V ∧ Scheme.Modules.IsFrameOn s V') :
    Scheme.Modules.IsFrameOn s V := by
  intro W hWU hWV
  choose V' hxV' hV'V hfr using h

  let ι : Type u := W
  let O : ι → X.Opens := fun x => W ⊓ V' x.1 (hWV x.2)
  have hOW : ∀ x, O x ≤ W := fun x => inf_le_left
  have hcover : W ≤ iSup O := fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, ⟨hx, hxV' x (hWV hx)⟩⟩

  have hbij : ∀ x, Function.Bijective fun a : Γ(X, O x) =>
      a • M.presheaf.map (homOfLE ((hOW x).trans hWU)).op s :=
    fun x => hfr x.1 (hWV x.2) ((hOW x).trans hWU) inf_le_right
  set sW := M.presheaf.map (homOfLE hWU).op s with hsW
  have hres : ∀ x, M.presheaf.map (homOfLE (hOW x)).op sW =
      M.presheaf.map (homOfLE ((hOW x).trans hWU)).op s := fun x => by rw [hsW, map_map]
  let F : TopCat.Sheaf Ab X := ⟨M.presheaf, Scheme.Modules.isSheaf M⟩
  refine ⟨fun a b hab => ?_, fun y => ?_⟩
  ·
    apply X.sheaf.eq_of_locally_eq' O W (fun x => homOfLE (hOW x)) hcover
    intro x
    apply (hbij x).1
    change X.presheaf.map (homOfLE (hOW x)).op a • _ = X.presheaf.map (homOfLE (hOW x)).op b • _
    rw [← hres, ← map_smul', ← map_smul']
    exact congrArg _ hab
  ·
    have hloc : ∀ x, ∃! a : Γ(X, O x),
        a • M.presheaf.map (homOfLE ((hOW x).trans hWU)).op s = M.presheaf.map (homOfLE (hOW x)).op y :=
      fun x => (Function.bijective_iff_existsUnique _).1 (hbij x) _
    choose a ha hauniq using hloc

    have hcompat : TopCat.Presheaf.IsCompatible X.presheaf O a := by
      intro x x'
      have hb : Function.Bijective fun c : Γ(X, O x ⊓ O x') =>
          c • M.presheaf.map (homOfLE ((inf_le_left.trans (hOW x)).trans hWU)).op s :=
        hfr x.1 (hWV x.2) _ (inf_le_left.trans inf_le_right)
      apply hb.1
      change X.presheaf.map (homOfLE inf_le_left).op (a x) • _ =
        X.presheaf.map (homOfLE inf_le_right).op (a x') • _
      have e1 : M.presheaf.map (homOfLE ((inf_le_left.trans (hOW x)).trans hWU)).op s =
          M.presheaf.map (homOfLE (inf_le_left : O x ⊓ O x' ≤ O x)).op
            (M.presheaf.map (homOfLE ((hOW x).trans hWU)).op s) := by rw [map_map]
      have e2 : M.presheaf.map (homOfLE ((inf_le_left.trans (hOW x)).trans hWU)).op s =
          M.presheaf.map (homOfLE (inf_le_right : O x ⊓ O x' ≤ O x')).op
            (M.presheaf.map (homOfLE ((hOW x').trans hWU)).op s) := by rw [map_map]
      conv_lhs => rw [e1, ← map_smul', ha x, map_map]
      conv_rhs => rw [e2, ← map_smul', ha x', map_map]
    obtain ⟨g, hg, -⟩ : ∃! g : Γ(X, W), ∀ x, X.presheaf.map (homOfLE (hOW x)).op g = a x :=
      X.sheaf.existsUnique_gluing' O W (fun x => homOfLE (hOW x)) hcover a hcompat
    refine ⟨g, ?_⟩
    change g • sW = y
    apply F.eq_of_locally_eq' O W (fun x => homOfLE (hOW x)) hcover
    intro x
    change M.presheaf.map (homOfLE (hOW x)).op (g • sW) = M.presheaf.map (homOfLE (hOW x)).op y
    rw [map_smul', hres, ← ha x]
    exact congrArg (· • _) (hg x)

end P2mGenFrame

open P2mGenFrame in
theorem solution
    {X : Scheme.{u}} {L : X.Modules} (hL : Scheme.Modules.IsInvertible L)
    {U : X.Opens} (hU : IsAffineOpen U) (m : Γ(L, U))
    (hm : Submodule.span Γ(X, U) {m} = ⊤) :
    Scheme.Modules.IsFrameOn m U := by

  let π : X ⟶ Spec (.of Γ(X, ⊤)) := X.toSpecΓ
  have hq : (OModulePresheaf.ofModules π L).IsQuasicoherent :=
    OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial π L hL.1
  refine isFrameOn_of_locally fun x hxU => ?_

  obtain ⟨U', s, hxU', hs⟩ := hL.exists_isFrameOn x
  obtain ⟨f, hfU', hxf⟩ := hU.exists_basicOpen_le ⟨x, hxU'⟩ hxU
  have hfU : X.basicOpen f ≤ U := X.basicOpen_le f
  refine ⟨X.basicOpen f, hxf, hfU, ?_⟩

  set s' := L.presheaf.map (homOfLE hfU').op s with hs'
  have hs'fr : Scheme.Modules.IsFrameOn s' (X.basicOpen f) := (hs.map (homOfLE hfU')).mono hfU'
  obtain ⟨g, hg⟩ := (hs'fr (le_refl _) le_rfl).2 (L.presheaf.map (homOfLE hfU).op m)
  change g • L.presheaf.map (homOfLE (le_refl _)).op s' = L.presheaf.map (homOfLE hfU).op m at hg
  have hrefl : L.presheaf.map (homOfLE (le_refl (X.basicOpen f))).op s' = s' := by
    rw [hs', map_map]
  rw [hrefl] at hg

  letI := (OModulePresheaf.ofModules π L).moduleRestrict hfU
  haveI hloc := OModulePresheaf.isLocalizedModule_res_of_isQuasicoherent (OModulePresheaf.ofModules π L) hq
    ⟨U, hU⟩ f
  obtain ⟨⟨y, ⟨fn, n, rfl⟩⟩, hy⟩ := IsLocalizedModule.surj (Submonoid.powers f)
    ((OModulePresheaf.ofModules π L).resₗ hfU) (show (OModulePresheaf.ofModules π L).obj (X.basicOpen f) from s')
  obtain ⟨b, rfl⟩ : ∃ b : Γ(X, U), b • m = y := by
    have : (y : Γ(L, U)) ∈ Submodule.span Γ(X, U) {m} := by rw [hm]; trivial
    exact Submodule.mem_span_singleton.mp this

  have hy' : X.presheaf.map (homOfLE hfU).op (f ^ n) • s' =
      (X.presheaf.map (homOfLE hfU).op b * g) • s' := by
    have lhs : ((⟨(fun x => f ^ x) n, n, rfl⟩ : Submonoid.powers f) •
        (show (OModulePresheaf.ofModules π L).obj (X.basicOpen f) from s')) =
        X.presheaf.map (homOfLE hfU).op (f ^ n) • s' := rfl
    have rhs : (OModulePresheaf.ofModules π L).resₗ hfU (b • m) =
        (show (OModulePresheaf.ofModules π L).obj (X.basicOpen f) from L.presheaf.map (homOfLE hfU).op (b • m)) :=
      rfl
    rw [lhs, rhs] at hy
    change X.presheaf.map (homOfLE hfU).op (f ^ n) • s' = L.presheaf.map (homOfLE hfU).op (b • m) at hy
    rw [hy, map_smul', ← hg, ← mul_smul]

  have hcoef : X.presheaf.map (homOfLE hfU).op (f ^ n) = X.presheaf.map (homOfLE hfU).op b * g := by
    apply (hs'fr (le_refl _) le_rfl).1
    change X.presheaf.map (homOfLE hfU).op (f ^ n) • L.presheaf.map (homOfLE (le_refl _)).op s' =
      (X.presheaf.map (homOfLE hfU).op b * g) • L.presheaf.map (homOfLE (le_refl _)).op s'
    rw [hrefl]
    exact hy'
  have hfunit : IsUnit (X.presheaf.map (homOfLE hfU).op (f ^ n)) := by
    rw [map_pow]
    exact (RingedSpace.isUnit_res_basicOpen (X := X.toLocallyRingedSpace.toRingedSpace) f).pow n
  have hgunit : IsUnit g := by
    rw [hcoef] at hfunit
    exact isUnit_of_mul_isUnit_right hfunit

  have hmres : Scheme.Modules.IsFrameOn (L.presheaf.map (homOfLE hfU).op m) (X.basicOpen f) := by
    rw [← hg]
    exact isFrameOn_smul_of_isUnit hs'fr hgunit
  exact isFrameOn_of_isFrameOn_map hfU le_rfl hmres

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_isFrameOn_of_isAffineOpen_of_span_singleton_eq_top
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_isFrameOn_of_isAffineOpen_of_span_singleton_eq_top (solution)
