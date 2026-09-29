-- Prove2me | solution 1 for AlgebraicGeometry.FramedPolarisedAbelianScheme.iso_of_iso_of_isReframe
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/1c0c7fbb-b711-57db-94c0-29469f13de5c

import Definitions.Def_AlgebraicGeometry_ThetaReframe
import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_projPresentation_pullback_sigma_eq_toProj_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_iso_forall_app_eq_of_toProj_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_toProj_eq_of_forall_sections_eq_univ
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_iso_of_iso_of_isReframe
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left"

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

open Opposite

universe u

namespace PPofIso

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} {M M' : X.Modules} {N : ℕ}

theorem app_map (φ : M ⟶ M') {V V' : X.Opens} (hle : V' ≤ V) (x : Γ(M, V)) :
    M'.presheaf.map (homOfLE hle).op (φ.app V x) = φ.app V' (M.presheaf.map (homOfLE hle).op x) := by
  have := φ.mapPresheaf.naturality (homOfLE hle).op
  have e := congrArg (fun f => f x) this
  simpa using e.symm

theorem app_bijective (φ : M ≅ M') (V : X.Opens) : Function.Bijective (φ.hom.app V) := by
  have h1 : ∀ x, φ.inv.app V (φ.hom.app V x) = x := fun x => by
    have e := congrArg (fun g : M ⟶ M => g.app V x) φ.hom_inv_id
    simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app] at e
    exact e
  have h2 : ∀ y, φ.hom.app V (φ.inv.app V y) = y := fun y => by
    have e := congrArg (fun g : M' ⟶ M' => g.app V y) φ.inv_hom_id
    simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app] at e
    exact e
  exact ⟨fun a b hab => by rw [← h1 a, ← h1 b, hab], fun y => ⟨_, h2 y⟩⟩

noncomputable def ofIso (𝔓 : Scheme.Modules.ProjPresentation M f N) (φ : M ≅ M') :
    Scheme.Modules.ProjPresentation M' f N where
  σ i := φ.hom.app ⊤ (𝔓.σ i)
  toProj := 𝔓.toProj
  toProj_π := 𝔓.toProj_π
  frame i V hV := by
    have key : (fun g : Γ(X, V) => g • (M'.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (φ.hom.app ⊤ (𝔓.σ i)) : Γ(M', V))) =
        (φ.hom.app V) ∘ (fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (𝔓.σ i) : Γ(M, V))) := by
      funext g
      simp only [Function.comp_apply, app_map, Scheme.Modules.Hom.app_smul]
    rw [key]
    exact (app_bijective φ V).comp (𝔓.frame i V hV)
  app_ratio_smul i j := by
    rw [app_map, app_map, ← Scheme.Modules.Hom.app_smul, 𝔓.app_ratio_smul i j]

theorem exists_of_iso (𝔓 : Scheme.Modules.ProjPresentation M f N) (φ : M ≅ M') :
    ∃ 𝔔 : Scheme.Modules.ProjPresentation M' f N, (∀ i, 𝔔.σ i = φ.hom.app ⊤ (𝔓.σ i)) ∧ 𝔔.toProj = 𝔓.toProj :=
  ⟨ofIso 𝔓 φ, fun _ => rfl, rfl⟩

end PPofIso

namespace CL4Sol

theorem key {S : Type u} [CommRing S] {A : Scheme.{u}} {f g : A ⟶ Spec (CommRingCat.of S)} (hfg : g = f)
    {L L' : A.Modules} {N : ℕ}
    (PX P' : Scheme.Modules.ProjPresentation L f N) (coef : Fin (N + 1) → Fin (N + 1) → Γ(A, ⊤))
    (hP' : ∀ i, P'.σ i = ∑ j, coef i j • PX.σ j)
    (Y1 Q1 : Scheme.Modules.ProjPresentation L' g N) (hQ1 : ∀ i, Q1.σ i = ∑ j, coef i j • Y1.σ j)
    (hι : Y1.toProj = PX.toProj) : Q1.toProj = P'.toProj := by
  subst hfg
  obtain ⟨ψ, hψ⟩ := AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_iso_forall_app_eq_of_toProj_eq Y1 PX hι
  obtain ⟨Q2, hQ2σ, hQ2π⟩ := PPofIso.exists_of_iso Q1 ψ
  have hσ : ∀ i, Q2.σ i = P'.σ i := fun i => by
    rw [hQ2σ, hQ1 i, hP' i, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Scheme.Modules.Hom.app_smul, hψ]
  rw [← hQ2π]
  exact AlgebraicGeometry.Scheme.Modules.ProjPresentation.toProj_eq_of_forall_sections_eq_univ Q2 P' hσ

theorem main
    {g N n : ℕ} {S : Type} [CommRing S] (U : Matrix (Fin (N + 1)) (Fin (N + 1)) S)
    (X Y X' Y' : FramedPolarisedAbelianScheme g N n S)
    (h : FramedPolarisedAbelianScheme.Iso X Y) (hX : X.IsReframe U X') (hY : Y.IsReframe U Y') :
    FramedPolarisedAbelianScheme.Iso X' Y' := by
  classical
  obtain ⟨e, he, hι, hmul, hP, hpol⟩ := h
  obtain ⟨P', h1, h2, rfl, hP'⟩ := hX
  obtain ⟨Q', k1, k2, rfl, hQ'⟩ := hY
  obtain ⟨Y1, hY1σ, hY1π⟩ :=
    AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_projPresentation_pullback_sigma_eq_toProj_eq e.hom Y.frame
  obtain ⟨Q1, hQ1σ, hQ1π⟩ :=
    AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_projPresentation_pullback_sigma_eq_toProj_eq e.hom Q'

  have hc : ∀ r : S, (e.hom.app ⊤).hom ((Y.f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom r)) =
      (X.f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom r) := by
    intro r
    have e1 : Y.f.app ⊤ ≫ e.hom.app ⊤ = X.f.app ⊤ := by
      rw [← he, Scheme.Hom.comp_app]; rfl
    rw [show Y.f.appLE ⊤ ⊤ le_top = Y.f.app ⊤ from (Scheme.Hom.app_eq_appLE Y.f).symm,
      show X.f.appLE ⊤ ⊤ le_top = X.f.app ⊤ from (Scheme.Hom.app_eq_appLE X.f).symm, ← e1]
    rfl

  have hcoef : ∀ i, Q1.σ i = ∑ j, ((X.f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (U i j))) • Y1.σ j := by
    intro i
    have hsum : ∀ (F : Fin (N + 1) → Γ(Y.pol, ⊤)),
        (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction e.hom).unit.app Y.pol) ⊤) (∑ j, F j) =
          ∑ j, (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction e.hom).unit.app Y.pol) ⊤) (F j) :=
      fun F => map_sum (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction e.hom).unit.app Y.pol) ⊤).hom F _
    rw [hQ1σ i, hQ' i]
    refine (hsum _).trans ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    refine (Scheme.Modules.Hom.app_smul _ _ _).trans ?_
    rw [hY1σ j, ← hc]
    rfl
  have hkey := key he X.frame P' (fun i j => (X.f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (U i j)))
    hP' Y1 Q1 hcoef (by rw [hY1π, hι])
  refine ⟨e, he, ?_, hmul, hP, hpol⟩
  show e.hom ≫ Q'.toProj = P'.toProj
  rw [← hQ1π]
  exact hkey

end CL4Sol

theorem solution
    {g N n : ℕ} {S : Type} [CommRing S] (U : Matrix (Fin (N + 1)) (Fin (N + 1)) S)
    (X Y X' Y' : FramedPolarisedAbelianScheme g N n S)
    (h : FramedPolarisedAbelianScheme.Iso X Y) (hX : X.IsReframe U X') (hY : Y.IsReframe U Y') :
    FramedPolarisedAbelianScheme.Iso X' Y' :=
  CL4Sol.main U X Y X' Y' h hX hY

end S_AlgebraicGeometry_FramedPolarisedAbelianScheme_iso_of_iso_of_isReframe
end P2MW
export P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_iso_of_iso_of_isReframe (solution)
