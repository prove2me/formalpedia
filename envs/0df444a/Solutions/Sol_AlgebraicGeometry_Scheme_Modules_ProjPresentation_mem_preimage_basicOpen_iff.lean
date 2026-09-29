-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.mem_preimage_basicOpen_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/1f195348-2498-5ebd-8bec-16f7362fbb58

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_mem_preimage_basicOpen_iff

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_mem_preimage_basicOpen_iff.AlgebraicGeometry"

universe u

open Opposite TopologicalSpace

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom Scheme.Hom.germ_stalkMap_apply Spec Scheme Proj.mem_basicOpen Proj Proj.stalkIso' Proj.basicOpen Scheme.Modules Proj.iSup_basicOpen_eq_top Proj.awayToSection ProjectiveSpectrum.Proj.awayToSection_germ ProjSpace.irrelevant_le_span_X ProjSpace.ratio"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "mem_basicOpen Hom mk Γ Hom.germ_stalkMap_apply basicOpen Modules Opens Modules.map_smul"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "presheaf Hom map_smul ProjPresentation"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace PresChart

section chart

variable (R : Type u) [CommRing R] (N : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R

lemma isUnit_germ_ratio_iff (i j : Fin (N + 1)) (y : Proj 𝒜)
    (hy : y ∈ Proj.basicOpen 𝒜 (MvPolynomial.X j)) :
    IsUnit ((Proj 𝒜).presheaf.germ (Proj.basicOpen 𝒜 (MvPolynomial.X j)) y hy
      (Proj.awayToSection 𝒜 (MvPolynomial.X j) (ProjSpace.ratio R N j i))) ↔
      y ∈ Proj.basicOpen 𝒜 (MvPolynomial.X i) := by
  have hle : Submonoid.powers (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) R) ≤
      y.asHomogeneousIdeal.toIdeal.primeCompl :=
    Submonoid.powers_le.mpr ((Proj.mem_basicOpen 𝒜 _ y).mp hy)
  have h := ConcreteCategory.congr_hom
    (ProjectiveSpectrum.Proj.awayToSection_germ 𝒜 (MvPolynomial.X j) y hy) (ProjSpace.ratio R N j i)
  have h' : (Proj 𝒜).presheaf.germ (Proj.basicOpen 𝒜 (MvPolynomial.X j)) y hy
      (Proj.awayToSection 𝒜 (MvPolynomial.X j) (ProjSpace.ratio R N j i)) =
      (Proj.stalkIso' 𝒜 y).symm (HomogeneousLocalization.mapId 𝒜 hle (ProjSpace.ratio R N j i)) := h
  have e1 : IsUnit ((Proj.stalkIso' 𝒜 y).symm (HomogeneousLocalization.mapId 𝒜 hle (ProjSpace.ratio R N j i))) ↔
      IsUnit (HomogeneousLocalization.mapId 𝒜 hle (ProjSpace.ratio R N j i)) :=
    ⟨fun hu => by simpa using hu.map (Proj.stalkIso' 𝒜 y), fun hu => hu.map _⟩
  rw [h']
  refine e1.trans ?_
  rw [← HomogeneousLocalization.isUnit_iff_isUnit_val, ProjSpace.ratio,
    HomogeneousLocalization.Away.mk, HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk,
    Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff, Proj.mem_basicOpen]
  exact Iff.rfl

lemma exists_mem_basicOpen_X (y : Proj 𝒜) : ∃ j : Fin (N + 1), y ∈ Proj.basicOpen 𝒜 (MvPolynomial.X j) := by
  have htop := Proj.iSup_basicOpen_eq_top 𝒜 (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) R)
    (ProjSpace.irrelevant_le_span_X R N)
  have hy : y ∈ (⊤ : (Proj 𝒜).Opens) := trivial
  rw [← htop] at hy
  exact Opens.mem_iSup.mp hy

end chart

section pres

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} {M : X.Modules} {N : ℕ}
    (𝔓 : M.ProjPresentation f N)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R

noncomputable abbrev resTop (V : X.Opens) (s : Γ(M, ⊤)) : Γ(M, V) :=
  M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op s

omit 𝔓 in
lemma res_resTop {V W : X.Opens} (h : W ≤ V) (s : Γ(M, ⊤)) :
    M.presheaf.map (homOfLE h).op (resTop V s) = resTop W s := by
  change (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ≫ M.presheaf.map (homOfLE h).op) s = _
  rw [← CategoryTheory.Functor.map_comp]
  rfl

theorem main (i : Fin (N + 1)) (x : X) :
    x ∈ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X i) ↔
      ∃ U : X.Opens, x ∈ U ∧ ∀ V : X.Opens, V ≤ U →
        Function.Bijective fun g : Γ(X, V) => g • resTop V (𝔓.σ i) := by
  constructor
  · intro hx
    exact ⟨_, hx, fun V hV => 𝔓.frame i V hV⟩
  · rintro ⟨U, hxU, hU⟩
    obtain ⟨j, hj⟩ := exists_mem_basicOpen_X R N (𝔓.toProj x)

    have hxW : x ∈ U ⊓ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j) := ⟨hxU, hj⟩
    have hWU : U ⊓ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j) ≤ U := inf_le_left
    have hWj : U ⊓ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j) ≤
        𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j) := inf_le_right

    have hρ : X.presheaf.map (homOfLE hWj).op
        (𝔓.toProj.app (Proj.basicOpen 𝒜 (MvPolynomial.X j))
          (Proj.awayToSection 𝒜 (MvPolynomial.X j) (ProjSpace.ratio R N j i))) •
        resTop (U ⊓ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j)) (𝔓.σ j) =
        resTop (U ⊓ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j)) (𝔓.σ i) := by
      have h := congrArg (M.presheaf.map (homOfLE hWj).op) (𝔓.app_ratio_smul j i)
      rw [Modules.map_smul, res_resTop, res_resTop] at h
      exact h

    obtain ⟨g, hg⟩ := (hU _ hWU).2 (resTop (U ⊓ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j)) (𝔓.σ j))
    dsimp only at hg

    have h1 : (g * X.presheaf.map (homOfLE hWj).op
        (𝔓.toProj.app (Proj.basicOpen 𝒜 (MvPolynomial.X j))
          (Proj.awayToSection 𝒜 (MvPolynomial.X j) (ProjSpace.ratio R N j i)))) •
        resTop (U ⊓ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j)) (𝔓.σ j) =
        (1 : Γ(X, U ⊓ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j))) •
          resTop (U ⊓ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j)) (𝔓.σ j) := by
      rw [mul_smul, hρ, hg, one_smul]
    have hunit : IsUnit (X.presheaf.map (homOfLE hWj).op
        (𝔓.toProj.app (Proj.basicOpen 𝒜 (MvPolynomial.X j))
          (Proj.awayToSection 𝒜 (MvPolynomial.X j) (ProjSpace.ratio R N j i)))) := by
      refine isUnit_iff_exists_inv.mpr ⟨g, ?_⟩
      rw [mul_comm]
      exact (𝔓.frame j _ hWj).1 h1

    have hgerm : IsUnit (X.presheaf.germ _ x hxW (X.presheaf.map (homOfLE hWj).op
        (𝔓.toProj.app (Proj.basicOpen 𝒜 (MvPolynomial.X j))
          (Proj.awayToSection 𝒜 (MvPolynomial.X j) (ProjSpace.ratio R N j i))))) := hunit.map _
    rw [TopCat.Presheaf.germ_res_apply] at hgerm
    have hgerm' : IsUnit (X.presheaf.germ (𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j)) x hj
        (𝔓.toProj.app (Proj.basicOpen 𝒜 (MvPolynomial.X j))
          (Proj.awayToSection 𝒜 (MvPolynomial.X j) (ProjSpace.ratio R N j i)))) := hgerm
    rw [← Scheme.Hom.germ_stalkMap_apply] at hgerm'
    haveI : IsLocalHom (ConcreteCategory.hom (𝔓.toProj.stalkMap x)) :=
      inferInstanceAs (IsLocalHom (𝔓.toProj.stalkMap x).hom)
    rw [isUnit_map_iff] at hgerm'
    exact (isUnit_germ_ratio_iff R N i j _ hj).mp hgerm'

end pres

end PresChart

end AlgebraicGeometry.Scheme.Modules

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} {M : X.Modules} {N : ℕ}
    (𝔓 : M.ProjPresentation f N) (i : Fin (N + 1)) (x : X) :
    x ∈ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i) ↔
      ∃ U : X.Opens, x ∈ U ∧ ∀ V : X.Opens, V ≤ U →
        Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (𝔓.σ i) : Γ(M, V)) :=
  AlgebraicGeometry.Scheme.Modules.PresChart.main 𝔓 i x

end S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_mem_preimage_basicOpen_iff
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_mem_preimage_basicOpen_iff (solution)
