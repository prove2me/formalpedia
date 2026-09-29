-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.FiniteBySections.pullback_of_isFinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/bb26c295-7bfc-5835-b59d-47820baccb6b

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_smul_unit_app_of_bijective_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_pullback_of_isFinite

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_pullback_of_isFinite.AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

open Opposite TopologicalSpace

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Scheme.Hom IsFinite Spec Scheme Proj Scheme.Hom.comp_app Proj.basicOpen Scheme.Modules Scheme.Hom.comp_preimage Proj.awayToSection ProjSpace.ratio Scheme.Modules.FiniteBySections"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul Modules.pullback Hom Γ Modules.Hom Hom.comp_app basicOpen Modules Opens Hom.comp_preimage Modules.FiniteBySections"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "Hom.app_smul pullback presheaf Hom.comp_app Hom mapPresheaf_app pullbackPushforwardAdjunction ProjPresentation FiniteBySections bijective_smul_unit_app_of_bijective_smul"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace PresPre

variable {R : Type u} [CommRing R] {X X' : Scheme.{u}} {f : X ⟶ Spec (.of R)} (p : X' ⟶ X)
    {M : X.Modules} {N : ℕ} (𝔓 : M.ProjPresentation f N)

local notation "𝒜R" => MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R

lemma preimage_chart (i : Fin (N + 1)) :
    (p ≫ 𝔓.toProj) ⁻¹ᵁ Proj.basicOpen 𝒜R (MvPolynomial.X i) =
      p ⁻¹ᵁ (𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜R (MvPolynomial.X i)) :=
  Scheme.Hom.comp_preimage _ _ _

noncomputable abbrev σ' (i : Fin (N + 1)) : Γ((Modules.pullback p).obj M, ⊤) :=
  ((pullbackPushforwardAdjunction p).unit.app M).app ⊤ (𝔓.σ i)

omit 𝔓 in

lemma presheaf_map_congr {Z : Scheme.{u}} (G : TopCat.Presheaf Ab Z) {U V : Z.Opens}
    (k₁ k₂ : op U ⟶ op V) (z : G.obj (op U)) : G.map k₁ z = G.map k₂ z := by
  rw [show k₁ = k₂ from Quiver.Hom.unop_inj (Subsingleton.elim _ _)]

noncomputable def eta (U : X.Opens) (m : Γ(M, U)) : Γ((Modules.pullback p).obj M, p ⁻¹ᵁ U) :=
  ((pullbackPushforwardAdjunction p).unit.app M).app U m

omit 𝔓 f in
lemma eta_smul (U : X.Opens) (r : Γ(X, U)) (m : Γ(M, U)) :
    eta p (M := M) U (r • m) = p.app U r • eta p (M := M) U m :=
  Modules.Hom.app_smul _ r m

omit 𝔓 f in
lemma eta_resTop (U : X.Opens) (m : Γ(M, ⊤)) :
    eta p (M := M) U (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op m) =
      ((Modules.pullback p).obj M).presheaf.map (homOfLE (le_top : p ⁻¹ᵁ U ≤ ⊤)).op (eta p (M := M) ⊤ m) := by
  have hnat := ((pullbackPushforwardAdjunction p).unit.app M).mapPresheaf.naturality
    (homOfLE (le_top : U ≤ ⊤)).op
  have hx := ConcreteCategory.congr_hom hnat m
  simp only [ConcreteCategory.comp_apply, mapPresheaf_app] at hx
  refine hx.trans ?_
  exact presheaf_map_congr ((Modules.pullback p).obj M).presheaf _ _ _

lemma ratio_pulled (i j : Fin (N + 1)) :
    (p.app (𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜R (MvPolynomial.X i))
        (𝔓.toProj.app (Proj.basicOpen 𝒜R (MvPolynomial.X i))
          (Proj.awayToSection _ (MvPolynomial.X i) (ProjSpace.ratio R N i j)))) •
      ((Modules.pullback p).obj M).presheaf.map
        (homOfLE (le_top : p ⁻¹ᵁ (𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜R (MvPolynomial.X i)) ≤ ⊤)).op (σ' p 𝔓 i) =
      ((Modules.pullback p).obj M).presheaf.map
        (homOfLE (le_top : p ⁻¹ᵁ (𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜R (MvPolynomial.X i)) ≤ ⊤)).op (σ' p 𝔓 j) := by
  have h := congrArg (eta p (M := M) (𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜R (MvPolynomial.X i)))
    (𝔓.app_ratio_smul i j)
  have h2 := (eta_smul p _ _ _).symm.trans h
  rw [eta_resTop, eta_resTop] at h2
  exact h2

lemma comp_app_ratio (i j : Fin (N + 1)) :
    (p ≫ 𝔓.toProj).app (Proj.basicOpen 𝒜R (MvPolynomial.X i))
        (Proj.awayToSection 𝒜R (MvPolynomial.X i) (ProjSpace.ratio R N i j)) =
      p.app (𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜R (MvPolynomial.X i))
        (𝔓.toProj.app (Proj.basicOpen 𝒜R (MvPolynomial.X i))
          (Proj.awayToSection 𝒜R (MvPolynomial.X i) (ProjSpace.ratio R N i j))) := by
  have h := ConcreteCategory.congr_hom (Scheme.Hom.comp_app p 𝔓.toProj (Proj.basicOpen 𝒜R (MvPolynomial.X i)))
    (Proj.awayToSection 𝒜R (MvPolynomial.X i) (ProjSpace.ratio R N i j))
  exact h

noncomputable def precomp : ((Modules.pullback p).obj M).ProjPresentation (p ≫ f) N where
  σ := σ' p 𝔓
  toProj := p ≫ 𝔓.toProj
  toProj_π := by rw [Category.assoc, 𝔓.toProj_π]
  frame := fun i V hV =>
    bijective_smul_unit_app_of_bijective_smul p M (𝔓.σ i)
      (V := 𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜R (MvPolynomial.X i)) (𝔓.frame i) V
      (hV.trans (preimage_chart p 𝔓 i).le)
  app_ratio_smul := fun i j => by
    have key := ratio_pulled p 𝔓 i j
    have hc := comp_app_ratio p 𝔓 i j
    rw [hc]
    exact key

lemma precomp_σ (i : Fin (N + 1)) :
    (precomp p 𝔓).σ i = ((pullbackPushforwardAdjunction p).unit.app M).app ⊤ (𝔓.σ i) := rfl

lemma precomp_toProj : (precomp p 𝔓).toProj = p ≫ 𝔓.toProj := rfl

end PresPre

end AlgebraicGeometry.Scheme.Modules

theorem solution
    {R : Type u} [CommRing R] {X X' : Scheme.{u}} {f : X ⟶ Spec (.of R)} (p : X' ⟶ X) [IsFinite p]
    {M : X.Modules} (hM : Scheme.Modules.FiniteBySections M f) :
    Scheme.Modules.FiniteBySections ((Scheme.Modules.pullback p).obj M) (p ≫ f) :=
  by
  obtain ⟨N, 𝔓, h𝔓⟩ := hM
  haveI := h𝔓
  exact ⟨N, AlgebraicGeometry.Scheme.Modules.PresPre.precomp p 𝔓, inferInstanceAs (IsFinite (p ≫ 𝔓.toProj))⟩

end S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_pullback_of_isFinite
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_pullback_of_isFinite (solution)
