-- Prove2me | solution 1 for AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.comp_of_commSq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/76ec12cd-4f0d-5543-b862-4dda37a79168

import Mathlib
import Definitions.Def_AlgebraicGeometry_GradedOAlgebraToProj
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_smul_unit_app_of_bijective_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_comp_of_commSq

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_comp_of_commSq.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul Scheme.Modules.pushforward Scheme.Modules.pullback Scheme.Hom Scheme.Hom.appLE_comp_appLE Scheme.Modules.Hom Spec Spec.map Scheme Proj Scheme.Modules.pullbackPushforwardAdjunction Proj.basicOpen Scheme.Modules Scheme.Hom.app_eq_appLE Proj.awayToSection GradedOAlgebra.IsCanonicalToProj Scheme.Modules.tensorPowMapIso Scheme.Modules.pullbackTensorPowIso Scheme.Modules.IsFrameOn Scheme.Modules.IsFrameOn.map_iso Scheme.Modules.bijective_smul_unit_app_of_bijective_smul"
namespace GradedOAlgebra
p2m_export "AlgebraicGeometry.GradedOAlgebra" "IsCanonicalToProj"
namespace CompOfCommSq
p2m_open "AlgebraicGeometry.GradedOAlgebra AlgebraicGeometry"

variable {X X' : Scheme.{u}}

theorem app_naturality {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (i : U ⟶ V) (m : Γ(M, V)) :
    N.presheaf.map i.op (φ.app V m) = φ.app U (M.presheaf.map i.op m) := by
  have h := PresheafOfModules.Hom.naturality φ.val i.op
  have h' := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) m
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h'
  exact h'.symm

variable (p : X' ⟶ X) (M : X.Modules)

abbrev η : M ⟶ (Scheme.Modules.pushforward p).obj ((Scheme.Modules.pullback p).obj M) :=
  (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M

abbrev pull (V : X.Opens) (m : Γ(M, V)) : Γ((Scheme.Modules.pullback p).obj M, p ⁻¹ᵁ V) := (η p M).app V m

theorem pull_smul (V : X.Opens) (c : Γ(X, V)) (m : Γ(M, V)) :
    pull p M V (c • m) = p.app V c • pull p M V m := by
  rw [pull, Scheme.Modules.Hom.app_smul]
  rfl

theorem map_pull {U V : X.Opens} (h : U ≤ V) (m : Γ(M, V)) :
    ((Scheme.Modules.pullback p).obj M).presheaf.map (homOfLE ((Opens.map p.base).monotone h)).op (pull p M V m)
      = pull p M U (M.presheaf.map (homOfLE h).op m) := by
  rw [pull, pull, ← app_naturality (η p M) (homOfLE h) m]
  rfl

end AlgebraicGeometry.GradedOAlgebra.CompOfCommSq

end

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_comp_of_commSq.AlgebraicGeometry AlgebraicGeometry.Scheme.Modules HomogeneousLocalization"

open AlgebraicGeometry.GradedOAlgebra.CompOfCommSq in
theorem solution
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
    {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (f' : X' ⟶ Spec (CommRingCat.of S')) (c : X' ⟶ X)
    (hc : c ≫ f = f' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S')))
    (L : X.Modules) (L' : X'.Modules) (e : (Scheme.Modules.pullback c).obj L ≅ L')
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤))
    (θ : X ⟶ Proj 𝓡) (hθ : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj f L R 𝓡 ι θ) :
    AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj (f' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S'))) L' R 𝓡
      (fun (n : ℕ) (x : 𝓡 n) =>
        ((Scheme.Modules.pullbackTensorPowIso c L n ≪≫ Scheme.Modules.tensorPowMapIso e n).hom.app ⊤)
          ((((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (L.tensorPow n)).app ⊤) (ι n x)))
      (c ≫ θ) := by
  refine ⟨?_, ?_, ?_⟩
  ·
    rw [Category.assoc, hθ.comp_toSpecZero]
    exact hc
  ·
    intro n hn σ
    refine Scheme.Modules.IsFrameOn.map_iso (M := (Scheme.Modules.pullback c).obj (L.tensorPow n)) ?_ _
    intro W hWU hWV
    exact Scheme.Modules.bijective_smul_unit_app_of_bijective_smul c (L.tensorPow n) (ι n σ)
      (V := θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R)) (fun W' hW' => hθ.isFrameOn n hn σ le_top hW') W hWV
  ·
    intro n hn σ k s
    have key := hθ.appLE_awayToSection_smul n hn σ k s

    have hA := congrArg (pull c (L.tensorPow (k • n)) (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R))) key
    rw [pull_smul, ← map_pull c (L.tensorPow (k • n)) (le_top : θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) ≤ ⊤),
      ← map_pull c (L.tensorPow (k • n)) (le_top : θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) ≤ ⊤)] at hA

    have hB := congrArg ((Scheme.Modules.pullbackTensorPowIso c L (k • n) ≪≫
      Scheme.Modules.tensorPowMapIso e (k • n)).hom.app (c ⁻¹ᵁ θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R))) hA
    rw [Scheme.Modules.Hom.app_smul, ← app_naturality, ← app_naturality] at hB

    have hsc : ((c ≫ θ).appLE (Proj.basicOpen 𝓡 (σ : R)) ((c ≫ θ) ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R)) le_rfl
          (Proj.awayToSection 𝓡 (σ : R) (Away.mk 𝓡 σ.2 k (s : R) s.2)))
        = c.app (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R))
            (θ.appLE (Proj.basicOpen 𝓡 (σ : R)) (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R)) le_rfl
              (Proj.awayToSection 𝓡 (σ : R) (Away.mk 𝓡 σ.2 k (s : R) s.2))) := by
      have h := Scheme.Hom.appLE_comp_appLE c θ (Proj.basicOpen 𝓡 (σ : R)) (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R))
        ((c ≫ θ) ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R)) le_rfl le_rfl
      have h' := (ConcreteCategory.congr_hom h (Proj.awayToSection 𝓡 (σ : R) (Away.mk 𝓡 σ.2 k (s : R) s.2))).symm
      rw [Scheme.Hom.app_eq_appLE]
      exact h'
    rw [hsc]
    exact hB

end S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_comp_of_commSq
end P2MW
export P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_comp_of_commSq (solution)
