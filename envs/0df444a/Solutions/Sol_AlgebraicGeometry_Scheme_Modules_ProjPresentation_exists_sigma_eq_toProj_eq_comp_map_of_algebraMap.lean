-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_sigma_eq_toProj_eq_comp_map_of_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/33d95579-5e23-5871-926c-4cfb00dec93a

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Theorems.Thm_AlgebraicGeometry_ProjSpace_map_preimage_basicOpen_X
import Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map
import Theorems.Thm_AlgebraicGeometry_ProjSpace_restrictFun_app_app_awayToSection_eq_app_awayToSection_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_sigma_eq_toProj_eq_comp_map_of_algebraMap

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [local instance] MvPolynomial.gradedAlgebra

namespace CompBaseSol

theorem smul_map_eq_of_eq {X : Scheme.{u}} (M : X.Modules) {W W' : X.Opens} (ρ : W ⟶ W') (e : W' = W)
    (s t : Γ(M, ⊤)) (g' : Γ(X, W'))
    (h : (X.presheaf.map ρ.op g') • M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s =
      M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op t) :
    g' • M.presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op s = M.presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op t := by
  subst e
  have hρ : ρ = 𝟙 _ := Subsingleton.elim _ _
  rw [hρ, op_id, CategoryTheory.Functor.map_id] at h
  exact h

end CompBaseSol

theorem solution
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {X : Scheme.{u}} {f : X ⟶ Spec (.of A)}
    {M : X.Modules} {N : ℕ} (𝔓 : M.ProjPresentation f N) :
    ∃ 𝔓' : M.ProjPresentation (f ≫ Spec.map (CommRingCat.ofHom (algebraMap R A))) N,
      (∀ i, 𝔓'.σ i = 𝔓.σ i) ∧ 𝔓'.toProj = 𝔓.toProj ≫ ProjSpace.map R A N := by

  have hpre : ∀ i : Fin (N + 1),
      (𝔓.toProj ≫ ProjSpace.map R A N) ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i) =
        𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A) (MvPolynomial.X i) := by
    intro i
    rw [← ProjSpace.map_preimage_basicOpen_X R A N i]
    rfl
  refine ⟨{ σ := 𝔓.σ
            toProj := 𝔓.toProj ≫ ProjSpace.map R A N
            toProj_π := ?_
            frame := ?_
            app_ratio_smul := ?_ }, fun i => rfl, rfl⟩
  · rw [Category.assoc, (ProjSpace.isPullback_map R A N).w, ← Category.assoc, 𝔓.toProj_π]
  · intro i V hV
    rw [hpre i] at hV
    exact 𝔓.frame i V hV
  · intro i j

    have hle : Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A) (MvPolynomial.X i) ≤
        ProjSpace.map R A N ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i) :=
      (ProjSpace.map_preimage_basicOpen_X R A N i).symm.le
    have key := AlgebraicGeometry.ProjSpace.restrictFun_app_app_awayToSection_eq_app_awayToSection_map
      (𝟙 _) A (𝟙 _) (ProjSpace.map R A N) (by simp) 1 (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X R j) i
      (by simpa using hle)
    refine CompBaseSol.smul_map_eq_of_eq M ((Opens.map 𝔓.toProj.base).map (homOfLE hle)) (hpre i) (𝔓.σ i) (𝔓.σ j) _ ?_

    convert 𝔓.app_ratio_smul i j using 2
    rw [Scheme.Hom.comp_app]
    have nat0 := Scheme.Hom.naturality 𝔓.toProj (homOfLE hle).op
    have e1 : (Scheme.Hom.app (ProjSpace.map R A N) (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)) ≫
        Scheme.Hom.app 𝔓.toProj (ProjSpace.map R A N ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i))) ≫
          X.presheaf.map ((Opens.map 𝔓.toProj.base).map (homOfLE hle).op.unop).op =
        Scheme.Hom.app (ProjSpace.map R A N) (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)) ≫
          ((Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)).presheaf.map (homOfLE hle).op ≫
            Scheme.Hom.app 𝔓.toProj (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A) (MvPolynomial.X i))) := by
      rw [Category.assoc, ← nat0]
    have key' : ((Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)).presheaf.map (homOfLE hle).op)
        ((ProjSpace.map R A N).app _ (Proj.awayToSection _ (MvPolynomial.X i) (ProjSpace.ratio R N i j))) =
        Proj.awayToSection _ (MvPolynomial.X i) (ProjSpace.ratio A N i j) := by
      have k := key
      erw [Scheme.Hom.id_app, Scheme.Hom.id_app] at k
      convert k using 3
      all_goals first
        | rfl
        | (erw [CategoryTheory.id_apply]
           congr 1
           apply HomogeneousLocalization.val_injective
           simp [ProjSpace.ratio, HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_mk, MvPolynomial.map_X])
    rw [← key']
    exact CategoryTheory.ConcreteCategory.congr_hom e1 (Proj.awayToSection _ (MvPolynomial.X i) (ProjSpace.ratio R N i j))

end S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_sigma_eq_toProj_eq_comp_map_of_algebraMap
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_sigma_eq_toProj_eq_comp_map_of_algebraMap (solution)
