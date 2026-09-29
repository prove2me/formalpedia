-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.FiniteBySections.of_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/6fbb4c9a-8ae3-5788-9887-cd875d0cf570

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_of_iso

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Opposite

attribute [local instance] MvPolynomial.gradedAlgebra

namespace FBSIsoSketch

variable {X : Scheme.{u}} {M M' : X.Modules}

theorem map_app (φ : M ⟶ M') {U V : X.Opens} (i : V ⟶ U) (s : Γ(M, U)) :
    M'.presheaf.map i.op (φ.app U s) = φ.app V (M.presheaf.map i.op s) := by
  have h := φ.mapPresheaf.naturality i.op
  have := congrArg (fun f => (ConcreteCategory.hom f) s) h
  simpa using this.symm

theorem app_bijective (e : M ≅ M') (U : X.Opens) : Function.Bijective (e.hom.app U) :=
  ConcreteCategory.bijective_of_isIso (e.hom.app U)

end FBSIsoSketch

open FBSIsoSketch in
theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} {M M' : X.Modules} (e : M ≅ M')
    (hM : M.FiniteBySections f) : M'.FiniteBySections f := by
  obtain ⟨N, 𝔓, hfin⟩ := hM
  refine ⟨N,
    { σ := fun i => e.hom.app ⊤ (𝔓.σ i)
      toProj := 𝔓.toProj
      toProj_π := 𝔓.toProj_π
      frame := fun i V hV => ?_
      app_ratio_smul := fun i j => ?_ }, hfin⟩
  · have key : (fun g : Γ(X, V) => g • M'.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (e.hom.app ⊤ (𝔓.σ i)))
        = (e.hom.app V) ∘ (fun g : Γ(X, V) => g • M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (𝔓.σ i)) := by
      funext g
      simp only [Function.comp_apply, map_app, Scheme.Modules.Hom.app_smul]
    rw [key]
    exact (app_bijective e V).comp (𝔓.frame i V hV)
  · rw [map_app, map_app, ← Scheme.Modules.Hom.app_smul, 𝔓.app_ratio_smul i j]

end S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_of_iso
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_of_iso (solution)
