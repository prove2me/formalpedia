-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/7a1b1f7e-f132-590b-9f01-c64dc7b29925

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

open Opposite

namespace PresIso

variable {X : Scheme.{u}} {M M' : X.Modules}

theorem map_app (φ : M ⟶ M') {U V : X.Opens} (i : V ⟶ U) (s : Γ(M, U)) :
    M'.presheaf.map i.op (φ.app U s) = φ.app V (M.presheaf.map i.op s) := by
  have h := φ.mapPresheaf.naturality i.op
  have := congrArg (fun f => (ConcreteCategory.hom f) s) h
  simpa using this.symm

theorem app_bijective (e : M ≅ M') (U : X.Opens) : Function.Bijective (e.hom.app U) :=
  ConcreteCategory.bijective_of_isIso (e.hom.app U)

noncomputable def transport {R : Type u} [CommRing R] {f : X ⟶ Spec (.of R)} {N : ℕ}
    (𝔓 : M.ProjPresentation f N) (e : M ≅ M') : M'.ProjPresentation f N where
  σ := fun i => e.hom.app ⊤ (𝔓.σ i)
  toProj := 𝔓.toProj
  toProj_π := 𝔓.toProj_π
  frame := fun i V hV => by
    have key : (fun g : Γ(X, V) => g • M'.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (e.hom.app ⊤ (𝔓.σ i)))
        = (e.hom.app V) ∘ (fun g : Γ(X, V) => g • M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (𝔓.σ i)) := by
      funext g
      simp only [Function.comp_apply, map_app, Scheme.Modules.Hom.app_smul]
    rw [key]
    exact (app_bijective e V).comp (𝔓.frame i V hV)
  app_ratio_smul := fun i j => by
    rw [map_app, map_app, ← Scheme.Modules.Hom.app_smul, 𝔓.app_ratio_smul i j]

end PresIso

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} {M M' : X.Modules} {N : ℕ}
    (𝔓 : M.ProjPresentation f N) (e : M ≅ M') :
    ∃ 𝔓' : M'.ProjPresentation f N, 𝔓'.toProj = 𝔓.toProj ∧ ∀ i, 𝔓'.σ i = (e.hom.app ⊤) (𝔓.σ i) :=
  ⟨PresIso.transport 𝔓 e, rfl, fun _ => rfl⟩

end S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso (solution)
