-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.Hom.mono_iff_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/d5b6cb58-9eab-52df-a7d0-4f2390d1fcca

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_Hom_mono_iff_injective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

theorem solution
    {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) :
    Mono φ ↔ ∀ U : X.Opens, Function.Injective (φ.app U) := by
  constructor
  · intro hφ U

    let ev : TopCat.Presheaf Ab.{u} X ⥤ Ab.{u} := (CategoryTheory.evaluation _ Ab.{u}).obj (op U)
    haveI : Mono ((Scheme.Modules.toPresheaf X).map φ) :=
      preserves_mono_of_preservesLimit (Scheme.Modules.toPresheaf X) φ
    haveI : PreservesLimitsOfShape WalkingCospan ev := evaluation_preservesLimitsOfShape _
    haveI : Mono (ev.map ((Scheme.Modules.toPresheaf X).map φ)) := preserves_mono_of_preservesLimit _ _
    have h : Mono (φ.app U) := this
    exact (AddCommGrpCat.mono_iff_injective (φ.app U)).1 h
  · intro h
    refine ⟨fun g g' w => ?_⟩
    refine Scheme.Modules.hom_ext g g' fun U => ?_
    ext x
    apply h U
    have := congr(($w).app U x)
    simpa [Scheme.Modules.Hom.comp_app] using this

end S_AlgebraicGeometry_Scheme_Modules_Hom_mono_iff_injective
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_Hom_mono_iff_injective (solution)
