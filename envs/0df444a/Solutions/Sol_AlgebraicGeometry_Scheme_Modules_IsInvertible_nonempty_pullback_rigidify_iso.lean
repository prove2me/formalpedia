-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_pullback_rigidify_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/d856b764-1de2-5729-9f64-42f535cb3747

import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_pullback_rigidify_iso

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry"

theorem solution
    {T P T' P' : Scheme.{u}} {σ : T ⟶ P} {q : P ⟶ T} {σ' : T' ⟶ P'} {q' : P' ⟶ T'}
    (ψ : T' ⟶ T) (Ψ : P' ⟶ P) (hσ : σ' ≫ Ψ = ψ ≫ σ) (hq : Ψ ≫ q = q' ≫ ψ)
    {L : P.Modules} (hL : Scheme.Modules.IsInvertible L) :
    Nonempty ((Scheme.Modules.pullback Ψ).obj (Scheme.Modules.rigidify σ q L) ≅
      Scheme.Modules.rigidify σ' q' ((Scheme.Modules.pullback Ψ).obj L)) := by
  have hσL : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback σ).obj L) :=
    Scheme.Modules.IsInvertible.pullback σ hL
  obtain ⟨d⟩ := Scheme.Modules.IsInvertible.pullback_dual ψ hσL

  let e₁ : (Scheme.Modules.pullback ψ).obj ((Scheme.Modules.pullback σ).obj L) ≅
      (Scheme.Modules.pullback σ').obj ((Scheme.Modules.pullback Ψ).obj L) :=
    (Scheme.Modules.pullbackComp ψ σ).app L ≪≫ (Scheme.Modules.pullbackCongr hσ.symm).app L ≪≫
      ((Scheme.Modules.pullbackComp σ' Ψ).app L).symm

  let M := Scheme.Modules.dual ((Scheme.Modules.pullback σ).obj L)
  let e₂ : (Scheme.Modules.pullback Ψ).obj ((Scheme.Modules.pullback q).obj M) ≅
      (Scheme.Modules.pullback q').obj ((Scheme.Modules.pullback ψ).obj M) :=
    (Scheme.Modules.pullbackComp Ψ q).app M ≪≫ (Scheme.Modules.pullbackCongr hq).app M ≪≫
      ((Scheme.Modules.pullbackComp q' ψ).app M).symm
  exact ⟨Scheme.Modules.pullbackTensorObjIso Ψ L _ ≪≫
    (Iso.refl _ ⊗ᵢ (e₂ ≪≫ (Scheme.Modules.pullback q').mapIso
      (d ≪≫ Scheme.Modules.dualMapIso e₁)))⟩

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_pullback_rigidify_iso
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_pullback_rigidify_iso (solution)
