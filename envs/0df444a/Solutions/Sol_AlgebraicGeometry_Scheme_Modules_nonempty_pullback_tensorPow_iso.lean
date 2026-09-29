-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.nonempty_pullback_tensorPow_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/5bf78409-6ae2-55ee-aae7-a45dcb2e5059

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_tensorPow_iso

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_tensorPow_iso.AlgebraicGeometry CategoryTheory.MonoidalCategory"

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Scheme Scheme.Modules Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Modules.pullback Modules Modules.pullbackTensorObjIso Modules.pullbackTensorUnitObjIso" namespace Modules p2m_export "AlgebraicGeometry.Scheme.Modules" "pullback tensorPow pullbackTensorObjIso pullbackTensorUnitObjIso" end AlgebraicGeometry.Scheme.Modules
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules" in

noncomputable def AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules) :
    ∀ n : ℕ, (Scheme.Modules.pullback f).obj (L.tensorPow n) ≅ ((Scheme.Modules.pullback f).obj L).tensorPow n
  | 0 => Scheme.Modules.pullbackTensorUnitObjIso f
  | n + 1 => Scheme.Modules.pullbackTensorObjIso f (L.tensorPow n) L ≪≫
      whiskerRightIso (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso f L n) _

theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules) (n : ℕ) :
    Nonempty ((Scheme.Modules.pullback f).obj (L.tensorPow n) ≅ ((Scheme.Modules.pullback f).obj L).tensorPow n) :=
  ⟨AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso f L n⟩

end S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_tensorPow_iso
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_tensorPow_iso (solution)
