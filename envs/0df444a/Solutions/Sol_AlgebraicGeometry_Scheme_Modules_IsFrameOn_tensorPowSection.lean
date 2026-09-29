-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsFrameOn.tensorPowSection
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/28fe2ff0-0920-5c7e-8ccc-8acb7a53f237

import Mathlib
import Definitions.Def_PresheafOfModules_InternalHom
import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorPowSection

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry"

set_option autoImplicit false

theorem solution {X : AlgebraicGeometry.Scheme.{u}} {L : X.Modules} {U V : X.Opens} {s : Γ(L, U)}
    (hs : AlgebraicGeometry.Scheme.Modules.IsFrameOn s V) (n : ℕ) :
    AlgebraicGeometry.Scheme.Modules.IsFrameOn
      (AlgebraicGeometry.Scheme.Modules.tensorPowSection s n) V := by
  induction n with
  | zero => exact AlgebraicGeometry.Scheme.Modules.isFrameOn_unitSection V
  | succ n ih =>
    rw [AlgebraicGeometry.Scheme.Modules.tensorPowSection_succ]
    exact AlgebraicGeometry.Scheme.Modules.IsFrameOn.tensorSections ih hs

end S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorPowSection
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorPowSection (solution)
