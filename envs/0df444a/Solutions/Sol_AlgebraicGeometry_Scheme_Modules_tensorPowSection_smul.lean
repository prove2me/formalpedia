-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.tensorPowSection_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/634b9d95-a1bb-59a1-ad29-4b8a88a3d34f

import Mathlib
import Definitions.Def_PresheafOfModules_InternalHom
import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_tensorPowSection_smul

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry"

set_option autoImplicit false

open AlgebraicGeometry.Scheme.Modules in

theorem solution {X : AlgebraicGeometry.Scheme.{u}} {L : X.Modules} {U : X.Opens} (g : Γ(X, U)) (s : Γ(L, U)) (n : ℕ) :
    AlgebraicGeometry.Scheme.Modules.tensorPowSection (g • s) n =
      g ^ n • AlgebraicGeometry.Scheme.Modules.tensorPowSection s n := by
  induction n with
  | zero => rw [tensorPowSection_zero, tensorPowSection_zero, pow_zero, one_smul]
  | succ n ih =>
    rw [tensorPowSection_succ, tensorPowSection_succ, ih, tensorSections_smul_left, tensorSections_smul_right,
      smul_smul, ← pow_succ]
    try rfl

end S_AlgebraicGeometry_Scheme_Modules_tensorPowSection_smul
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_tensorPowSection_smul (solution)
