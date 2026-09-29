-- Prove2me | solution 1 for AlgebraicCurve.Pic0.pushforwardHom_pullbackHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/9746de16-1378-5a61-902d-e2b94602a115

import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Theorems.Thm_AlgebraicCurve_Divisor_pushforward_pullback_of_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_pushforwardHom_pullbackHom

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Pic0_pushforwardHom_pullbackHom.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Divisor.PushforwardNormFormula SumRamificationInertia Pic0.pullbackHom Pic0.pushforwardHom Divisor HasPrincipalDivisors Pic Pic0 Divisor.pushforward_pullback_of_finite"
namespace Pic0
p2m_export "AlgebraicCurve.Pic0" "pullbackHom pullbackHom_mk pushforwardHom pushforwardHom_mk mk mk_surjective"
p2m_open "AlgebraicCurve.Pic0 AlgebraicCurve"
variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F']

private theorem pushforwardHom_pullbackHom_s11 [Module.Finite F F'] [SumRamificationInertia K F F']
    (H : Divisor.PushforwardNormFormula K F F') (x : Pic0 K F) :
    pushforwardHom K F F' H (pullbackHom F' x) = (Module.finrank F F' : ℤ) • x := by
  obtain ⟨D, rfl⟩ := mk_surjective x
  rw [pullbackHom_mk, pushforwardHom_mk]
  rw [show ((Module.finrank F F' : ℤ) • mk D : Pic0 K F)
      = mk ((Module.finrank F F' : ℤ) • D) from rfl]
  exact congrArg mk (Subtype.ext (Divisor.pushforward_pullback_of_finite (D : Divisor K F)))

end AlgebraicCurve.Pic0

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F'] [Module.Finite F F'] [SumRamificationInertia K F F'] (H : Divisor.PushforwardNormFormula K F F') (x : Pic0 K F) : Pic0.pushforwardHom K F F' H (Pic0.pullbackHom F' x) = (Module.finrank F F' : ℤ) • x :=
  AlgebraicCurve.Pic0.pushforwardHom_pullbackHom_s11 H x

end S_AlgebraicCurve_Pic0_pushforwardHom_pullbackHom
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_pushforwardHom_pullbackHom (solution)
