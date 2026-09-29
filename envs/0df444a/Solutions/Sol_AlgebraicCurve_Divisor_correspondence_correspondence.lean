-- Prove2me | solution 1 for AlgebraicCurve.Divisor.correspondence_correspondence
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/1e09e43d-9435-5c17-87c8-9ea3a22604f4

import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_AlgebraicCurve_Divisor_pullbackAlong_pullbackAlong
import Theorems.Thm_AlgebraicCurve_Divisor_pushforwardAlong_pushforwardAlong
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Divisor_correspondence_correspondence

set_option autoImplicit false

open IsDedekindDomain AlgebraicCurve

theorem solution {K F F₁ F₂ Z : Type*} [Field K] [Field F] [Field F₁] [Field F₂] [Field Z] [Algebra K F] [Algebra K F₁] [Algebra K F₂] [Algebra K Z] [HasPrincipalDivisors K F₁] [HasPrincipalDivisors K F₂] [HasPrincipalDivisors K Z] (φ ψ : F →ₐ[K] F₁) (φ' ψ' : F →ₐ[K] F₂) (u : F₁ →ₐ[K] Z) (u' : F₂ →ₐ[K] Z) (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (hφ' : φ'.toRingHom.IsIntegral) (hψ' : ψ'.toRingHom.IsIntegral) (hu : u.toRingHom.IsIntegral) (hu' : u'.toRingHom.IsIntegral) (huφ' : (u'.comp φ').toRingHom.IsIntegral) (huψ : (u.comp ψ).toRingHom.IsIntegral) (hex : ∀ D : Divisor K F₂, Divisor.pullbackAlong φ hφ (Divisor.pushforwardAlong ψ' hψ' D) = Divisor.pushforwardAlong u hu (Divisor.pullbackAlong u' hu' D)) (D : Divisor K F) : Divisor.correspondence φ ψ hφ hψ (Divisor.correspondence φ' ψ' hφ' hψ' D) = Divisor.correspondence (u'.comp φ') (u.comp ψ) huφ' huψ D := by
  rw [Divisor.correspondence_apply, Divisor.correspondence_apply, Divisor.correspondence_apply,
    hex (Divisor.pullbackAlong φ' hφ' D),
    AlgebraicCurve.Divisor.pushforwardAlong_pushforwardAlong ψ u hψ hu huψ,
    AlgebraicCurve.Divisor.pullbackAlong_pullbackAlong φ' u' hφ' hu' huφ']

end S_AlgebraicCurve_Divisor_correspondence_correspondence
end P2MW
export P2MW.S_AlgebraicCurve_Divisor_correspondence_correspondence (solution)
