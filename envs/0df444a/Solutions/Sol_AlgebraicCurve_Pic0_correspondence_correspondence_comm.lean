-- Prove2me | solution 1 for AlgebraicCurve.Pic0.correspondence_correspondence_comm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/7564fc78-bb7b-5804-98cb-be3240bcf168

import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_correspondence_correspondence_comm

set_option autoImplicit false

open IsDedekindDomain AlgebraicCurve

theorem solution {K F F₁ F₂ : Type*} [Field K] [Field F] [Field F₁] [Field F₂] [Algebra K F] [Algebra K F₁] [Algebra K F₂] [HasPrincipalDivisors K F₁] [HasPrincipalDivisors K F₂] (φ ψ : F →ₐ[K] F₁) (φ' ψ' : F →ₐ[K] F₂) (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (hφ' : φ'.toRingHom.IsIntegral) (hψ' : ψ'.toRingHom.IsIntegral) (hFI : FundamentalIdentityAlong K φ hφ) (hfin : FiniteAlong K ψ) (hN : NormFormulaAlong K ψ hfin) (hFI' : FundamentalIdentityAlong K φ' hφ') (hfin' : FiniteAlong K ψ') (hN' : NormFormulaAlong K ψ' hfin') (hcomm : ∀ D : Divisor K F, Divisor.correspondence φ ψ hφ hψ (Divisor.correspondence φ' ψ' hφ' hψ' D) = Divisor.correspondence φ' ψ' hφ' hψ' (Divisor.correspondence φ ψ hφ hψ D)) (x : Pic0 K F) : Pic0.correspondence φ ψ hφ hψ hFI hfin hN (Pic0.correspondence φ' ψ' hφ' hψ' hFI' hfin' hN' x) = Pic0.correspondence φ' ψ' hφ' hψ' hFI' hfin' hN' (Pic0.correspondence φ ψ hφ hψ hFI hfin hN x) := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [Pic0.correspondence_mk, Pic0.correspondence_mk, Pic0.correspondence_mk, Pic0.correspondence_mk]
  exact congrArg Pic0.mk (Subtype.ext (hcomm (D : Divisor K F)))

end S_AlgebraicCurve_Pic0_correspondence_correspondence_comm
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_correspondence_correspondence_comm (solution)
