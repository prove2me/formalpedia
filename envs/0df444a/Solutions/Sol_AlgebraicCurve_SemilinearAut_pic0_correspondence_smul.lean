-- Prove2me | solution 1 for AlgebraicCurve.SemilinearAut.pic0_correspondence_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/a894daa4-2948-5ddf-92cc-669a7a2e0a9e

import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_AlgebraicCurve_SemilinearAut_correspondence_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_SemilinearAut_pic0_correspondence_smul

open AlgebraicCurve AlgebraicCurve.SemilinearAut

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    {g : SemilinearAut K F} {g' : SemilinearAut K F'} [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hFI : FundamentalIdentityAlong K φ hφ) (hfin : FiniteAlong K ψ)
    (hN : NormFormulaAlong K ψ hfin)
    (hgφ : IntertwinesAlong φ.toRingHom g g') (hgψ : IntertwinesAlong ψ.toRingHom g g')
    (c : Pic0 K F) :
    Pic0.correspondence φ ψ hφ hψ hFI hfin hN (g • c)
      = g • Pic0.correspondence φ ψ hφ hψ hFI hfin hN c := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective c
  rw [pic0_smul_mk, Pic0.correspondence_mk, Pic0.correspondence_mk, pic0_smul_mk]
  congr 1
  apply Subtype.ext
  rw [Pic0.coe_degZeroCorrespondence, coe_degZeroSMulHom, coe_degZeroSMulHom,
    Pic0.coe_degZeroCorrespondence]
  exact correspondence_smul φ ψ hφ hψ hgφ hgψ (D : Divisor K F)

end S_AlgebraicCurve_SemilinearAut_pic0_correspondence_smul
end P2MW
export P2MW.S_AlgebraicCurve_SemilinearAut_pic0_correspondence_smul (solution)
