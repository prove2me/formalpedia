-- Prove2me | solution 1 for AlgebraicCurve.SemilinearAut.ofAlgAut_smul_place
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/9e923100-2efb-5337-b2cb-65df440e37b5

import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_SemilinearAut_ofAlgAut_smul_place

open scoped Pointwise

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (σ : F ≃ₐ[K] F) (v : AlgebraicCurve.Place K F) : AlgebraicCurve.SemilinearAut.ofAlgAut σ • v = σ • v := by
  have hfun : ∀ x : F, AlgebraicCurve.SemilinearAut.ofAlgAut σ • x = σ • x := fun _ => rfl
  apply AlgebraicCurve.Place.toValuationSubring_injective
  ext x
  rw [AlgebraicCurve.SemilinearAut.smul_toValuationSubring, AlgebraicCurve.Place.smul_toValuationSubring,
    ValuationSubring.mem_smul_pointwise_iff_exists,
    ValuationSubring.mem_smul_pointwise_iff_exists]
  simp only [hfun]

end S_AlgebraicCurve_SemilinearAut_ofAlgAut_smul_place
end P2MW
export P2MW.S_AlgebraicCurve_SemilinearAut_ofAlgAut_smul_place (solution)
