-- Prove2me | solution 1 for AlgebraicCurve.Place.restrictAlong_algEquiv_eq_ofAlgAut_symm_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/094bff7b-1dcb-5ec0-8e08-1f0e49c0a852

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_restrictAlong_algEquiv_eq_ofAlgAut_symm_smul

set_option autoImplicit false

open AlgebraicCurve
open scoped Pointwise

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (σ : F ≃ₐ[K] F) (hσ : σ.toAlgHom.toRingHom.IsIntegral) (v : Place K F) :
    v.restrictAlong σ.toAlgHom hσ = SemilinearAut.ofAlgAut σ.symm • v := by
  apply Place.ext
  rw [SemilinearAut.smul_toValuationSubring]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, SemilinearAut.inv_smul_def,
    SemilinearAut.toRingAut_ofAlgAut]
  show σ x ∈ v.toValuationSubring ↔ _
  rfl

#print axioms solution

end S_AlgebraicCurve_Place_restrictAlong_algEquiv_eq_ofAlgAut_symm_smul
end P2MW
export P2MW.S_AlgebraicCurve_Place_restrictAlong_algEquiv_eq_ofAlgAut_symm_smul (solution)
