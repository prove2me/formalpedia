-- Prove2me | solution 1 for AlgebraicCurve.Place.ord_smul_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/1674e0b0-7466-5d27-9782-8d136657c972

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_ord_smul_of_ne_zero

set_option autoImplicit false

open AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {c : K} (hc : c ≠ 0) (x : F) : v.ord (c • x) = v.ord x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [smul_zero]
  · have halg : algebraMap K F c ≠ 0 :=
      fun h => hc ((algebraMap K F).injective (by rw [h, map_zero]))
    have hunit : IsUnit (⟨algebraMap K F c, v.algebraMap_mem' c⟩ : v.toValuationSubring) := by
      refine isUnit_iff_exists_inv.mpr ⟨⟨algebraMap K F c⁻¹, v.algebraMap_mem' c⁻¹⟩, ?_⟩
      ext
      simp [mul_inv_cancel₀ halg]
    have h0 : v.ord (algebraMap K F c) = 0 := by
      have h1 : v.adicValuation (algebraMap K F c) = 1 :=
        (v.adicValuation_coe_eq_one_iff ⟨algebraMap K F c, v.algebraMap_mem' c⟩).mpr hunit
      simp [AlgebraicCurve.Place.ord, h1]
    rw [Algebra.smul_def, v.ord_mul halg hx0, h0, zero_add]

end S_AlgebraicCurve_Place_ord_smul_of_ne_zero
end P2MW
export P2MW.S_AlgebraicCurve_Place_ord_smul_of_ne_zero (solution)
