-- Prove2me | solution 1 for AlgebraicCurve.Place.taylorRem_mem_toValuationSubring
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/7a3924d4-b9ca-537c-856b-883735d57705

import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_taylorRem_mem_toValuationSubring

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place

namespace P2MJetT1

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem evalAt_sub_of_mem' (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_sub, v.algebraMap_evalAt hv (sub_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_sub]
  rfl

theorem ord_nonneg_of_mem' (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) :
    0 ≤ v.ord f :=
  ((v.adicValuation_le_one_iff).mp (v.adicValuation_le_one_of_mem hf)).resolve_left hf0

theorem sub_evalAt_mul_inv_mem' (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1)
    {g : F} (hg : g ∈ v.toValuationSubring) :
    (g - algebraMap K F (v.evalAt g)) * t⁻¹ ∈ v.toValuationSubring := by
  have hc : algebraMap K F (v.evalAt g) ∈ v.toValuationSubring := v.algebraMap_mem' _
  have hx : g - algebraMap K F (v.evalAt g) ∈ v.toValuationSubring := sub_mem hg hc
  by_cases hx0 : g - algebraMap K F (v.evalAt g) = 0
  · rw [hx0, zero_mul]; exact zero_mem _
  have ht0 : t ≠ 0 := by rintro rfl; simp [Place.ord_zero] at ht
  have hval : v.evalAt (g - algebraMap K F (v.evalAt g)) = 0 := by
    rw [P2MJetT1.evalAt_sub_of_mem' v hv hg hc, v.evalAt_algebraMap_eq, sub_self]
  have hord0 : v.ord (g - algebraMap K F (v.evalAt g)) ≠ 0 := fun h0 =>
    v.evalAt_ne_zero_of_ord_eq_zero hv hx0 h0 hval
  have hord1 : 1 ≤ v.ord (g - algebraMap K F (v.evalAt g)) := by
    have := P2MJetT1.ord_nonneg_of_mem' v hx hx0; omega
  apply v.mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero hx0 (inv_ne_zero ht0))
  rw [v.ord_mul hx0 (inv_ne_zero ht0), v.ord_inv, ht]
  omega

end P2MJetT1

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1) {f : F}
    (hf : f ∈ v.toValuationSubring) (r : ℕ) :
    taylorRem v t f r ∈ v.toValuationSubring := by
  induction r with
  | zero => simpa using hf
  | succ r ih =>
    rw [taylorRem_succ]
    exact P2MJetT1.sub_evalAt_mul_inv_mem' v hv ht ih

end S_AlgebraicCurve_Place_taylorRem_mem_toValuationSubring
end P2MW
export P2MW.S_AlgebraicCurve_Place_taylorRem_mem_toValuationSubring (solution)
