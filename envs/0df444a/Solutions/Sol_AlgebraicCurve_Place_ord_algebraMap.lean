-- Prove2me | solution 1 for AlgebraicCurve.Place.ord_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/3e52d324-acb0-5f10-abfd-f730853be6f1

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_ord_algebraMap

open IsDedekindDomain WithZero IsLocalRing

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "coe_algebraMap adicValuation adicValuation_coe_eq_one_iff ord ord_zero toValuationSubring"
p2m_open "AlgebraicCurve.Place"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.isUnit_algebraMap {c : K} (hc : c ≠ 0) :
    IsUnit (algebraMap K v.toValuationSubring c) :=
  (isUnit_iff_ne_zero.mpr hc).map _

p2m_export "AlgebraicCurve.Place" "isUnit_algebraMap"
private theorem _root_.AlgebraicCurve.Place.adicValuation_algebraMap {c : K} (hc : c ≠ 0) :
    v.adicValuation (algebraMap K F c) = 1 := by
  rw [← v.coe_algebraMap]
  exact (v.adicValuation_coe_eq_one_iff _).mpr (v.isUnit_algebraMap hc)

p2m_export "AlgebraicCurve.Place" "adicValuation_algebraMap"
private theorem rowMain (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [map_zero, v.ord_zero]
  · simp only [ord, v.adicValuation_algebraMap hc, log_one, neg_zero]

end Place

end AlgebraicCurve

end

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Place_ord_algebraMap.AlgebraicCurve in
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (c : K) :
    v.ord (algebraMap K F c) = 0 :=
  AlgebraicCurve.Place.rowMain v c

end S_AlgebraicCurve_Place_ord_algebraMap
end P2MW
export P2MW.S_AlgebraicCurve_Place_ord_algebraMap (solution)
