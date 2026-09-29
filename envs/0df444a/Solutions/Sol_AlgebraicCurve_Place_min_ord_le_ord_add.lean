-- Prove2me | solution 1 for AlgebraicCurve.Place.min_ord_le_ord_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/0d17451d-b08c-5c66-a8d5-342e7d970351

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_min_ord_le_ord_add

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord"
namespace FF2S
p2m_open "AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem le_ord_add (v : Place K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) :
    min (v.ord f) (v.ord g) ≤ v.ord (f + g) := by
  have hf' := v.adicValuation_ne_zero hf
  have hg' := v.adicValuation_ne_zero hg
  have hfg' := v.adicValuation_ne_zero hfg
  have hmax : v.adicValuation (f + g) ≤ max (v.adicValuation f) (v.adicValuation g) :=
    Valuation.map_add _ _ _
  unfold Place.ord
  rcases le_max_iff.mp hmax with hle | hle
  · have := (WithZero.log_le_log hfg' hf').mpr hle
    omega
  · have := (WithZero.log_le_log hfg' hg').mpr hle
    omega

end AlgebraicCurve.FF2S

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) :
    min (v.ord f) (v.ord g) ≤ v.ord (f + g) :=
  AlgebraicCurve.FF2S.le_ord_add v hf hg hfg

end S_AlgebraicCurve_Place_min_ord_le_ord_add
end P2MW
export P2MW.S_AlgebraicCurve_Place_min_ord_le_ord_add (solution)
