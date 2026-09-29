-- Prove2me | solution 1 for AlgebraicCurve.WeilDatum.symm_pairing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/994f5429-b9d1-599c-bb43-1fe3a611f6ab

import Definitions.Def_AlgebraicCurve_WeilDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_WeilDatum_symm_pairing

open AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} (d : WeilDatum K F n) : d.symm.pairing = d.pairing⁻¹ := by
  rw [WeilDatum.pairing, WeilDatum.pairing, inv_div]
  rfl

end S_AlgebraicCurve_WeilDatum_symm_pairing
end P2MW
export P2MW.S_AlgebraicCurve_WeilDatum_symm_pairing (solution)
