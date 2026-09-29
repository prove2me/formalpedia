-- Prove2me | solution 1 for AlgebraicCurve.exists_D_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/59e76fc4-337a-5583-8bd6-8eda6ea1db3e

import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_D_ne_zero

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F] : ∃ t : F, KaehlerDifferential.D K F t ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[F⁄K])
  have hmem : ω ∈ Submodule.span F (Set.range (KaehlerDifferential.D K F)) := by
    rw [KaehlerDifferential.span_range_derivation]
    exact Submodule.mem_top
  have hbot : Submodule.span F (Set.range (KaehlerDifferential.D K F)) = ⊥ :=
    Submodule.span_eq_bot.2 (by rintro _ ⟨t, rfl⟩; exact h t)
  rw [hbot, Submodule.mem_bot] at hmem
  exact hω hmem

end S_AlgebraicCurve_exists_D_ne_zero
end P2MW
export P2MW.S_AlgebraicCurve_exists_D_ne_zero (solution)
