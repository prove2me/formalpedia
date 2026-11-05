-- Prove2me | Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
-- name    : AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-03T23:31:41.3842+00:00
-- url     : https://prove2.me/theorems/4c0b840b-c1d8-4087-81ff-ad3ec077ddde
-- title:
--   Original source intrinsic large negative jump sum
-- statement:
--   On original Omega, define Jlarge(t,omega) as the literal signed mark integral of X's intrinsic marked jump measure over (0,t] and marks (-infinity,-1], including z=-1 and excluding zero time. This is the same-source large-jump term to subtract when constructing Mc; no unrelated Levy process or martingale assumption.
-- source:
--   Proved original separated negative jump count finiteness (3537a106); exact source mark measure integral equals source finite jump sum (b881e8e7).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- The genuine original source X integral of its large negative jump marks
on (0,t], including marks exactly -1; no compensation is subtracted. -/
noncomputable def avram_p4_h_gaussian_intrinsic_large_jump_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ p in (Ioc (0 : ℝ≥0) t ×ˢ Iic (-1 : ℝ)),
    p.2 ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))

end AvramDividend.Classical


