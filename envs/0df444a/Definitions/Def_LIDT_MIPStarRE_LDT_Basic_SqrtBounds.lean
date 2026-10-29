-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SqrtBounds
-- name    : LIDT_MIPStarRE_LDT_Basic_SqrtBounds
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T10:47:03.968125+00:00
-- url     : https://prove2.me/theorems/c2e30a62-be19-4a2a-ac47-5fd8fdcdd7fb
-- title:
--   LIDT definitions: LDT / Basic / SqrtBounds
-- statement:
--   This bundle records the square-root subadditivity estimates used throughout the error bookkeeping. It handles both two-term and three-term sums of nonnegative errors, allowing separate contributions to be absorbed into a single square-root bound.
--
--   Principal definitions:
--   - `sqrt_add_le_add_sqrt`: bounds the square root of a two-term sum by the sum of square roots.
--   - `sqrt_add3_le_add3_sqrt`: gives the corresponding three-term bound.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Basic/SqrtBounds.lean#L15-L30

-- Generated from MIPStarRE/LDT/Basic/SqrtBounds.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Mathlib

namespace LIDT

/-!
# Square-root bounds for error estimates

Small reusable inequalities for square roots of nonnegative error terms.
-/

@[expose] public section

namespace MIPStarRE.LDT

/-- Subadditivity of the square root on nonnegative error terms. -/
theorem sqrt_add_le_add_sqrt {x y : Error} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  refine Real.sqrt_le_iff.mpr ?_
  refine ⟨by positivity, ?_⟩
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, Real.sqrt_nonneg x, Real.sqrt_nonneg y]

/-- Three-term subadditivity of the square root on nonnegative error terms. -/
theorem sqrt_add3_le_add3_sqrt {x y z : Error}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    Real.sqrt (x + y + z) ≤ Real.sqrt x + Real.sqrt y + Real.sqrt z := by
  calc
    Real.sqrt (x + y + z) = Real.sqrt ((x + y) + z) := by ring_nf
    _ ≤ Real.sqrt (x + y) + Real.sqrt z := sqrt_add_le_add_sqrt (add_nonneg hx hy) hz
    _ ≤ Real.sqrt x + Real.sqrt y + Real.sqrt z := by
      nlinarith [sqrt_add_le_add_sqrt hx hy, Real.sqrt_nonneg z]

end MIPStarRE.LDT

end

end LIDT


