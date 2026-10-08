-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_TateNormalFormBridge_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_TateNormalFormBridge_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:46:58.237547+00:00
-- url     : https://prove2.me/theorems/58c26ea5-8ad5-491c-a0e6-3db42f4c1860
-- title:
--   FLT.Assumptions.MazurProof.TateNormalFormBridge source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.TateNormalFormBridge

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.TateNormalFormBridge
Original leading source comments and nonproject imports are retained below. -/
import Mathlib
import Definitions.Def_MazurN13_scratch_TateZ2xZ10Reduction_p0
import Theorems.Thm_MazurHuang_exists_tate_normal_form_of_addOrderOf_gt_three

set_option autoImplicit false




/-!
# A reusable Tate-normal-form bridge

The N=10 and N=12 reductions contain the same normalization argument.  This
file extracts the part that depends only on a marked point of order greater
than three: after two explicit Weierstrass variable changes, the marked point
is `(0,0)` on Tate normal form and its additive order is preserved.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.TateNormalFormBridge

open Scratch.TateZ2xZ10Reduction

noncomputable section

private lemma tate_origin_nonsingular
    (b c : ℚ) [WeierstrassCurve.IsElliptic (tateNormalFormCurve b c)] :
    WeierstrassCurve.Affine.Nonsingular (tateNormalFormCurve b c) 0 0 := by
  apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [tateNormalFormCurve]

/-- The marked origin on Tate normal form. -/
def tateOrigin (b c : ℚ)
    [WeierstrassCurve.IsElliptic (tateNormalFormCurve b c)] :
    WeierstrassCurve.Affine.Point (tateNormalFormCurve b c) :=
  WeierstrassCurve.Affine.Point.some 0 0 (tate_origin_nonsingular b c)

/-- The Tate-normal-form bridge with only the order and nonvanishing data (statement as in
`FLT/Assumptions/MazurProof/TateNormalFormBridge.lean`), here obtained from the published
theorem `MazurHuang.exists_tate_normal_form_of_addOrderOf_gt_three`, which states the same
fact with the curve and the marked point written out. -/
theorem exists_tate_normalized_of_addOrder_gt_three
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (n : ℕ) (hn : 3 < n)
    (hP : addOrderOf P = n) :
    ∃ b c : ℚ,
      ∃ _hEll : WeierstrassCurve.IsElliptic (tateNormalFormCurve b c),
        addOrderOf (tateOrigin b c) = n ∧ b ≠ 0 := by
  obtain ⟨b, c, hb, hEll, _h, hord⟩ :=
    MazurHuang.exists_tate_normal_form_of_addOrderOf_gt_three E P n hn hP
  exact ⟨b, c, hEll, hord, hb⟩

end

end MazurProof.TateNormalFormBridge


