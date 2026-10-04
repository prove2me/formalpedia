-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftUpperAfterHalfCollarAndNarrow
-- name    : CK_GeneralCK_PureGapZeroCapLeftUpperAfterHalfCollarAndNarrow
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T03:04:36.782699+00:00
-- url     : https://prove2.me/theorems/0d0d6b00-5854-40c9-954d-3a5cf5dc4e49
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapZeroCapLeftUpperAfterHalfCollarAndNarrow` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapZeroCapLeftUpperAfterHalfCollarAndNarrow` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapZeroCapLeftUpperAfterHalfCollarAndNarrow` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapZeroCapLeftUpperAfterHalfCollarAndNarrow (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapZeroCapLeftUpperAfterHalfCollarAndNarrow.lean)

import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftUpperAfterHalfCollar
import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftUpperNarrowRectangle

-- ===== source module GeneralCK.PureGapZeroCapLeftUpperAfterHalfCollarAndNarrow =====
section

/-! The exact left-upper remainder after two unconditional certified regions. -/

namespace GeneralCK

def LeftUpperOutsideHalfCollarAndNarrowOwner : Prop :=
  ∀ a b : ℝ, 0 < a → a < b → b < 1 / 2 → a < 31 / 64 →
    ¬ ((1 / 8 : ℝ) ≤ a ∧ a ≤ 129 / 1024 ∧
      129 / 1024 ≤ b ∧ b ≤ 65 / 512) →
    0 ≤ canonicalPureGap a (1 / 2) (H a) (H b)

theorem leftUpper_outsideHalfCollar_of_outsideNarrow
    (h : LeftUpperOutsideHalfCollarAndNarrowOwner) :
    LeftUpperOutsideHalfCollarOwner := by
  intro a b ha hab hb ha31
  by_cases hrect : (1 / 8 : ℝ) ≤ a ∧ a ≤ 129 / 1024 ∧
      129 / 1024 ≤ b ∧ b ≤ 65 / 512
  · exact ZeroCapLeftUpperNarrow.leftUpper_on_narrow_rectangle
      hrect.1 hrect.2.1 hrect.2.2.1 hrect.2.2.2 hab
  · exact h a b ha hab hb ha31 hrect

theorem zeroCap_leftUpper_of_outsideHalfCollarAndNarrow
    (h : LeftUpperOutsideHalfCollarAndNarrowOwner) :
    ∀ e f, 0 < e → e < f → f < 1 →
      0 ≤ canonicalPureGap (entropyInverse e) (1 / 2) e f :=
  zeroCap_leftUpper_of_outsideHalfCollar
    (leftUpper_outsideHalfCollar_of_outsideNarrow h)

#print axioms leftUpper_outsideHalfCollar_of_outsideNarrow
#print axioms zeroCap_leftUpper_of_outsideHalfCollarAndNarrow

end GeneralCK

end


