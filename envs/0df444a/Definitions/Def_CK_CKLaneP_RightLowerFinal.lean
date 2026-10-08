-- Prove2me | Definitions.Def_CK_CKLaneP_RightLowerFinal
-- name    : CK_CKLaneP_RightLowerFinal
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T06:59:02.067989+00:00
-- url     : https://prove2.me/theorems/c8dda520-6779-4437-bcdd-db22e8ccf62d
-- title:
--   Courtade–Kumar proof module `CKLaneP.RightLowerFinal` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.RightLowerFinal` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.RightLowerFinal` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.RightLowerFinal (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/RightLowerFinal.lean)

import Definitions.Def_CK_CKLaneP_RightLower
import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBatchJointOwnerAdapter

-- ===== source module CKLaneP.RightLowerFinal =====
section
/-
Lane P — FINAL instantiation of the `rightLower` field (merged provider root P/genroot).

`rightLower_of_doubleCap` (CKLaneP.RightLower) + the compiled external double-cap owner
`GeneralCK.canonicalDoubleCapEntropyEndpoints_of_joint_batches` (I-A root closure, hardlinked into
P/genroot; the 170 modules shared with ~/gck_lanes/F-C/work/root are byte-identical).
-/

set_option autoImplicit false

namespace CKLaneP

open GeneralCK SmallMeanPhiCutoff

/-- The `rightLower` field of `CanonicalPureGapCapFiberOwnersExceptEqual retainedCutoff`. -/
theorem rightLower_certified :
    ∀ e f : ℝ, 0 < e → e < f → f ≤ 1 →
      capFiberLower retainedCutoff e (entropyInverse f) ≤ entropyInverse f →
      0 ≤ canonicalPureGap (capFiberLower retainedCutoff e (entropyInverse f))
        (entropyInverse f) e f :=
  rightLower_of_doubleCap canonicalDoubleCapEntropyEndpoints_of_joint_batches

/-- The statement above is exactly the type of the structure field. -/
example : (∀ o : CanonicalPureGapCapFiberOwnersExceptEqual retainedCutoff,
    ∀ e f : ℝ, 0 < e → e < f → f ≤ 1 →
      capFiberLower retainedCutoff e (entropyInverse f) ≤ entropyInverse f →
      0 ≤ canonicalPureGap (capFiberLower retainedCutoff e (entropyInverse f))
        (entropyInverse f) e f) := fun o => o.rightLower

end CKLaneP

end


