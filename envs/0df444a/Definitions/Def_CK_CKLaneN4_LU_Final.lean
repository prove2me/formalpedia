-- Prove2me | Definitions.Def_CK_CKLaneN4_LU_Final
-- name    : CK_CKLaneN4_LU_Final
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T17:01:24.503578+00:00
-- url     : https://prove2.me/theorems/390819ab-5d59-4bd3-89f0-5220935cc5ca
-- title:
--   Courtade–Kumar proof module `CKLaneN4.LU.Final` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN4.LU.Final` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN4.LU.Final` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN4.LU.Final (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN4/LU/Final.lean)

import Definitions.Def_CK_CKLaneN4_LU_Owner
import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBatchJointOwnerAdapter
import Definitions.Def_CK_GeneralCK_PureGapCapAnalytic
import Definitions.Def_CK_GeneralCK_SmallMeanPhiRetainedCutoff

-- ===== source module CKLaneN4.LU.Final =====
section
/-
Lane N4b — FINAL: the `leftUpper` field of
`GeneralCK.CanonicalPureGapCapFiberOwnersExceptEqual retainedCutoff` (merged provider P/genroot).

* `f < 1`: `CKLaneN4.LU.leftUpper_lt_one` (certified cover, F-C root modules; byte-identical in genroot);
* `f = 1`: the double-cap value `canonicalPureGap (entropyInverse e) (entropyInverse 1) e 1`, owned by
  `GeneralCK.canonicalDoubleCapEntropyEndpoints_of_joint_batches` (I-A closure in P/genroot) through
  `canonicalPureGap_inverse_doubleCap_nonneg_of_scalar_endpoints`, exactly as Lane P's RightLowerFinal.
-/

set_option autoImplicit false

namespace CKLaneN4.LU

open GeneralCK SmallMeanPhiCutoff

theorem entropyInverse_one_eq : entropyInverse 1 = 1 / 2 := by
  have h := entropyInverse_H_lower (v := 1 / 2) (by norm_num) le_rfl
  rwa [H_half] at h

/-- The `leftUpper` field of `CanonicalPureGapCapFiberOwnersExceptEqual retainedCutoff`. -/
theorem leftUpper_certified :
    ∀ e f : ℝ, 0 < e → e < f → f ≤ 1 →
      capFiberLower retainedCutoff f (entropyInverse e) ≤ 1 / 2 →
      0 ≤ canonicalPureGap (entropyInverse e) (1 / 2) e f := by
  intro e f he hef hf _
  rcases lt_or_eq_of_le hf with hf1 | hf1
  · exact leftUpper_lt_one e f he hef hf1
  · subst hf1
    have h := canonicalPureGap_inverse_doubleCap_nonneg_of_scalar_endpoints
      canonicalDoubleCapEntropyEndpoints_of_joint_batches he hef le_rfl
    rwa [entropyInverse_one_eq] at h

/-- The statement above is exactly the type of the structure field. -/
example : (∀ o : CanonicalPureGapCapFiberOwnersExceptEqual retainedCutoff,
    ∀ e f : ℝ, 0 < e → e < f → f ≤ 1 →
      capFiberLower retainedCutoff f (entropyInverse e) ≤ 1 / 2 →
      0 ≤ canonicalPureGap (entropyInverse e) (1 / 2) e f) := fun o => o.leftUpper

end CKLaneN4.LU

end


