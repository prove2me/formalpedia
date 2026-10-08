-- Prove2me | Definitions.Def_CK_CKLaneN1_LeftLowerFinal
-- name    : CK_CKLaneN1_LeftLowerFinal
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T21:02:42.41234+00:00
-- url     : https://prove2.me/theorems/f50d3391-e94a-49ab-b27f-4271c00ec4f3
-- title:
--   Courtade–Kumar proof module `CKLaneN1.LeftLowerFinal` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1.LeftLowerFinal` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1.LeftLowerFinal` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1.LeftLowerFinal (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1/LeftLowerFinal.lean)

import Definitions.Def_CK_CKLaneN1_EdgeFinal
import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBatchJointOwnerAdapter

-- ===== source module CKLaneN1.LeftLowerFinal =====
section
/-
Lane N1 — FINAL instantiation of the `leftLower` field of
`CanonicalPureGapCapFiberOwnersExceptEqual retainedCutoff` (provider root P/genroot).

Case `b ≥ S - a` (double cap): the compiled external owner
`GeneralCK.canonicalDoubleCapEntropyEndpoints_of_joint_batches` (I-A closure in P/genroot) through
`canonicalPureGap_inverse_doubleCap_nonneg_of_scalar_endpoints`.
Case `a + b < S` (cutoff edge): `CKLaneN1.Edge.leftEdge_retained` (kernel-checked box tree).
The case split is the one of `PositiveCutoffCapProbabilityOwners.toExceptEqual` (corpus source
`PureGapPositiveCutoffCapReduction.lean`, not compiled in the provider root).
-/

set_option autoImplicit false

namespace CKLaneN1.Edge

open GeneralCK SmallMeanPhiCutoff

/-- The `leftLower` field of `CanonicalPureGapCapFiberOwnersExceptEqual retainedCutoff`. -/
theorem leftLower_certified :
    ∀ e f : ℝ, 0 < e → e < f → f ≤ 1 →
      capFiberLower retainedCutoff f (entropyInverse e) ≤ 1 / 2 →
      0 ≤ canonicalPureGap (entropyInverse e) (capFiberLower retainedCutoff f (entropyInverse e))
        e f := by
  intro e f he hef hf hhalf
  have hie := entropyInverse_spec he.le (hef.le.trans hf)
  have hif := entropyInverse_spec (he.trans hef).le hf
  have ha : 0 < entropyInverse e := entropyInverse_pos he (hef.le.trans hf)
  have hab : entropyInverse e < entropyInverse f := entropyInverse_strictMonoOn
    ⟨he.le, hef.le.trans hf⟩ ⟨(he.trans hef).le, hf⟩ hef
  have hb : entropyInverse f ≤ 1 / 2 := hif.2.1
  by_cases hedge : retainedCutoff - entropyInverse e ≤ entropyInverse f
  · have hmax : capFiberLower retainedCutoff f (entropyInverse e) = entropyInverse f := by
      unfold capFiberLower
      exact max_eq_left hedge
    rw [hmax]
    exact canonicalPureGap_inverse_doubleCap_nonneg_of_scalar_endpoints
      canonicalDoubleCapEntropyEndpoints_of_joint_batches he hef hf
  · have hbEdge : entropyInverse f < retainedCutoff - entropyInverse e := lt_of_not_ge hedge
    have hmax : capFiberLower retainedCutoff f (entropyInverse e) =
        retainedCutoff - entropyInverse e := by
      unfold capFiberLower
      exact max_eq_right hbEdge.le
    have hhalf' : retainedCutoff - entropyInverse e ≤ 1 / 2 := by
      rw [hmax] at hhalf
      exact hhalf
    have hv := leftEdge_retained (entropyInverse e) (entropyInverse f) ha hab hb hbEdge hhalf'
    rw [hie.2.2, hif.2.2] at hv
    rw [hmax]
    exact hv

/-- Binding check: `leftLower_certified` is accepted in the `leftLower` slot of the structure
(elaborated against the field's own expected type). -/
example (o : CanonicalPureGapCapFiberOwnersExceptEqual retainedCutoff) :
    CanonicalPureGapCapFiberOwnersExceptEqual retainedCutoff :=
  { o with leftLower := leftLower_certified }

end CKLaneN1.Edge

end


