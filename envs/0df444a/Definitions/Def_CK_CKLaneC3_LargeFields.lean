-- Prove2me | Definitions.Def_CK_CKLaneC3_LargeFields
-- name    : CK_CKLaneC3_LargeFields
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T22:34:56.335984+00:00
-- url     : https://prove2.me/theorems/de1bfc79-2003-40d1-bedd-a22d0ae30a05
-- title:
--   Courtade–Kumar proof module `CKLaneC3.LargeFields` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC3.LargeFields` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC3.LargeFields` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC3.LargeFields (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC3/LargeFields.lean)

import Definitions.Def_CK_E8GlobalRatioCertificate
import Definitions.Def_CK_E8LargeTFinal
import Definitions.Def_CK_GeneralCK_PureGapE8CertificateReduction

-- ===== source module CKLaneC3.LargeFields =====
section

/-!
# Lane C3 — the `largeS`, `largeT`, `smallSTail` fields of `GeneralCK.E8CertificateOwners`

Re-verified P-E8 results over the final assembly root `~/ck_lanes_20260923/coord/asmRoot`, importing
the CANONICAL E8 modules (`E8GlobalRatioCertificate` = C2's pinned 989ac0b7…1461, `E8LargeTFinal`)
rather than lane copies (integration conflict C3):

* `largeS` is `GeneralCK.E8RatioMonotonicity.e8LargeSCertified` (ratio monotonicity of the E8
  inverse; canonical 14-module ratio package over the canonical GeneralCK large-s modules);
* `largeT` is `GeneralCK.E8LargeTSAxis.largeT`;
* `smallSTail` follows from `GeneralCK.E8LargeTSAxis.largeT_elevenNine`, whose region
  `119/10 ≤ t ∧ s ≤ 63/20` contains `20 ≤ t ∧ s ≤ 1/200`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneC3.LargeFields

open GeneralCK

/-- The `largeS` field of `GeneralCK.E8CertificateOwners`, with its exact type. -/
theorem largeS : E8PositiveOn fun s _ => (63 / 20 : ℝ) ≤ s :=
  GeneralCK.E8RatioMonotonicity.e8LargeSCertified

/-- The `largeT` field of `GeneralCK.E8CertificateOwners`, with its exact type. -/
theorem largeT : E8PositiveOn fun s t => (119 / 10 : ℝ) ≤ t ∧ (1 / 200 : ℝ) ≤ s ∧ s ≤ 63 / 20 :=
  GeneralCK.E8LargeTSAxis.largeT

/-- The `smallSTail` field of `GeneralCK.E8CertificateOwners`, with its exact type. -/
theorem smallSTail : E8PositiveOn fun s t => (20 : ℝ) ≤ t ∧ s ≤ 1 / 200 := by
  intro s t hadm h
  have h' : (20 : ℝ) ≤ t ∧ s ≤ 1 / 200 := h
  exact GeneralCK.E8LargeTSAxis.largeT_elevenNine s t hadm
    ⟨by linarith [h'.1], by linarith [h'.2]⟩

end CKLaneC3.LargeFields

end


