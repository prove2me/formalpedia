-- Prove2me | Definitions.Def_CK_CKLaneN1_R3Assembly_q00
-- name    : CK_CKLaneN1_R3Assembly_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T17:38:14.965111+00:00
-- url     : https://prove2.me/theorems/6c9b8f20-e1ef-4660-9310-30945a3e145f
-- title:
--   Courtade–Kumar proof module `CKLaneN1.R3Assembly (piece 1 of 5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1.R3Assembly (piece 1 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1.R3Assembly (piece 1 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1.R3Assembly (piece 1 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1/R3Assembly (piece 1 of 5).lean)

import Definitions.Def_CK_CKLaneN1_R3Excl



/-!
# Lane N1 — CE-stat row 3: assembly of `TransverseCurvatureOwner` from the numeric cover

`CoverStmt` is the stationarity-free statement the numeric cover (M07) certifies on the normalized
domain `2^-17 ≤ a < 1/100` in coordinates `(a, z, y)`, `b = a + z y`, `c = a + y`.

* `transverse_of_cover : CoverStmt → TransverseCurvatureOwner` — every row-3 point satisfies the
  cover hypotheses (`a_lower`, `b < t_C ≤ 1/100`, `A ≤ 1/20`, retained cutoff), and
  `canonicalPureGap ≥ gapLB` (M07 `gapLB_le`, no stationarity used).
* `cover_of_octaves` — the octave dispatch: `CoverStmt` from `Sem` on the dyadic octave roots
  `[2^-k, 2^-(k-1)] × [0,1] × [0, Y_k]` together with the height exclusion `y_upper`.

Both are CONDITIONAL adapters; the closure instantiates them with the compiled cover.
-/

set_option autoImplicit false

namespace CKLaneN1.R3

open GeneralCK CKLaneN1 CKLaneE.FP GeneralCK.SmallMeanPhiCutoff

/-- the stationarity-free statement of the numeric cover -/
def CoverStmt : Prop :=
  ∀ a z y : ℝ, 1 / 131072 ≤ a → a < 1 / 100 → 0 < z → z < 1 → 0 < y → a + y < 1 / 2 →
    y ≤ (H a + H (a + z * y)) / 20 → 1 / 10000 < 2 * a + y → a + z * y < 1 / 100 →
    0 ≤ CKLaneM07.CE.gapLB (H a) (H (a + z * y)) (a + y)

end CKLaneN1.R3


