-- Prove2me | Definitions.Def_CK_CKLaneP_SeamFinal_q00
-- name    : CK_CKLaneP_SeamFinal_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T19:53:46.327525+00:00
-- url     : https://prove2.me/theorems/8b444e7b-e266-4c5f-9e0d-dfb90920e656
-- title:
--   Courtade–Kumar proof module `CKLaneP.SeamFinal (piece 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.SeamFinal (piece 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.SeamFinal (piece 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.SeamFinal (piece 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/SeamFinal (piece 1 of 3).lean)

import Definitions.Def_CK_CKLaneP_SeamTree
import Definitions.Def_CK_CKLaneP_SeamTCheck
import Definitions.Def_CK_GeneralCK_SmallMeanPhiRetainedCutoff


/-
Lane P — seam assembly pieces:

* `tlistOK` / `tlistOK_sound` : a list of T-cells covering `κ = H p/H q ∈ [0, 1]` gives the
  small-scale lemma `∀ p q, 0 < p → p < q → q ≤ qT → SeamAt p q`.
* `seam_exclusion_of_box` : the root box `SeamBox 0 (S/2) 0 2` implies
  `StrictSeamMinimizerExclusion (1/10000)` (the seam field, up to unfolding `retainedCutoff`).
Both are conditional on their hypotheses; the certificates discharge them.
-/

set_option autoImplicit false

namespace CKLaneP

open GeneralCK GeneralCK.Certificates.Mixed Set

/-- Consecutive T-cells: the first starts at `k`, each next starts where the previous ends,
the last ends at `≥ 1`; all share `qT`. -/
def tlistOK (qT : ℚ) : ℚ → List (ℕ × TCell) → Bool
  | k, [] => decide (1 ≤ k)
  | k, (kind, c) :: rest => (decide (c.qT = qT ∧ c.k0 = k) && tcheck kind c) && tlistOK qT c.k1 rest

end CKLaneP


