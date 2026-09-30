-- Prove2me | Definitions.Def_CK_CKLaneE_SRectF
-- name    : CK_CKLaneE_SRectF
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T05:49:45.362819+00:00
-- url     : https://prove2.me/theorems/df5a57b4-e49d-4098-8f39-7bbad13c57d8
-- title:
--   Courtade–Kumar proof module `CKLaneE.SRectF` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneE.SRectF` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneE.SRectF` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneE.SRectF (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneE/SRectF.lean)

import Definitions.Def_CK_CKLaneE_SRectC

-- ===== source module CKLaneE.SRectF =====
section

/-!
# Lane E: batched archived-leaf families per certified rectangle

`family_of_all`: a certified rectangle `RectOK X t0` and one kernel-checked Boolean
`L.all (fun p => fitsC (sBoxL p) X t0)` give `LeafS (sBoxL p)` for every path `p ∈ L`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneE.S

theorem family_of_all {X : SRect} {t0 : ℚ} (hR : RectOK X t0) (L : List (List ℕ))
    (h : L.all (fun p => fitsC (sBoxL p) X t0) = true) : ∀ p ∈ L, LeafS (sBoxL p) := by
  intro p hp
  have := List.all_eq_true.mp h p hp
  exact leafS_of_rectC (sBoxL p) hR this

end CKLaneE.S

#print axioms CKLaneE.S.family_of_all

end


