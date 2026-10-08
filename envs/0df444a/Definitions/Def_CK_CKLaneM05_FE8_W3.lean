-- Prove2me | Definitions.Def_CK_CKLaneM05_FE8_W3
-- name    : CK_CKLaneM05_FE8_W3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T08:13:59.982984+00:00
-- url     : https://prove2.me/theorems/77e50815-182d-43ea-812a-0582d0e9dd29
-- title:
--   Courtade–Kumar proof module `CKLaneM05.FE8.W3` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM05.FE8.W3` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM05.FE8.W3` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM05.FE8.W3 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM05/FE8/W3.lean)

import Definitions.Def_CK_CKLaneM05_FE8_EAdapt
import Definitions.Def_CK_CKLaneM05_FE8_SPlane
import Definitions.Def_CK_CKLaneM05_FE8_W1

-- ===== source module CKLaneM05.FE8.W3 =====
section

/-!
# Lane M05 / FE8: certificate type v3 = v2 (outside, cap, parent, plane, Lane E kernels) + shifted plane

`W3.check_sound : W3.check B w = true → LeafOK B`, no other hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM05.FE8

/-- FE8 certificate, version 3. -/
inductive W3 where
  | old (w : W2)
  | sp (c : SC)
  deriving Repr

def W3.check (B : CKLaneD.Box) : W3 → Bool
  | .old w => W2.check B w
  | .sp c => splaneCheck B c

theorem W3.check_sound : ∀ (B : CKLaneD.Box) (w : W3), W3.check B w = true → LeafOK B
  | B, .old w, h => W2.check_sound B w h
  | _, .sp _, h => leafOK_of_splaneCheck h

end CKLaneM05.FE8

#check @CKLaneM05.FE8.W3.check_sound
#print axioms CKLaneM05.FE8.W3.check_sound

end


