-- Prove2me | Definitions.Def_CK_CKLaneM07_CE_R3Glue
-- name    : CK_CKLaneM07_CE_R3Glue
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T12:46:13.946972+00:00
-- url     : https://prove2.me/theorems/6afddce9-f462-44f8-b6ea-6cd5d6f97b20
-- title:
--   Courtade–Kumar proof module `CKLaneM07.CE.R3Glue` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM07.CE.R3Glue` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM07.CE.R3Glue` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM07.CE.R3Glue (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM07/CE/R3Glue.lean)

import Definitions.Def_CK_CKLaneN1_R3Leaf

-- ===== source module CKLaneM07.CE.R3Glue =====
section

/-!
# Lane M07 / CE-stat row 3: gluing lemmas for the numeric cover

`sem_node`: `Sem` of the two halves of a box along any axis gives `Sem` of the box (N1 `B3.mem_step`);
`sem_eq`: transport along an equality of boxes (used with `decide` to match a generated sub-root literal).
The octave modules compose these along the generated skeleton, so the proof term has the depth of the
skeleton, not the number of shards.
-/

set_option autoImplicit false

namespace CKLaneM07.CE.R3Glue

open CKLaneN1

theorem sem_node {B : B3} (ax : ℕ) (h0 : CKLaneN1.R3.Sem (B.step (2 * ax)))
    (h1 : CKLaneN1.R3.Sem (B.step (2 * ax + 1))) : CKLaneN1.R3.Sem B := by
  intro a z y hm
  rcases B3.mem_step hm ax with h | h
  · exact h0 a z y h
  · exact h1 a z y h

theorem sem_eq {B B' : B3} (h : B = B') (s : CKLaneN1.R3.Sem B') : CKLaneN1.R3.Sem B := h ▸ s

end CKLaneM07.CE.R3Glue

end


