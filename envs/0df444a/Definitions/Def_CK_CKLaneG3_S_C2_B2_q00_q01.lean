-- Prove2me | Definitions.Def_CK_CKLaneG3_S_C2_B2_q00_q01
-- name    : CK_CKLaneG3_S_C2_B2_q00_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T11:42:05.394272+00:00
-- url     : https://prove2.me/theorems/4d7c4c33-849b-4251-b2a4-8386f341cfe8
-- title:
--   Courtade–Kumar proof module `CKLaneG3.S.C2.B2 (piece 1 of 4) (piece 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.S.C2.B2 (piece 1 of 4) (piece 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.S.C2.B2 (piece 1 of 4) (piece 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.S.C2.B2 (piece 1 of 4) (piece 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/S/C2/B2 (piece 1 of 4) (piece 2 of 3).lean)

import Definitions.Def_CK_CKLaneG3_S_C2_B2_q00_q00

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneG3.S.C2.B2
open CKLaneD CKLaneG3
theorem SH_ok : ∀ S ∈ SH, ∀ x ∈ S, SLeafOK (sBox (id x)) :=
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0046.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0047.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0048.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0049.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0050.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0051.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0052.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0053.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0054.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0055.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0056.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0057.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0058.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0059.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0060.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0061.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0062.leaves_sem x hx))
   shards_nil)))))))))))))))))

end CKLaneG3.S.C2.B2


