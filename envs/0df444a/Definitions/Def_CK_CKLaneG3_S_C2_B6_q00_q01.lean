-- Prove2me | Definitions.Def_CK_CKLaneG3_S_C2_B6_q00_q01
-- name    : CK_CKLaneG3_S_C2_B6_q00_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T10:42:45.506731+00:00
-- url     : https://prove2.me/theorems/6c63c32b-89ae-4e04-a665-f4160242030b
-- title:
--   Courtade–Kumar proof module `CKLaneG3.S.C2.B6 (piece 1 of 4) (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.S.C2.B6 (piece 1 of 4) (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.S.C2.B6 (piece 1 of 4) (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.S.C2.B6 (piece 1 of 4) (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/S/C2/B6 (piece 1 of 4) (piece 2 of 4).lean)

import Definitions.Def_CK_CKLaneG3_S_C2_B6_q00_q00

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneG3.S.C2.B6
open CKLaneD CKLaneG3
theorem SH_ok : ∀ S ∈ SH, ∀ x ∈ S, SLeafOK (sBox (id x)) :=
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0157.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0158.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0159.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0160.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0161.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0162.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0163.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0164.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0165.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0166.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0167.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0168.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0169.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0170.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0171.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0172.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0173.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0174.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0175.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0176.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0177.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0178.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0179.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0180.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0181.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0182.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0183.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0184.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0185.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0186.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0187.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0188.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0189.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0190.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0191.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0192.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0193.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0194.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0195.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0196.leaves_sem x hx))
   shards_nil))))))))))))))))))))))))))))))))))))))))

end CKLaneG3.S.C2.B6


