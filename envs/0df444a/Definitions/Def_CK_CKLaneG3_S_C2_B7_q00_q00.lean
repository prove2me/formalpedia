-- Prove2me | Definitions.Def_CK_CKLaneG3_S_C2_B7_q00_q00
-- name    : CK_CKLaneG3_S_C2_B7_q00_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T14:56:06.00564+00:00
-- url     : https://prove2.me/theorems/3a8b112e-2bb5-4276-82ae-8cc409d89bc7
-- title:
--   Courtade–Kumar proof module `CKLaneG3.S.C2.B7 (piece 1 of 4) (piece 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.S.C2.B7 (piece 1 of 4) (piece 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.S.C2.B7 (piece 1 of 4) (piece 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.S.C2.B7 (piece 1 of 4) (piece 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/S/C2/B7 (piece 1 of 4) (piece 1 of 3).lean)

import Definitions.Def_CK_CKLaneG3_S_C2_B7_q00_q00_q00

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneG3.S.C2.B7
open CKLaneD CKLaneG3
theorem SH_ok : ∀ S ∈ SH, ∀ x ∈ S, SLeafOK (sBox (id x)) :=
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0197.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0198.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0199.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0200.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0201.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0202.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0203.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0204.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0205.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0206.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0207.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0208.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0209.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0210.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0211.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0212.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0213.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0214.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0215.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0216.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0217.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0218.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0219.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0220.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0221.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0222.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0223.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0224.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0225.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0226.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0227.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0228.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0229.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0230.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0231.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0232.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0233.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0234.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0235.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0236.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0237.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0238.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0239.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0240.leaves_sem x hx))
   shards_nil))))))))))))))))))))))))))))))))))))))))))))

end CKLaneG3.S.C2.B7


