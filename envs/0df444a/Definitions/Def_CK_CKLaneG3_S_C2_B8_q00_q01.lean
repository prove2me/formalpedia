-- Prove2me | Definitions.Def_CK_CKLaneG3_S_C2_B8_q00_q01
-- name    : CK_CKLaneG3_S_C2_B8_q00_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-08T00:01:47.762664+00:00
-- url     : https://prove2.me/theorems/a524c770-c49c-4f66-a40a-ba7fec9be767
-- title:
--   Courtade–Kumar proof module `CKLaneG3.S.C2.B8 (piece 1 of 4) (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.S.C2.B8 (piece 1 of 4) (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.S.C2.B8 (piece 1 of 4) (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.S.C2.B8 (piece 1 of 4) (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/S/C2/B8 (piece 1 of 4) (piece 2 of 4).lean)

import Definitions.Def_CK_CKLaneG3_S_C2_B8_q00_q00

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneG3.S.C2.B8
open CKLaneD CKLaneG3
theorem SH_ok : ∀ S ∈ SH, ∀ x ∈ S, SLeafOK (sBox (id x)) :=
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0240.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0241.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0242.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0243.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0244.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0245.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0246.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0247.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0248.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0249.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0250.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0251.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0252.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0253.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0254.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0255.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0256.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0257.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0258.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0259.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0260.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0261.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0262.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0263.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0264.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0265.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0266.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0267.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0268.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0269.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0270.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0271.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0272.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0273.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0274.leaves_sem x hx))
  (shards_cons (fun x hx => CKLaneM03.sLeafOK_of_sem (CKLaneM03.EP.P0275.leaves_sem x hx))
   shards_nil))))))))))))))))))))))))))))))))))))

end CKLaneG3.S.C2.B8


