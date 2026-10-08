-- Prove2me | Definitions.Def_CK_CKLaneM03_Family_F02_q00_q01_q00_q00
-- name    : CK_CKLaneM03_Family_F02_q00_q01_q00_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T18:34:10.520745+00:00
-- url     : https://prove2.me/theorems/f22fef1f-25b7-47a4-b3cf-f03747ce6ed9
-- title:
--   Courtade–Kumar proof module `CKLaneM03.Family.F02 (piece 1 of 4) (piece 2 of 4) (piece 1 of 3) (piece 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM03.Family.F02 (piece 1 of 4) (piece 2 of 4) (piece 1 of 3) (piece 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM03.Family.F02 (piece 1 of 4) (piece 2 of 4) (piece 1 of 3) (piece 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM03.Family.F02 (piece 1 of 4) (piece 2 of 4) (piece 1 of 3) (piece 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM03/Family/F02 (piece 1 of 4) (piece 2 of 4) (piece 1 of 3) (piece 1 of 3).lean)

import Definitions.Def_CK_CKLaneM03_Family_F02_q00_q00



namespace CKLaneM03.EP
open CKLaneM03
namespace P0050
set_option maxRecDepth 200000 in
theorem leaves_sem : ∀ p ∈ leaves, Sem (ssBox p) :=
  sem_forall_cons l_502020300431512503413413402 (sem_forall_cons l_502020300431512503413413403 (sem_forall_cons l_502020300431512503413413412 (sem_forall_cons l_502020300431512503413413413 (sem_forall_cons l_502020300431512513402403403 (sem_forall_cons l_5020203004315125134024034124 (sem_forall_cons l_5020203004315125134024034134 (sem_forall_cons l_5020203004315125134024124024 (sem_forall_cons l_5020203004315125134024124034 (sem_forall_cons l_5020203004315125134024124134 (sem_forall_cons l_5020203004315125134024134024 (sem_forall_cons l_5020203004315125134024134034 (sem_forall_cons l_5020203004315125134024134124 (sem_forall_cons l_5020203004315125134024134134 (sem_forall_cons l_502020300431512513403402402 (sem_forall_cons l_502020300431512513403402403 (sem_forall_cons l_502020300431512513403402412 (sem_forall_cons l_502020300431512513403402413 (sem_forall_cons l_502020300431512513403403402 (sem_forall_cons l_502020300431512513403403403 (sem_forall_cons l_502020300431512513403403412 (sem_forall_cons l_502020300431512513403403413 (sem_forall_cons l_5020203004315125134034035134 (sem_forall_cons l_5020203004315125134034124024 (sem_forall_cons l_5020203004315125134034124025 (sem_forall_cons l_502020300431512513403412403 (sem_forall_cons l_5020203004315125134034124124 (sem_forall_cons l_5020203004315125134034124134 (sem_forall_cons l_5020203004315125134034124135 (sem_forall_cons l_502020300431512513403413402 (sem_forall_cons l_502020300431512513403413403 (sem_forall_cons l_502020300431512513403413412 (sem_forall_cons l_502020300431512513403413413 (sem_forall_cons l_5020203004315125134124034024 (sem_forall_cons l_5020203004315125134124034034 (sem_forall_cons l_5020203004315125134124034134 (sem_forall_cons l_50202030043151251341241340341 (sem_forall_cons l_50202030043151251341241341340 (sem_forall_cons l_50202030043151251341241341341 (sem_forall_cons l_5020203004315125134134024024 (sem_forall_cons l_5020203004315125134134024034 (sem_forall_cons l_5020203004315125134134024124 (sem_forall_cons l_5020203004315125134134024134 (sem_forall_cons l_5020203004315125134134034024 (sem_forall_cons l_5020203004315125134134034025 (sem_forall_cons l_502020300431512513413403403 (sem_forall_cons l_5020203004315125134134034124 (sem_forall_cons l_50202030043151251341340341251 (sem_forall_cons l_5020203004315125134134034134 (sem_forall_cons l_5020203004315125134134034135 (sem_forall_cons l_5020203004315125134134124024 (sem_forall_cons l_5020203004315125134134124034 (sem_forall_cons l_50202030043151251341341241240 (sem_forall_cons l_50202030043151251341341241241 (sem_forall_cons l_5020203004315125134134124134 (sem_forall_cons l_5020203004315125134134134024 (sem_forall_cons l_50202030043151251341341340250 (sem_forall_cons l_50202030043151251341341340251 (sem_forall_cons l_5020203004315125134134134034 (sem_forall_cons l_50202030043151251341341340350 (sem_forall_cons l_50202030043151251341341340351 (sem_forall_cons l_5020203004315125134134134124 (sem_forall_cons l_50202030043151251341341341250 (sem_forall_cons l_5020203004315125134134134134 (sem_forall_cons l_50202030043151251341341341350 (sem_forall_cons l_50202030043151251341341341351 sem_forall_nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end P0050

namespace P0051

end P0051
end CKLaneM03.EP


