-- Prove2me | Definitions.Def_CK_CKLaneM03_Family_F05_q02
-- name    : CK_CKLaneM03_Family_F05_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T14:18:03.59937+00:00
-- url     : https://prove2.me/theorems/4444f153-7b48-4b23-928a-692d98125b85
-- title:
--   Courtade–Kumar proof module `CKLaneM03.Family.F05 (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM03.Family.F05 (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM03.Family.F05 (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM03.Family.F05 (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM03/Family/F05 (piece 3 of 4).lean)

import Definitions.Def_CK_CKLaneM03_Family_F05_q02_q03

namespace CKLaneM03.EP
open CKLaneM03
namespace P0148
set_option maxRecDepth 200000 in
theorem leaves_sem : ∀ p ∈ leaves, Sem (ssBox p) :=
  sem_forall_cons l_5030001521240341351341350240 (sem_forall_cons l_5030001521240341351341350340 (sem_forall_cons l_5030001521240341351341350341 (sem_forall_cons l_5030001521240341351341351340 (sem_forall_cons l_5030001521241240240240240340 (sem_forall_cons l_5030001521241240240240240341 (sem_forall_cons l_503000152124124024024034024 (sem_forall_cons l_503000152124124024024034034 (sem_forall_cons l_5030001521241240240240340350 (sem_forall_cons l_5030001521241240240240340351 (sem_forall_cons l_5030001521241240240240341240 (sem_forall_cons l_503000152124124024024034134 (sem_forall_cons l_503000152124124024024134034 (sem_forall_cons l_503000152124124024034024024 (sem_forall_cons l_5030001521241240240340240250 (sem_forall_cons l_5030001521241240240340240251 (sem_forall_cons l_503000152124124024034024034 (sem_forall_cons l_503000152124124024034024035 (sem_forall_cons l_503000152124124024034024124 (sem_forall_cons l_5030001521241240240340241250 (sem_forall_cons l_503000152124124024034024134 (sem_forall_cons l_5030001521241240240340241350 (sem_forall_cons l_5030001521241240240340241351 (sem_forall_cons l_50300015212412402403403402 (sem_forall_cons l_50300015212412402403403403 (sem_forall_cons l_503000152124124024034034124 (sem_forall_cons l_503000152124124024034034125 (sem_forall_cons l_50300015212412402403403413 (sem_forall_cons l_5030001521241240240340350240 (sem_forall_cons l_5030001521241240240340350340 (sem_forall_cons l_5030001521241240240340350341 (sem_forall_cons l_5030001521241240240340351340 (sem_forall_cons l_5030001521241240240340351341 (sem_forall_cons l_503000152124124024034124024 (sem_forall_cons l_503000152124124024034124034 (sem_forall_cons l_503000152124124024034124124 (sem_forall_cons l_503000152124124024034124134 (sem_forall_cons l_503000152124124024034134024 (sem_forall_cons l_5030001521241240240341340250 (sem_forall_cons l_5030001521241240240341340251 (sem_forall_cons l_503000152124124024034134034 (sem_forall_cons l_503000152124124024034134035 (sem_forall_cons l_503000152124124024034134124 (sem_forall_cons l_503000152124124024034134134 (sem_forall_cons l_5030001521241240240341341350 (sem_forall_cons l_503000152124124024134024034 (sem_forall_cons l_503000152124124024134034024 (sem_forall_cons l_503000152124124024134034034 (sem_forall_cons l_503000152124124024134034124 (sem_forall_cons l_503000152124124024134034134 (sem_forall_cons l_503000152124124024134134034 (sem_forall_cons l_50300015212412403402402402 (sem_forall_cons l_50300015212412403402402403 (sem_forall_cons l_50300015212412403402402412 (sem_forall_cons l_50300015212412403402402413 (sem_forall_cons l_503000152124124034024025024 (sem_forall_cons l_503000152124124034024025034 (sem_forall_cons l_5030001521241240340240250350 (sem_forall_cons l_5030001521241240340240251240 (sem_forall_cons l_5030001521241240340240251241 (sem_forall_cons l_503000152124124034024025134 (sem_forall_cons l_50300015212412403402403402 (sem_forall_cons l_50300015212412403402403403 (sem_forall_cons l_50300015212412403402403412 (sem_forall_cons l_50300015212412403402403413 (sem_forall_cons l_503000152124124034024035024 (sem_forall_cons l_5030001521241240340240350250 (sem_forall_cons l_5030001521241240340240350251 (sem_forall_cons l_503000152124124034024035034 (sem_forall_cons l_503000152124124034024035035 (sem_forall_cons l_503000152124124034024035124 (sem_forall_cons l_5030001521241240340240351250 (sem_forall_cons l_503000152124124034024035134 (sem_forall_cons l_5030001521241240340240351350 (sem_forall_cons l_5030001521241240340240351351 (sem_forall_cons l_50300015212412403402412402 (sem_forall_cons l_50300015212412403402412403 (sem_forall_cons l_503000152124124034024124124 (sem_forall_cons l_503000152124124034024124125 (sem_forall_cons l_50300015212412403402412413 (sem_forall_cons l_5030001521241240340241250240 (sem_forall_cons l_5030001521241240340241250340 (sem_forall_cons l_5030001521241240340241250341 (sem_forall_cons l_5030001521241240340241251340 (sem_forall_cons l_50300015212412403402413402 (sem_forall_cons l_50300015212412403402413403 (sem_forall_cons l_50300015212412403402413412 (sem_forall_cons l_50300015212412403402413413 (sem_forall_cons l_503000152124124034024135024 (sem_forall_cons l_503000152124124034024135034 (sem_forall_cons l_5030001521241240340241350350 (sem_forall_cons l_5030001521241240340241351240 (sem_forall_cons l_5030001521241240340241351241 (sem_forall_cons l_503000152124124034024135134 sem_forall_nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end P0148

namespace P0149

end P0149
end CKLaneM03.EP


