-- Prove2me | Definitions.Def_CK_CKLaneM10_Leaves_q00
-- name    : CK_CKLaneM10_Leaves_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T01:31:30.761006+00:00
-- url     : https://prove2.me/theorems/6e98a508-45c6-44fa-97d9-e41545d3772c
-- title:
--   Courtade–Kumar proof module `CKLaneM10.Leaves (piece 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM10.Leaves (piece 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM10.Leaves (piece 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM10.Leaves (piece 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM10/Leaves (piece 1 of 3).lean)

import Definitions.Def_CK_CKLaneM10_Leaves_q00_q01

namespace CKLaneM10.Leaves
open CKLaneD CKLaneM10
theorem allLeaves_sem : ∀ x ∈ allLeaves, SemUVT (uvtBox x.1) :=
  sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (Fleet.S0000.sem) Fleet.S0001.sem) Fleet.S0002.sem) Fleet.S0003.sem) Fleet.S0004.sem) Fleet.S0005.sem) Fleet.S0006.sem) Fleet.S0007.sem) Fleet.S0008.sem) Fleet.S0009.sem) Fleet.S0010.sem) Fleet.S0011.sem) Fleet.S0012.sem) Fleet.S0013.sem) Fleet.S0014.sem) Fleet.S0015.sem) Fleet.S0016.sem) Fleet.S0017.sem) Fleet.S0018.sem) Fleet.S0019.sem) Fleet.S0020.sem) Fleet.S0021.sem) Fleet.S0022.sem) Fleet.S0023.sem) Fleet.S0024.sem) Fleet.S0025.sem) Fleet.S0026.sem) Fleet.S0027.sem) Fleet.S0028.sem) Fleet.S0029.sem) Fleet.S0030.sem) Fleet.S0031.sem) Fleet.S0032.sem) Fleet.S0033.sem) Fleet.S0034.sem) Fleet.S0035.sem) Fleet.S0036.sem) Fleet.S0037.sem) Fleet.S0038.sem) Fleet.S0039.sem) Fleet.S0040.sem) Fleet.S0041.sem) Fleet.S0042.sem) Fleet.S0043.sem) Fleet.S0044.sem) Fleet.S0045.sem) Fleet.S0046.sem) Fleet.S0047.sem) Fleet.S0048.sem) Fleet.S0049.sem) Fleet.S0050.sem) Fleet.S0051.sem) Fleet.S0052.sem) Fleet.S0053.sem) Fleet.S0054.sem) Fleet.S0055.sem) Fleet.S0056.sem) Fleet.S0057.sem) Fleet.S0058.sem) Fleet.S0059.sem) Fleet.S0060.sem) Fleet.S0061.sem) Fleet.S0062.sem) Fleet.S0063.sem) Fleet.S0064.sem) Fleet.S0065.sem) Fleet.S0066.sem) Fleet.S0067.sem) Fleet.S0068.sem) Fleet.S0069.sem) Fleet.S0070.sem) Fleet.S0071.sem) Fleet.S0072.sem) Fleet.S0073.sem) Fleet.S0074.sem) Fleet.S0075.sem) Fleet.S0076.sem) Fleet.S0077.sem

end CKLaneM10.Leaves


