-- Prove2me | Definitions.Def_CK_CKLaneM10_Leaves_q00_q01
-- name    : CK_CKLaneM10_Leaves_q00_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T23:34:17.942391+00:00
-- url     : https://prove2.me/theorems/07e84276-69b2-46be-b9ee-8b6566df330e
-- title:
--   Courtade–Kumar proof module `CKLaneM10.Leaves (piece 1 of 3) (piece 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM10.Leaves (piece 1 of 3) (piece 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM10.Leaves (piece 1 of 3) (piece 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM10.Leaves (piece 1 of 3) (piece 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM10/Leaves (piece 1 of 3) (piece 2 of 3).lean)

import Definitions.Def_CK_CKLaneM10_Leaves_q00_q00

namespace CKLaneM10.Leaves
open CKLaneD CKLaneM10
/-- All shard witnesses, in archive (left-first DFS) order. -/
noncomputable def allLeaves : List (List ℕ × FSWitness) :=
    Fleet.S0000.leaves ++
    Fleet.S0001.leaves ++
    Fleet.S0002.leaves ++
    Fleet.S0003.leaves ++
    Fleet.S0004.leaves ++
    Fleet.S0005.leaves ++
    Fleet.S0006.leaves ++
    Fleet.S0007.leaves ++
    Fleet.S0008.leaves ++
    Fleet.S0009.leaves ++
    Fleet.S0010.leaves ++
    Fleet.S0011.leaves ++
    Fleet.S0012.leaves ++
    Fleet.S0013.leaves ++
    Fleet.S0014.leaves ++
    Fleet.S0015.leaves ++
    Fleet.S0016.leaves ++
    Fleet.S0017.leaves ++
    Fleet.S0018.leaves ++
    Fleet.S0019.leaves ++
    Fleet.S0020.leaves ++
    Fleet.S0021.leaves ++
    Fleet.S0022.leaves ++
    Fleet.S0023.leaves ++
    Fleet.S0024.leaves ++
    Fleet.S0025.leaves ++
    Fleet.S0026.leaves ++
    Fleet.S0027.leaves ++
    Fleet.S0028.leaves ++
    Fleet.S0029.leaves ++
    Fleet.S0030.leaves ++
    Fleet.S0031.leaves ++
    Fleet.S0032.leaves ++
    Fleet.S0033.leaves ++
    Fleet.S0034.leaves ++
    Fleet.S0035.leaves ++
    Fleet.S0036.leaves ++
    Fleet.S0037.leaves ++
    Fleet.S0038.leaves ++
    Fleet.S0039.leaves ++
    Fleet.S0040.leaves ++
    Fleet.S0041.leaves ++
    Fleet.S0042.leaves ++
    Fleet.S0043.leaves ++
    Fleet.S0044.leaves ++
    Fleet.S0045.leaves ++
    Fleet.S0046.leaves ++
    Fleet.S0047.leaves ++
    Fleet.S0048.leaves ++
    Fleet.S0049.leaves ++
    Fleet.S0050.leaves ++
    Fleet.S0051.leaves ++
    Fleet.S0052.leaves ++
    Fleet.S0053.leaves ++
    Fleet.S0054.leaves ++
    Fleet.S0055.leaves ++
    Fleet.S0056.leaves ++
    Fleet.S0057.leaves ++
    Fleet.S0058.leaves ++
    Fleet.S0059.leaves ++
    Fleet.S0060.leaves ++
    Fleet.S0061.leaves ++
    Fleet.S0062.leaves ++
    Fleet.S0063.leaves ++
    Fleet.S0064.leaves ++
    Fleet.S0065.leaves ++
    Fleet.S0066.leaves ++
    Fleet.S0067.leaves ++
    Fleet.S0068.leaves ++
    Fleet.S0069.leaves ++
    Fleet.S0070.leaves ++
    Fleet.S0071.leaves ++
    Fleet.S0072.leaves ++
    Fleet.S0073.leaves ++
    Fleet.S0074.leaves ++
    Fleet.S0075.leaves ++
    Fleet.S0076.leaves ++
    Fleet.S0077.leaves

end CKLaneM10.Leaves


