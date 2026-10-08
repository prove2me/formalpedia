-- Prove2me | Definitions.Def_CK_CKLaneN1_EdgeFinal_q00
-- name    : CK_CKLaneN1_EdgeFinal_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T16:38:56.677391+00:00
-- url     : https://prove2.me/theorems/d209a405-38f2-407a-b555-26cc11024372
-- title:
--   Courtade–Kumar proof module `CKLaneN1.EdgeFinal (piece 1 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1.EdgeFinal (piece 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1.EdgeFinal (piece 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1.EdgeFinal (piece 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1/EdgeFinal (piece 1 of 4).lean)

import Definitions.Def_CK_CKLaneN1_EdgeShard_E00
import Definitions.Def_CK_CKLaneN1_EdgeShard_E01
import Definitions.Def_CK_CKLaneN1_EdgeShard_E02
import Definitions.Def_CK_CKLaneN1_EdgeShard_E03
import Definitions.Def_CK_CKLaneN1_EdgeShard_E04
import Definitions.Def_CK_CKLaneN1_EdgeShard_E05
import Definitions.Def_CK_CKLaneN1_EdgeShard_E06
import Definitions.Def_CK_CKLaneN1_EdgeShard_E07
import Definitions.Def_CK_CKLaneN1_EdgeShard_E08
import Definitions.Def_CK_CKLaneN1_EdgeShard_E09
import Definitions.Def_CK_CKLaneN1_EdgeShard_E10
import Definitions.Def_CK_CKLaneN1_EdgeShard_E11
import Definitions.Def_CK_CKLaneN1_EdgeShard_E12
import Definitions.Def_CK_CKLaneN1_EdgeShard_E13
import Definitions.Def_CK_CKLaneN1_EdgeShard_E14
import Definitions.Def_CK_CKLaneN1_EdgeShard_E15
import Definitions.Def_CK_CKLaneN1_EdgeShard_E16
import Definitions.Def_CK_CKLaneN1_EdgeShard_E17
import Definitions.Def_CK_CKLaneN1_EdgeShard_E18
import Definitions.Def_CK_CKLaneN1_EdgeShard_E19
import Definitions.Def_CK_CKLaneN1_EdgeShard_E20
import Definitions.Def_CK_CKLaneN1_EdgeShard_E21
import Definitions.Def_CK_CKLaneN1_EdgeShard_E22
import Definitions.Def_CK_CKLaneN1_EdgeShard_E23
import Definitions.Def_CK_CKLaneN1_EdgeShard_E24
import Definitions.Def_CK_CKLaneN1_EdgeShard_E25
import Definitions.Def_CK_CKLaneN1_EdgeShard_E26
import Definitions.Def_CK_CKLaneN1_EdgeShard_E27
import Definitions.Def_CK_CKLaneN1_EdgeShard_E28
import Definitions.Def_CK_CKLaneN1_EdgeShard_E29
import Definitions.Def_CK_CKLaneN1_EdgeShard_E30
import Definitions.Def_CK_CKLaneN1_EdgeShard_E31
import Definitions.Def_CK_CKLaneN1_EdgeShard_E32
import Definitions.Def_CK_CKLaneN1_EdgeShard_E33
import Definitions.Def_CK_CKLaneN1_EdgeShard_E34
import Definitions.Def_CK_CKLaneN1_EdgeShard_E35
import Definitions.Def_CK_CKLaneN1_EdgeShard_E36
import Definitions.Def_CK_CKLaneN1_EdgeShard_E37
import Definitions.Def_CK_CKLaneN1_EdgeShard_E38
import Definitions.Def_CK_CKLaneN1_EdgeShard_E39
import Definitions.Def_CK_CKLaneN1_EdgeShard_E40
import Definitions.Def_CK_CKLaneN1_EdgeShard_E41
import Definitions.Def_CK_CKLaneN1_EdgeShard_E42
import Definitions.Def_CK_CKLaneN1_EdgeShard_E43
import Definitions.Def_CK_CKLaneN1_EdgeShard_E44
import Definitions.Def_CK_CKLaneN1_EdgeShard_E45
import Definitions.Def_CK_CKLaneN1_EdgeShard_E46
import Definitions.Def_CK_CKLaneN1_EdgeShard_E47
import Definitions.Def_CK_CKLaneN1_EdgeShard_E48
import Definitions.Def_CK_CKLaneN1_EdgeShard_E49
import Definitions.Def_CK_CKLaneN1_EdgeShard_E50
import Definitions.Def_CK_CKLaneN1_EdgeShard_E51
import Definitions.Def_CK_CKLaneN1_EdgeShard_E52
import Definitions.Def_CK_CKLaneN1_EdgeShard_E53
import Definitions.Def_CK_CKLaneN1_EdgeShard_E54
import Definitions.Def_CK_CKLaneN1_EdgeShard_E55
import Definitions.Def_CK_CKLaneN1_EdgeShard_E56
import Definitions.Def_CK_CKLaneN1_EdgeShard_E57
import Definitions.Def_CK_CKLaneN1_EdgeShard_E58
import Definitions.Def_CK_CKLaneN1_EdgeShard_E59
import Definitions.Def_CK_CKLaneN1_EdgeShard_E60
import Definitions.Def_CK_CKLaneN1_Chunks
import Definitions.Def_CK_CKLaneN1_EdgeCorner



set_option autoImplicit false

/-!
# Lane N1: capFibers cutoff edge (`leftEdge`) — CLOSED from the kernel-checked box tree

`edgeTree_ok`: all 3006 leaves of `edgeTree` pass `edgeLeafOK` (fleet shards `EdgeShard.E00..E60`,
`decide +kernel`).  With `edgeOK_sound` (certified boxes) and `corner_pos` (the corner box) this
gives positivity of the cutoff-edge value on the whole strict edge `0 < a < b < S - a`,
`S = retainedCutoff = 1/10000`.
-/

namespace CKLaneN1.Edge

open GeneralCK SmallMeanPhiCutoff

theorem edgeTree_length : edgeTree.leaves.length = 3006 := by decide +kernel

end CKLaneN1.Edge


