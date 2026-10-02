-- Prove2me | Definitions.Def_CK_CKLaneC3_CompactTreeA_part00_q00_q00_q00
-- name    : CK_CKLaneC3_CompactTreeA_part00_q00_q00_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T20:20:34.79317+00:00
-- url     : https://prove2.me/theorems/f3d83868-2e61-4acd-93c9-246d2ea683b0
-- title:
--   Courtade–Kumar proof module `CKLaneC3.CompactTreeA (part 1 of 2) (piece 1 of 3) (piece 1 of 3) (piece 1 of 5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC3.CompactTreeA (part 1 of 2) (piece 1 of 3) (piece 1 of 3) (piece 1 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC3.CompactTreeA (part 1 of 2) (piece 1 of 3) (piece 1 of 3) (piece 1 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC3.CompactTreeA (part 1 of 2) (piece 1 of 3) (piece 1 of 3) (piece 1 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC3/CompactTreeA (part 1 of 2) (piece 1 of 3) (piece 1 of 3) (piece 1 of 5).lean)

import Definitions.Def_CK_CKLaneC3_CompactTreeA_part00_q00_q00_q00_t15




/-! Lane C3 compact cover tree, part A (generated): the split tree, its validity, and the
exact leaf list as literal slices (traversal order, 120 leaves per slice).  No batch imports. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactTreeA
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisRationalTreeBridgeKernel
open E8TAxisGeneratedGeometry (RatRect)

set_option maxRecDepth 100000 in
def tree : Tree := .splitS (8 / 25 : ℚ) (.splitS (2 / 25 : ℚ) (.splitS (1 / 25 : ℚ) (.splitT (8 / 25 : ℚ) (.splitT (2 / 25 : ℚ) (.splitT (1 / 25 : ℚ) .leaf (.splitS (3 / 100 : ℚ) tree_sub_000 tree_sub_001)) (.splitT (4 / 25 : ℚ) (.splitS (3 / 100 : ℚ) tree_sub_002 tree_sub_003) (.splitS (3 / 100 : ℚ) tree_sub_004 tree_sub_005))) (.splitT (32 / 25 : ℚ) (.splitT (16 / 25 : ℚ) (.splitS (3 / 100 : ℚ) tree_sub_006 tree_sub_007) (.splitS (3 / 100 : ℚ) tree_sub_008 tree_sub_009)) (.splitT (64 / 25 : ℚ) (.splitS (3 / 100 : ℚ) tree_sub_010 tree_sub_011) (.splitT (128 / 25 : ℚ) (.splitS (3 / 100 : ℚ) (.splitT (96 / 25 : ℚ) (.splitS (1 / 40 : ℚ) tree_sub_012 tree_sub_013) tree_sub_014) tree_sub_015) (.splitT (214 / 25 : ℚ) (.splitS (3 / 100 : ℚ) (.splitT (171 / 25 : ℚ) (.splitS (1 / 40 : ℚ) tree_sub_016 tree_sub_017) tree_sub_018) tree_sub_019) (.splitS (3 / 100 : ℚ) (.splitS (1 / 40 : ℚ) (.splitT (257 / 25 : ℚ) tree_sub_020 tree_sub_021) tree_sub_022) (.splitT (257 / 25 : ℚ) tree_sub_023 tree_sub_024))))))) (.splitT (8 / 25 : ℚ) (.splitT (2 / 25 : ℚ) (.splitT (1 / 25 : ℚ) tree_sub_025 tree_sub_026) (.splitT (4 / 25 : ℚ) tree_sub_027 tree_sub_028)) (.splitT (32 / 25 : ℚ) (.splitT (16 / 25 : ℚ) tree_sub_029 tree_sub_030) (.splitT (64 / 25 : ℚ) (.splitS (3 / 50 : ℚ) tree_sub_031 tree_sub_032) (.splitT (128 / 25 : ℚ) (.splitS (3 / 50 : ℚ) tree_sub_033 tree_sub_034) (.splitT (214 / 25 : ℚ) (.splitS (3 / 50 : ℚ) (.splitT (171 / 25 : ℚ) tree_sub_035 tree_sub_036) tree_sub_037) (.splitS (3 / 50 : ℚ) (.splitS (1 / 20 : ℚ) (.splitT (257 / 25 : ℚ) tree_sub_038 tree_sub_039) tree_sub_040) (.splitT (257 / 25 : ℚ) tree_sub_041 tree_sub_042)))))))) (.splitS (4 / 25 : ℚ) (.splitT (8 / 25 : ℚ) (.splitT (2 / 25 : ℚ) (.splitT (1 / 25 : ℚ) tree_sub_043 tree_sub_044) tree_sub_045) (.splitT (32 / 25 : ℚ) tree_sub_046 (.splitT (64 / 25 : ℚ) tree_sub_047 (.splitT (128 / 25 : ℚ) tree_sub_048 (.splitT (214 / 25 : ℚ) (.splitS (3 / 25 : ℚ) tree_sub_049 tree_sub_050) (.splitS (3 / 25 : ℚ) (.splitS (1 / 10 : ℚ) tree_sub_051 tree_sub_052) tree_sub_053)))))) (.splitT (8 / 25 : ℚ) (.splitT (2 / 25 : ℚ) (.splitT (1 / 25 : ℚ) tree_sub_054 tree_sub_055) tree_sub_056) (.splitT (32 / 25 : ℚ) tree_sub_057 (.splitT (64 / 25 : ℚ) tree_sub_058 (.splitT (128 / 25 : ℚ) tree_sub_059 (.splitT (214 / 25 : ℚ) tree_sub_060 tree_sub_061))))))) (.splitS (32 / 25 : ℚ) (.splitS (16 / 25 : ℚ) (.splitT (8 / 25 : ℚ) (.splitT (2 / 25 : ℚ) tree_sub_062 tree_sub_063) (.splitT (32 / 25 : ℚ) tree_sub_064 (.splitT (64 / 25 : ℚ) tree_sub_065 (.splitT (128 / 25 : ℚ) tree_sub_066 (.splitT (214 / 25 : ℚ) tree_sub_067 tree_sub_068))))) (.splitT (8 / 25 : ℚ) (.splitT (2 / 25 : ℚ) tree_sub_069 tree_sub_070) (.splitT (32 / 25 : ℚ) tree_sub_071 (.splitT (64 / 25 : ℚ) tree_sub_072 (.splitT (128 / 25 : ℚ) tree_sub_073 (.splitT (214 / 25 : ℚ) tree_sub_074 tree_sub_075)))))) (.splitS (64 / 25 : ℚ) (.splitT (8 / 25 : ℚ) (.splitT (2 / 25 : ℚ) tree_sub_076 tree_sub_077) (.splitT (32 / 25 : ℚ) tree_sub_078 (.splitT (64 / 25 : ℚ) tree_sub_079 (.splitT (128 / 25 : ℚ) tree_sub_080 (.splitT (214 / 25 : ℚ) tree_sub_081 tree_sub_082))))) (.splitT (8 / 25 : ℚ) tree_sub_083 tree_sub_084)))

end CKLaneC3.CompactTreeA


