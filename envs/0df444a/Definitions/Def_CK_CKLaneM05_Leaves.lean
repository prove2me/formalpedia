-- Prove2me | Definitions.Def_CK_CKLaneM05_Leaves
-- name    : CK_CKLaneM05_Leaves
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T01:22:58.331087+00:00
-- url     : https://prove2.me/theorems/a355161c-f4a1-4e66-8953-ae0c3af2c5f5
-- title:
--   Courtade–Kumar proof module `CKLaneM05.Leaves` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM05.Leaves` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM05.Leaves` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM05.Leaves (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM05/Leaves.lean)

import Definitions.Def_CK_CKLaneM05_Split
import Definitions.Def_CK_CKLaneM05_SAdapter
import Definitions.Def_CK_CKLaneM05_Fleet_S000__6

-- ===== source module CKLaneM05.Leaves =====
section

/-!
# Lane M05: all 69 archived same-side `parent` leaves (aggregate)

* `parentPaths` : the 69 archived leaf paths owned by `parent` (ADAPT_RESULT.json order);
  `parent_leaves : ∀ p ∈ parentPaths, ParentSem (ssBox p)` from the fleet shard theorems.
* Canonical (S) form (BRIEF §7, `CKLaneG3.SCover`): `parent_sLeafOK : ∀ p ∈ parentPaths,
  CKLaneG3.SLeafOK (CKLaneG3.sBox p)` and `parent_parentS : ∀ p ∈ parentPaths,
  CKLaneG3.ParentS (CKLaneG3.sBox p)` (via `toS_ssBox`, `sLeafOK_of_parentSem`).
* `parentSubtrees` : the 47 maximal archived subtrees all of whose leaves are `parent` leaves;
  `parent_subtrees : ∀ p ∈ parentSubtrees, ParentSem (ssBox p)` (exact halving, `parentSem_split`),
  and the canonical forms `parent_subtrees_sLeafOK`, `parent_subtrees_parentS`.
* Reconciliation with the archive population CSV (`same_side,parent,69`): `parentPaths_length`,
  `parentPaths_nodup`, `parentBoxes` (exact rational boxes).
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace CKLaneM05

/-- The 69 archived `parent` leaf paths (digits), ADAPT_RESULT.json order. -/
def parentPaths : List (List ℕ) :=
  [[4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 0, 2, 0, 2, 0, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 0, 2, 0, 2, 1, 2],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 0, 2, 0, 2, 1, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 0, 2, 0, 3, 0],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 0, 2, 0, 3, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 0, 2, 1, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 0, 3, 0, 0],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 0, 3, 0, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 0, 3, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 1, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 3, 0, 0, 0],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 3, 0, 0, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 3, 0, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 3, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 3, 0, 0, 0, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 3, 0, 0, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 3, 0, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 2, 1, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 2, 0, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 2, 1, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 2, 1, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 5, 2],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 2, 0, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 2, 1, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 2, 1, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 4, 2],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 4, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 5, 2],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 5, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 2, 0, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 2, 1, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 2, 1, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 4, 2],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 4, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 5, 2],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 5, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 2, 0, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 2, 1, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 2, 1, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 4, 2],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 4, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 5, 2],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 5, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 2, 0, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 2, 1, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 4, 2],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 4, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 5, 2],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 5, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 4, 3, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 5, 3, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 4, 3, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 5, 3, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 1, 0, 5, 3]]

theorem parentPaths_length : parentPaths.length = 69 := by decide +kernel

theorem parentPaths_nodup : parentPaths.Nodup := by decide +kernel

/-- The exact rational archive boxes of the 69 leaves (x0, x1, b0, b1, t0, t1). -/
theorem parentBoxes : parentPaths.map ssBox =
    [⟨qq (0) 1, qq (1) 1, qq (1) 32, qq (47) 1024, qq (0) 1, qq (1) 131072⟩,
     ⟨qq (0) 1, qq (1) 1, qq (47) 1024, qq (31) 512, qq (0) 1, qq (1) 131072⟩,
     ⟨qq (1) 1, qq (2) 1, qq (1) 32, qq (47) 1024, qq (0) 1, qq (1) 131072⟩,
     ⟨qq (1) 1, qq (2) 1, qq (47) 1024, qq (31) 512, qq (0) 1, qq (1) 131072⟩,
     ⟨qq (0) 1, qq (1) 1, qq (31) 512, qq (23) 256, qq (0) 1, qq (1) 131072⟩,
     ⟨qq (1) 1, qq (2) 1, qq (31) 512, qq (23) 256, qq (0) 1, qq (1) 131072⟩,
     ⟨qq (2) 1, qq (4) 1, qq (31) 512, qq (23) 256, qq (0) 1, qq (1) 131072⟩,
     ⟨qq (0) 1, qq (1) 1, qq (23) 256, qq (19) 128, qq (0) 1, qq (1) 131072⟩,
     ⟨qq (1) 1, qq (2) 1, qq (23) 256, qq (19) 128, qq (0) 1, qq (1) 131072⟩,
     ⟨qq (2) 1, qq (4) 1, qq (23) 256, qq (19) 128, qq (0) 1, qq (1) 131072⟩,
     ⟨qq (4) 1, qq (8) 1, qq (23) 256, qq (19) 128, qq (0) 1, qq (1) 131072⟩,
     ⟨qq (0) 1, qq (1) 1, qq (19) 128, qq (17) 64, qq (0) 1, qq (1) 131072⟩,
     ⟨qq (1) 1, qq (2) 1, qq (19) 128, qq (17) 64, qq (0) 1, qq (1) 131072⟩,
     ⟨qq (2) 1, qq (4) 1, qq (19) 128, qq (17) 64, qq (0) 1, qq (1) 131072⟩,
     ⟨qq (4) 1, qq (8) 1, qq (19) 128, qq (17) 64, qq (0) 1, qq (1) 131072⟩,
     ⟨qq (1) 1, qq (2) 1, qq (17) 64, qq (1) 2, qq (0) 1, qq (1) 131072⟩,
     ⟨qq (2) 1, qq (4) 1, qq (17) 64, qq (1) 2, qq (0) 1, qq (1) 131072⟩,
     ⟨qq (4) 1, qq (8) 1, qq (17) 64, qq (1) 2, qq (0) 1, qq (1) 131072⟩,
     ⟨qq (8) 1, qq (16) 1, qq (19) 128, qq (17) 64, qq (1) 131072, qq (1) 65536⟩,
     ⟨qq (2) 1, qq (4) 1, qq (17) 64, qq (1) 2, qq (1) 131072, qq (1) 65536⟩,
     ⟨qq (4) 1, qq (8) 1, qq (17) 64, qq (1) 2, qq (1) 131072, qq (1) 65536⟩,
     ⟨qq (8) 1, qq (16) 1, qq (17) 64, qq (1) 2, qq (1) 131072, qq (1) 65536⟩,
     ⟨qq (16) 1, qq (24) 1, qq (19) 128, qq (17) 64, qq (1) 131072, qq (1) 65536⟩,
     ⟨qq (24) 1, qq (32) 1, qq (19) 128, qq (17) 64, qq (1) 131072, qq (1) 65536⟩,
     ⟨qq (8) 1, qq (16) 1, qq (19) 128, qq (17) 64, qq (1) 65536, qq (1) 32768⟩,
     ⟨qq (1) 1, qq (2) 1, qq (17) 64, qq (49) 128, qq (3) 131072, qq (1) 32768⟩,
     ⟨qq (4) 1, qq (8) 1, qq (17) 64, qq (1) 2, qq (1) 65536, qq (1) 32768⟩,
     ⟨qq (8) 1, qq (16) 1, qq (17) 64, qq (1) 2, qq (1) 65536, qq (1) 32768⟩,
     ⟨qq (16) 1, qq (24) 1, qq (19) 128, qq (17) 64, qq (1) 65536, qq (1) 32768⟩,
     ⟨qq (24) 1, qq (32) 1, qq (19) 128, qq (17) 64, qq (1) 65536, qq (1) 32768⟩,
     ⟨qq (16) 1, qq (32) 1, qq (17) 64, qq (1) 2, qq (1) 65536, qq (1) 32768⟩,
     ⟨qq (8) 1, qq (16) 1, qq (19) 128, qq (17) 64, qq (1) 32768, qq (1) 16384⟩,
     ⟨qq (1) 1, qq (2) 1, qq (17) 64, qq (49) 128, qq (1) 32768, qq (3) 65536⟩,
     ⟨qq (1) 1, qq (2) 1, qq (49) 128, qq (1) 2, qq (1) 32768, qq (3) 65536⟩,
     ⟨qq (1) 1, qq (2) 1, qq (17) 64, qq (49) 128, qq (3) 65536, qq (1) 16384⟩,
     ⟨qq (1) 1, qq (2) 1, qq (49) 128, qq (1) 2, qq (3) 65536, qq (1) 16384⟩,
     ⟨qq (4) 1, qq (8) 1, qq (17) 64, qq (1) 2, qq (1) 32768, qq (1) 16384⟩,
     ⟨qq (8) 1, qq (16) 1, qq (17) 64, qq (1) 2, qq (1) 32768, qq (1) 16384⟩,
     ⟨qq (16) 1, qq (24) 1, qq (19) 128, qq (17) 64, qq (1) 32768, qq (1) 16384⟩,
     ⟨qq (24) 1, qq (32) 1, qq (19) 128, qq (17) 64, qq (1) 32768, qq (1) 16384⟩,
     ⟨qq (16) 1, qq (32) 1, qq (17) 64, qq (1) 2, qq (1) 32768, qq (1) 16384⟩,
     ⟨qq (8) 1, qq (16) 1, qq (19) 128, qq (17) 64, qq (1) 16384, qq (1) 8192⟩,
     ⟨qq (1) 1, qq (2) 1, qq (17) 64, qq (49) 128, qq (1) 16384, qq (3) 32768⟩,
     ⟨qq (1) 1, qq (2) 1, qq (49) 128, qq (1) 2, qq (1) 16384, qq (3) 32768⟩,
     ⟨qq (1) 1, qq (2) 1, qq (17) 64, qq (49) 128, qq (3) 32768, qq (1) 8192⟩,
     ⟨qq (1) 1, qq (2) 1, qq (49) 128, qq (1) 2, qq (3) 32768, qq (1) 8192⟩,
     ⟨qq (4) 1, qq (8) 1, qq (17) 64, qq (1) 2, qq (1) 16384, qq (1) 8192⟩,
     ⟨qq (8) 1, qq (16) 1, qq (17) 64, qq (1) 2, qq (1) 16384, qq (1) 8192⟩,
     ⟨qq (16) 1, qq (24) 1, qq (19) 128, qq (17) 64, qq (1) 16384, qq (1) 8192⟩,
     ⟨qq (24) 1, qq (32) 1, qq (19) 128, qq (17) 64, qq (1) 16384, qq (1) 8192⟩,
     ⟨qq (16) 1, qq (32) 1, qq (17) 64, qq (1) 2, qq (1) 16384, qq (1) 8192⟩,
     ⟨qq (8) 1, qq (16) 1, qq (19) 128, qq (17) 64, qq (1) 8192, qq (1) 4096⟩,
     ⟨qq (1) 1, qq (2) 1, qq (17) 64, qq (49) 128, qq (1) 8192, qq (3) 16384⟩,
     ⟨qq (1) 1, qq (2) 1, qq (49) 128, qq (1) 2, qq (1) 8192, qq (3) 16384⟩,
     ⟨qq (1) 1, qq (2) 1, qq (17) 64, qq (49) 128, qq (3) 16384, qq (1) 4096⟩,
     ⟨qq (1) 1, qq (2) 1, qq (49) 128, qq (1) 2, qq (3) 16384, qq (1) 4096⟩,
     ⟨qq (8) 1, qq (16) 1, qq (17) 64, qq (1) 2, qq (1) 8192, qq (1) 4096⟩,
     ⟨qq (16) 1, qq (24) 1, qq (19) 128, qq (17) 64, qq (1) 8192, qq (1) 4096⟩,
     ⟨qq (24) 1, qq (32) 1, qq (19) 128, qq (17) 64, qq (1) 8192, qq (1) 4096⟩,
     ⟨qq (16) 1, qq (32) 1, qq (17) 64, qq (1) 2, qq (1) 8192, qq (1) 4096⟩,
     ⟨qq (1) 1, qq (2) 1, qq (17) 64, qq (49) 128, qq (1) 4096, qq (3) 8192⟩,
     ⟨qq (1) 1, qq (2) 1, qq (49) 128, qq (1) 2, qq (1) 4096, qq (3) 8192⟩,
     ⟨qq (1) 1, qq (2) 1, qq (17) 64, qq (49) 128, qq (3) 8192, qq (1) 2048⟩,
     ⟨qq (1) 1, qq (2) 1, qq (49) 128, qq (1) 2, qq (3) 8192, qq (1) 2048⟩,
     ⟨qq (3) 2, qq (2) 1, qq (49) 128, qq (1) 2, qq (1) 2048, qq (3) 4096⟩,
     ⟨qq (3) 2, qq (2) 1, qq (49) 128, qq (1) 2, qq (3) 4096, qq (1) 1024⟩,
     ⟨qq (3) 2, qq (2) 1, qq (49) 128, qq (1) 2, qq (1) 1024, qq (3) 2048⟩,
     ⟨qq (3) 2, qq (2) 1, qq (49) 128, qq (1) 2, qq (3) 2048, qq (1) 512⟩,
     ⟨qq (2) 1, qq (3) 1, qq (49) 128, qq (1) 2, qq (3) 2048, qq (1) 512⟩] := by
  decide +kernel

/-- Parent dominance on every archived `parent` leaf box. -/
theorem parent_leaves : ∀ p ∈ parentPaths, ParentSem (ssBox p) := by
  unfold parentPaths
  exact List.forall_mem_cons.2 ⟨Fleet.S000.sem_444444444444444440202020202,
    List.forall_mem_cons.2 ⟨Fleet.S000.sem_444444444444444440202020203,
    List.forall_mem_cons.2 ⟨Fleet.S000.sem_444444444444444440202020212,
    List.forall_mem_cons.2 ⟨Fleet.S000.sem_444444444444444440202020213,
    List.forall_mem_cons.2 ⟨Fleet.S000.sem_44444444444444444020202030,
    List.forall_mem_cons.2 ⟨Fleet.S000.sem_44444444444444444020202031,
    List.forall_mem_cons.2 ⟨Fleet.S000.sem_4444444444444444402020213,
    List.forall_mem_cons.2 ⟨Fleet.S000.sem_4444444444444444402020300,
    List.forall_mem_cons.2 ⟨Fleet.S000.sem_4444444444444444402020301,
    List.forall_mem_cons.2 ⟨Fleet.S000.sem_444444444444444440202031,
    List.forall_mem_cons.2 ⟨Fleet.S000.sem_44444444444444444020213,
    List.forall_mem_cons.2 ⟨Fleet.S000.sem_444444444444444440203000,
    List.forall_mem_cons.2 ⟨Fleet.S001.sem_444444444444444440203001,
    List.forall_mem_cons.2 ⟨Fleet.S001.sem_44444444444444444020301,
    List.forall_mem_cons.2 ⟨Fleet.S001.sem_4444444444444444402031,
    List.forall_mem_cons.2 ⟨Fleet.S001.sem_44444444444444444030001,
    List.forall_mem_cons.2 ⟨Fleet.S001.sem_4444444444444444403001,
    List.forall_mem_cons.2 ⟨Fleet.S001.sem_444444444444444440301,
    List.forall_mem_cons.2 ⟨Fleet.S001.sem_444444444444444450213,
    List.forall_mem_cons.2 ⟨Fleet.S001.sem_4444444444444444503001,
    List.forall_mem_cons.2 ⟨Fleet.S001.sem_444444444444444450301,
    List.forall_mem_cons.2 ⟨Fleet.S001.sem_44444444444444445031,
    List.forall_mem_cons.2 ⟨Fleet.S001.sem_444444444444444451203,
    List.forall_mem_cons.2 ⟨Fleet.S001.sem_444444444444444451213,
    List.forall_mem_cons.2 ⟨Fleet.S002.sem_44444444444444450213,
    List.forall_mem_cons.2 ⟨Fleet.S002.sem_444444444444444503000152,
    List.forall_mem_cons.2 ⟨Fleet.S002.sem_44444444444444450301,
    List.forall_mem_cons.2 ⟨Fleet.S002.sem_4444444444444445031,
    List.forall_mem_cons.2 ⟨Fleet.S002.sem_44444444444444451203,
    List.forall_mem_cons.2 ⟨Fleet.S002.sem_44444444444444451213,
    List.forall_mem_cons.2 ⟨Fleet.S002.sem_444444444444444513,
    List.forall_mem_cons.2 ⟨Fleet.S002.sem_4444444444444450213,
    List.forall_mem_cons.2 ⟨Fleet.S002.sem_44444444444444503000142,
    List.forall_mem_cons.2 ⟨Fleet.S002.sem_44444444444444503000143,
    List.forall_mem_cons.2 ⟨Fleet.S002.sem_44444444444444503000152,
    List.forall_mem_cons.2 ⟨Fleet.S002.sem_44444444444444503000153,
    List.forall_mem_cons.2 ⟨Fleet.S003.sem_4444444444444450301,
    List.forall_mem_cons.2 ⟨Fleet.S003.sem_444444444444445031,
    List.forall_mem_cons.2 ⟨Fleet.S003.sem_4444444444444451203,
    List.forall_mem_cons.2 ⟨Fleet.S003.sem_4444444444444451213,
    List.forall_mem_cons.2 ⟨Fleet.S003.sem_44444444444444513,
    List.forall_mem_cons.2 ⟨Fleet.S003.sem_444444444444450213,
    List.forall_mem_cons.2 ⟨Fleet.S003.sem_4444444444444503000142,
    List.forall_mem_cons.2 ⟨Fleet.S003.sem_4444444444444503000143,
    List.forall_mem_cons.2 ⟨Fleet.S003.sem_4444444444444503000152,
    List.forall_mem_cons.2 ⟨Fleet.S003.sem_4444444444444503000153,
    List.forall_mem_cons.2 ⟨Fleet.S003.sem_444444444444450301,
    List.forall_mem_cons.2 ⟨Fleet.S003.sem_44444444444445031,
    List.forall_mem_cons.2 ⟨Fleet.S004.sem_444444444444451203,
    List.forall_mem_cons.2 ⟨Fleet.S004.sem_444444444444451213,
    List.forall_mem_cons.2 ⟨Fleet.S004.sem_4444444444444513,
    List.forall_mem_cons.2 ⟨Fleet.S004.sem_44444444444450213,
    List.forall_mem_cons.2 ⟨Fleet.S004.sem_444444444444503000142,
    List.forall_mem_cons.2 ⟨Fleet.S004.sem_444444444444503000143,
    List.forall_mem_cons.2 ⟨Fleet.S004.sem_444444444444503000152,
    List.forall_mem_cons.2 ⟨Fleet.S004.sem_444444444444503000153,
    List.forall_mem_cons.2 ⟨Fleet.S004.sem_4444444444445031,
    List.forall_mem_cons.2 ⟨Fleet.S004.sem_44444444444451203,
    List.forall_mem_cons.2 ⟨Fleet.S004.sem_44444444444451213,
    List.forall_mem_cons.2 ⟨Fleet.S004.sem_444444444444513,
    List.forall_mem_cons.2 ⟨Fleet.S005.sem_44444444444503000142,
    List.forall_mem_cons.2 ⟨Fleet.S005.sem_44444444444503000143,
    List.forall_mem_cons.2 ⟨Fleet.S005.sem_44444444444503000152,
    List.forall_mem_cons.2 ⟨Fleet.S005.sem_44444444444503000153,
    List.forall_mem_cons.2 ⟨Fleet.S005.sem_44444444445030001431,
    List.forall_mem_cons.2 ⟨Fleet.S005.sem_44444444445030001531,
    List.forall_mem_cons.2 ⟨Fleet.S005.sem_4444444445030001431,
    List.forall_mem_cons.2 ⟨Fleet.S005.sem_4444444445030001531,
    List.forall_mem_cons.2 ⟨Fleet.S005.sem_444444444503001053,
    fun _ h => by simp at h⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- Canonical (S) family theorem: the `SS_Compact` per-leaf obligation on every archived
`parent` leaf box `CKLaneG3.sBox p`. -/
theorem parent_sLeafOK : ∀ p ∈ parentPaths, CKLaneG3.SLeafOK (CKLaneG3.sBox p) :=
  fun _ hp => sLeafOK_of_parentSem (parent_leaves _ hp)

/-- Canonical (S) parent dominance on every archived `parent` leaf box. -/
theorem parent_parentS : ∀ p ∈ parentPaths, CKLaneG3.ParentS (CKLaneG3.sBox p) := by
  intro p hp
  rw [← toS_ssBox]
  exact parentS_toS (parent_leaves p hp)

/-- Maximal archived parent subtree `444444444444444440202020` (6 leaves). -/
theorem subtree_444444444444444440202020 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 0, 2, 0]) :=
  parentSem_split [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 0, 2, 0] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 0, 2, 0, 2] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 0, 2, 0, 3] 1 (by decide) rfl rfl
    (parentSem_split [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 0, 2, 0, 2] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 0, 2, 0, 2, 0] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 0, 2, 0, 2, 1] 0 (by decide) rfl rfl
      (parentSem_split [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 0, 2, 0, 2, 0] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 0, 2, 0, 2, 0, 3] 1 (by decide) rfl rfl
        (Fleet.S000.sem_444444444444444440202020202)
        (Fleet.S000.sem_444444444444444440202020203))
      (parentSem_split [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 0, 2, 0, 2, 1] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 0, 2, 0, 2, 1, 2] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 0, 2, 0, 2, 1, 3] 1 (by decide) rfl rfl
        (Fleet.S000.sem_444444444444444440202020212)
        (Fleet.S000.sem_444444444444444440202020213)))
    (parentSem_split [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 0, 2, 0, 3] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 0, 2, 0, 3, 0] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 0, 2, 0, 3, 1] 0 (by decide) rfl rfl
      (Fleet.S000.sem_44444444444444444020202030)
      (Fleet.S000.sem_44444444444444444020202031))

/-- Maximal archived parent subtree `4444444444444444402020213` (1 leaves). -/
theorem subtree_4444444444444444402020213 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 0, 2, 1, 3]) :=
  Fleet.S000.sem_4444444444444444402020213

/-- Maximal archived parent subtree `44444444444444444020203` (3 leaves). -/
theorem subtree_44444444444444444020203 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 0, 3]) :=
  parentSem_split [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 0, 3] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 0, 3, 0] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 0, 3, 1] 0 (by decide) rfl rfl
    (parentSem_split [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 0, 3, 0] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 0, 3, 0, 0] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 0, 3, 0, 1] 0 (by decide) rfl rfl
      (Fleet.S000.sem_4444444444444444402020300)
      (Fleet.S000.sem_4444444444444444402020301))
    (Fleet.S000.sem_444444444444444440202031)

/-- Maximal archived parent subtree `44444444444444444020213` (1 leaves). -/
theorem subtree_44444444444444444020213 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 1, 3]) :=
  Fleet.S000.sem_44444444444444444020213

/-- Maximal archived parent subtree `444444444444444440203` (4 leaves). -/
theorem subtree_444444444444444440203 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 3]) :=
  parentSem_split [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 3] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 3, 0] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 3, 1] 0 (by decide) rfl rfl
    (parentSem_split [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 3, 0] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 3, 0, 0] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 3, 0, 1] 0 (by decide) rfl rfl
      (parentSem_split [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 3, 0, 0] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 3, 0, 0, 0] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 3, 0, 0, 1] 0 (by decide) rfl rfl
        (Fleet.S000.sem_444444444444444440203000)
        (Fleet.S001.sem_444444444444444440203001))
      (Fleet.S001.sem_44444444444444444020301))
    (Fleet.S001.sem_4444444444444444402031)

/-- Maximal archived parent subtree `44444444444444444030001` (1 leaves). -/
theorem subtree_44444444444444444030001 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 3, 0, 0, 0, 1]) :=
  Fleet.S001.sem_44444444444444444030001

/-- Maximal archived parent subtree `4444444444444444403001` (1 leaves). -/
theorem subtree_4444444444444444403001 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 3, 0, 0, 1]) :=
  Fleet.S001.sem_4444444444444444403001

/-- Maximal archived parent subtree `444444444444444440301` (1 leaves). -/
theorem subtree_444444444444444440301 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 3, 0, 1]) :=
  Fleet.S001.sem_444444444444444440301

/-- Maximal archived parent subtree `444444444444444450213` (1 leaves). -/
theorem subtree_444444444444444450213 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 2, 1, 3]) :=
  Fleet.S001.sem_444444444444444450213

/-- Maximal archived parent subtree `4444444444444444503001` (1 leaves). -/
theorem subtree_4444444444444444503001 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 1]) :=
  Fleet.S001.sem_4444444444444444503001

/-- Maximal archived parent subtree `444444444444444450301` (1 leaves). -/
theorem subtree_444444444444444450301 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 1]) :=
  Fleet.S001.sem_444444444444444450301

/-- Maximal archived parent subtree `44444444444444445031` (1 leaves). -/
theorem subtree_44444444444444445031 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 1]) :=
  Fleet.S001.sem_44444444444444445031

/-- Maximal archived parent subtree `444444444444444451203` (1 leaves). -/
theorem subtree_444444444444444451203 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 2, 0, 3]) :=
  Fleet.S001.sem_444444444444444451203

/-- Maximal archived parent subtree `444444444444444451213` (1 leaves). -/
theorem subtree_444444444444444451213 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 2, 1, 3]) :=
  Fleet.S001.sem_444444444444444451213

/-- Maximal archived parent subtree `44444444444444450213` (1 leaves). -/
theorem subtree_44444444444444450213 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 2, 1, 3]) :=
  Fleet.S002.sem_44444444444444450213

/-- Maximal archived parent subtree `444444444444444503000152` (1 leaves). -/
theorem subtree_444444444444444503000152 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 5, 2]) :=
  Fleet.S002.sem_444444444444444503000152

/-- Maximal archived parent subtree `44444444444444450301` (1 leaves). -/
theorem subtree_44444444444444450301 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 1]) :=
  Fleet.S002.sem_44444444444444450301

/-- Maximal archived parent subtree `4444444444444445031` (1 leaves). -/
theorem subtree_4444444444444445031 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 1]) :=
  Fleet.S002.sem_4444444444444445031

/-- Maximal archived parent subtree `44444444444444451203` (1 leaves). -/
theorem subtree_44444444444444451203 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 2, 0, 3]) :=
  Fleet.S002.sem_44444444444444451203

/-- Maximal archived parent subtree `44444444444444451213` (1 leaves). -/
theorem subtree_44444444444444451213 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 2, 1, 3]) :=
  Fleet.S002.sem_44444444444444451213

/-- Maximal archived parent subtree `444444444444444513` (1 leaves). -/
theorem subtree_444444444444444513 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 3]) :=
  Fleet.S002.sem_444444444444444513

/-- Maximal archived parent subtree `4444444444444450213` (1 leaves). -/
theorem subtree_4444444444444450213 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 2, 1, 3]) :=
  Fleet.S002.sem_4444444444444450213

/-- Maximal archived parent subtree `444444444444445030001` (4 leaves). -/
theorem subtree_444444444444445030001 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1]) :=
  parentSem_split [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 4] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 5] 2 (by decide) rfl rfl
    (parentSem_split [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 4] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 4, 2] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 4, 3] 1 (by decide) rfl rfl
      (Fleet.S002.sem_44444444444444503000142)
      (Fleet.S002.sem_44444444444444503000143))
    (parentSem_split [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 5] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 5, 2] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 5, 3] 1 (by decide) rfl rfl
      (Fleet.S002.sem_44444444444444503000152)
      (Fleet.S002.sem_44444444444444503000153))

/-- Maximal archived parent subtree `4444444444444450301` (1 leaves). -/
theorem subtree_4444444444444450301 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 1]) :=
  Fleet.S003.sem_4444444444444450301

/-- Maximal archived parent subtree `444444444444445031` (1 leaves). -/
theorem subtree_444444444444445031 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 1]) :=
  Fleet.S003.sem_444444444444445031

/-- Maximal archived parent subtree `4444444444444451203` (1 leaves). -/
theorem subtree_4444444444444451203 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 2, 0, 3]) :=
  Fleet.S003.sem_4444444444444451203

/-- Maximal archived parent subtree `4444444444444451213` (1 leaves). -/
theorem subtree_4444444444444451213 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 2, 1, 3]) :=
  Fleet.S003.sem_4444444444444451213

/-- Maximal archived parent subtree `44444444444444513` (1 leaves). -/
theorem subtree_44444444444444513 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 3]) :=
  Fleet.S003.sem_44444444444444513

/-- Maximal archived parent subtree `444444444444450213` (1 leaves). -/
theorem subtree_444444444444450213 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 2, 1, 3]) :=
  Fleet.S003.sem_444444444444450213

/-- Maximal archived parent subtree `44444444444445030001` (4 leaves). -/
theorem subtree_44444444444445030001 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1]) :=
  parentSem_split [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 4] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 5] 2 (by decide) rfl rfl
    (parentSem_split [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 4] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 4, 2] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 4, 3] 1 (by decide) rfl rfl
      (Fleet.S003.sem_4444444444444503000142)
      (Fleet.S003.sem_4444444444444503000143))
    (parentSem_split [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 5] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 5, 2] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 5, 3] 1 (by decide) rfl rfl
      (Fleet.S003.sem_4444444444444503000152)
      (Fleet.S003.sem_4444444444444503000153))

/-- Maximal archived parent subtree `444444444444450301` (1 leaves). -/
theorem subtree_444444444444450301 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 1]) :=
  Fleet.S003.sem_444444444444450301

/-- Maximal archived parent subtree `44444444444445031` (1 leaves). -/
theorem subtree_44444444444445031 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 1]) :=
  Fleet.S003.sem_44444444444445031

/-- Maximal archived parent subtree `444444444444451203` (1 leaves). -/
theorem subtree_444444444444451203 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 2, 0, 3]) :=
  Fleet.S004.sem_444444444444451203

/-- Maximal archived parent subtree `444444444444451213` (1 leaves). -/
theorem subtree_444444444444451213 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 2, 1, 3]) :=
  Fleet.S004.sem_444444444444451213

/-- Maximal archived parent subtree `4444444444444513` (1 leaves). -/
theorem subtree_4444444444444513 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 3]) :=
  Fleet.S004.sem_4444444444444513

/-- Maximal archived parent subtree `44444444444450213` (1 leaves). -/
theorem subtree_44444444444450213 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 2, 1, 3]) :=
  Fleet.S004.sem_44444444444450213

/-- Maximal archived parent subtree `4444444444445030001` (4 leaves). -/
theorem subtree_4444444444445030001 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1]) :=
  parentSem_split [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 4] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 5] 2 (by decide) rfl rfl
    (parentSem_split [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 4] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 4, 2] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 4, 3] 1 (by decide) rfl rfl
      (Fleet.S004.sem_444444444444503000142)
      (Fleet.S004.sem_444444444444503000143))
    (parentSem_split [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 5] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 5, 2] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 5, 3] 1 (by decide) rfl rfl
      (Fleet.S004.sem_444444444444503000152)
      (Fleet.S004.sem_444444444444503000153))

/-- Maximal archived parent subtree `4444444444445031` (1 leaves). -/
theorem subtree_4444444444445031 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 1]) :=
  Fleet.S004.sem_4444444444445031

/-- Maximal archived parent subtree `44444444444451203` (1 leaves). -/
theorem subtree_44444444444451203 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 2, 0, 3]) :=
  Fleet.S004.sem_44444444444451203

/-- Maximal archived parent subtree `44444444444451213` (1 leaves). -/
theorem subtree_44444444444451213 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 2, 1, 3]) :=
  Fleet.S004.sem_44444444444451213

/-- Maximal archived parent subtree `444444444444513` (1 leaves). -/
theorem subtree_444444444444513 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 3]) :=
  Fleet.S004.sem_444444444444513

/-- Maximal archived parent subtree `444444444445030001` (4 leaves). -/
theorem subtree_444444444445030001 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1]) :=
  parentSem_split [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 4] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 5] 2 (by decide) rfl rfl
    (parentSem_split [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 4] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 4, 2] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 4, 3] 1 (by decide) rfl rfl
      (Fleet.S005.sem_44444444444503000142)
      (Fleet.S005.sem_44444444444503000143))
    (parentSem_split [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 5] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 5, 2] [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 5, 3] 1 (by decide) rfl rfl
      (Fleet.S005.sem_44444444444503000152)
      (Fleet.S005.sem_44444444444503000153))

/-- Maximal archived parent subtree `44444444445030001431` (1 leaves). -/
theorem subtree_44444444445030001431 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 4, 3, 1]) :=
  Fleet.S005.sem_44444444445030001431

/-- Maximal archived parent subtree `44444444445030001531` (1 leaves). -/
theorem subtree_44444444445030001531 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 5, 3, 1]) :=
  Fleet.S005.sem_44444444445030001531

/-- Maximal archived parent subtree `4444444445030001431` (1 leaves). -/
theorem subtree_4444444445030001431 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 4, 3, 1]) :=
  Fleet.S005.sem_4444444445030001431

/-- Maximal archived parent subtree `4444444445030001531` (1 leaves). -/
theorem subtree_4444444445030001531 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 5, 3, 1]) :=
  Fleet.S005.sem_4444444445030001531

/-- Maximal archived parent subtree `444444444503001053` (1 leaves). -/
theorem subtree_444444444503001053 : ParentSem (ssBox [4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 1, 0, 5, 3]) :=
  Fleet.S005.sem_444444444503001053

/-- The 47 maximal archived subtrees whose leaves are all `parent` leaves. -/
def parentSubtrees : List (List ℕ) :=
  [[4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 0, 2, 0],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 0, 2, 1, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 0, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 2, 1, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 2, 0, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 3, 0, 0, 0, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 3, 0, 0, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 3, 0, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 2, 1, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 2, 0, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 2, 1, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 2, 1, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 5, 2],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 2, 0, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 2, 1, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 2, 1, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 2, 0, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 2, 1, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 2, 1, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 2, 0, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 2, 1, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 2, 1, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 2, 0, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 2, 1, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 3],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 4, 3, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 5, 3, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 4, 3, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 0, 1, 5, 3, 1],
   [4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 3, 0, 0, 1, 0, 5, 3]]

theorem parentSubtrees_length : parentSubtrees.length = 47 := by decide +kernel

theorem parent_subtrees : ∀ p ∈ parentSubtrees, ParentSem (ssBox p) := by
  unfold parentSubtrees
  exact List.forall_mem_cons.2 ⟨subtree_444444444444444440202020,
    List.forall_mem_cons.2 ⟨subtree_4444444444444444402020213,
    List.forall_mem_cons.2 ⟨subtree_44444444444444444020203,
    List.forall_mem_cons.2 ⟨subtree_44444444444444444020213,
    List.forall_mem_cons.2 ⟨subtree_444444444444444440203,
    List.forall_mem_cons.2 ⟨subtree_44444444444444444030001,
    List.forall_mem_cons.2 ⟨subtree_4444444444444444403001,
    List.forall_mem_cons.2 ⟨subtree_444444444444444440301,
    List.forall_mem_cons.2 ⟨subtree_444444444444444450213,
    List.forall_mem_cons.2 ⟨subtree_4444444444444444503001,
    List.forall_mem_cons.2 ⟨subtree_444444444444444450301,
    List.forall_mem_cons.2 ⟨subtree_44444444444444445031,
    List.forall_mem_cons.2 ⟨subtree_444444444444444451203,
    List.forall_mem_cons.2 ⟨subtree_444444444444444451213,
    List.forall_mem_cons.2 ⟨subtree_44444444444444450213,
    List.forall_mem_cons.2 ⟨subtree_444444444444444503000152,
    List.forall_mem_cons.2 ⟨subtree_44444444444444450301,
    List.forall_mem_cons.2 ⟨subtree_4444444444444445031,
    List.forall_mem_cons.2 ⟨subtree_44444444444444451203,
    List.forall_mem_cons.2 ⟨subtree_44444444444444451213,
    List.forall_mem_cons.2 ⟨subtree_444444444444444513,
    List.forall_mem_cons.2 ⟨subtree_4444444444444450213,
    List.forall_mem_cons.2 ⟨subtree_444444444444445030001,
    List.forall_mem_cons.2 ⟨subtree_4444444444444450301,
    List.forall_mem_cons.2 ⟨subtree_444444444444445031,
    List.forall_mem_cons.2 ⟨subtree_4444444444444451203,
    List.forall_mem_cons.2 ⟨subtree_4444444444444451213,
    List.forall_mem_cons.2 ⟨subtree_44444444444444513,
    List.forall_mem_cons.2 ⟨subtree_444444444444450213,
    List.forall_mem_cons.2 ⟨subtree_44444444444445030001,
    List.forall_mem_cons.2 ⟨subtree_444444444444450301,
    List.forall_mem_cons.2 ⟨subtree_44444444444445031,
    List.forall_mem_cons.2 ⟨subtree_444444444444451203,
    List.forall_mem_cons.2 ⟨subtree_444444444444451213,
    List.forall_mem_cons.2 ⟨subtree_4444444444444513,
    List.forall_mem_cons.2 ⟨subtree_44444444444450213,
    List.forall_mem_cons.2 ⟨subtree_4444444444445030001,
    List.forall_mem_cons.2 ⟨subtree_4444444444445031,
    List.forall_mem_cons.2 ⟨subtree_44444444444451203,
    List.forall_mem_cons.2 ⟨subtree_44444444444451213,
    List.forall_mem_cons.2 ⟨subtree_444444444444513,
    List.forall_mem_cons.2 ⟨subtree_444444444445030001,
    List.forall_mem_cons.2 ⟨subtree_44444444445030001431,
    List.forall_mem_cons.2 ⟨subtree_44444444445030001531,
    List.forall_mem_cons.2 ⟨subtree_4444444445030001431,
    List.forall_mem_cons.2 ⟨subtree_4444444445030001531,
    List.forall_mem_cons.2 ⟨subtree_444444444503001053,
    fun _ h => by simp at h⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem parent_subtrees_sLeafOK : ∀ p ∈ parentSubtrees, CKLaneG3.SLeafOK (CKLaneG3.sBox p) :=
  fun _ hp => sLeafOK_of_parentSem (parent_subtrees _ hp)

theorem parent_subtrees_parentS : ∀ p ∈ parentSubtrees, CKLaneG3.ParentS (CKLaneG3.sBox p) := by
  intro p hp
  rw [← toS_ssBox]
  exact parentS_toS (parent_subtrees p hp)

end CKLaneM05

#check @CKLaneM05.parent_leaves
#print axioms CKLaneM05.parent_leaves
#check @CKLaneM05.parent_sLeafOK
#print axioms CKLaneM05.parent_sLeafOK
#check @CKLaneM05.parent_subtrees
#print axioms CKLaneM05.parent_subtrees

end


