-- Prove2me | Definitions.Def_CK_CKLaneG1_E25All
-- name    : CK_CKLaneG1_E25All
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-05T04:39:54.724548+00:00
-- url     : https://prove2.me/theorems/27b7d8c9-98b1-435d-9036-c1b5313783b7
-- title:
--   Courtade–Kumar proof module `CKLaneG1.E25All` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG1.E25All` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG1.E25All` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG1.E25All (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG1/E25All.lean)

import Definitions.Def_CK_CKLaneG1_E25S_S0000__4
import Definitions.Def_CK_CKLaneG1_E25S_S0004__4
import Definitions.Def_CK_CKLaneG1_E25S_S0008__3
import Definitions.Def_CK_CKLaneG1_E25S_S0011__4
import Definitions.Def_CK_CKLaneG1_E25S_S0015__2

-- ===== source module CKLaneG1.E25All =====
section

/-!
# Lane G1: union of the E ≤ 1/25 certificate shards

`all` = the 4,178 archived (O) leaves classified `le` in `G1/trees/archiveO/e25_index_v1.json`
(shards `CKLaneG1.E25S.S0000..S0016`); `all_le`: each of their clipped physical images
`CKLaneD.InUVT (uvtBox p)` lies in `E ≤ 1/25` (the region delegated to OUTER_OPPOSITE_LOW_ENTROPY).
-/

namespace CKLaneG1.E25All

open CKLaneD CKLaneG1

def all : List (List ℕ × EW) :=
  E25S.S0000.leaves ++ (E25S.S0001.leaves ++ (E25S.S0002.leaves ++ (E25S.S0003.leaves ++ (E25S.S0004.leaves ++ (E25S.S0005.leaves ++ (E25S.S0006.leaves ++ (E25S.S0007.leaves ++ (E25S.S0008.leaves ++ (E25S.S0009.leaves ++ (E25S.S0010.leaves ++ (E25S.S0011.leaves ++ (E25S.S0012.leaves ++ (E25S.S0013.leaves ++ (E25S.S0014.leaves ++ (E25S.S0015.leaves ++ (E25S.S0016.leaves))))))))))))))))

theorem all_length : all.length = 4178 := by decide +kernel

theorem all_le : ∀ x ∈ all, ∀ a b E : ℝ, InUVT (uvtBox x.1) a b E → E ≤ 1 / 25 := by
  intro x hx
  simp only [all, List.mem_append] at hx
  rcases hx with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  exacts [E25S.S0000.le x h, E25S.S0001.le x h, E25S.S0002.le x h, E25S.S0003.le x h, E25S.S0004.le x h, E25S.S0005.le x h, E25S.S0006.le x h, E25S.S0007.le x h, E25S.S0008.le x h, E25S.S0009.le x h, E25S.S0010.le x h, E25S.S0011.le x h, E25S.S0012.le x h, E25S.S0013.le x h, E25S.S0014.le x h, E25S.S0015.le x h, E25S.S0016.le x h]

end CKLaneG1.E25All

end


