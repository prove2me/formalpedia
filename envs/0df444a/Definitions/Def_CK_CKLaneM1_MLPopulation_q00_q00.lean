-- Prove2me | Definitions.Def_CK_CKLaneM1_MLPopulation_q00_q00
-- name    : CK_CKLaneM1_MLPopulation_q00_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T21:14:16.900086+00:00
-- url     : https://prove2.me/theorems/b67c7e9f-e129-4e69-8a8d-9e3e00829f3e
-- title:
--   Courtade–Kumar proof module `CKLaneM1.MLPopulation (piece 1 of 4) (piece 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM1.MLPopulation (piece 1 of 4) (piece 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM1.MLPopulation (piece 1 of 4) (piece 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM1.MLPopulation (piece 1 of 4) (piece 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM1/MLPopulation (piece 1 of 4) (piece 1 of 2).lean)

import Definitions.Def_CK_CKLaneM1_MLChecker




/-!
# Lane M1: the archived `same_side.mean_logsum` population

`allLeaves` concatenates the 423 kernel-checked shards (50429 archived leaves, each bound to its
archive path by `checkLeaf`).  `all_paths_sLeafOK` is the coordinator's final (S) family form
`∀ archived mean_logsum path p, CKLaneG3.SLeafOK (CKLaneG3.sBox p)` (the path list equals the archived
mean_logsum leaves of `same_side/ADAPT_RESULT.json`, see work/population_receipt.json).
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace CKLaneM1.ML.Population

open CKLaneM1.ML

theorem sem_append {L₁ L₂ : List (List ℕ × LeafCert)}
    (h₁ : ∀ x ∈ L₁, SemSS (ssBox x.1)) (h₂ : ∀ x ∈ L₂, SemSS (ssBox x.1)) :
    ∀ x ∈ L₁ ++ L₂, SemSS (ssBox x.1) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact h₁ x h
  · exact h₂ x h

end CKLaneM1.ML.Population


