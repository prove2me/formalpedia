-- Prove2me | Definitions.Def_CK_CKLaneN1_CEStatCapital
-- name    : CK_CKLaneN1_CEStatCapital
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T06:17:14.006513+00:00
-- url     : https://prove2.me/theorems/3cd4c8e3-c6d1-4096-bf45-21ec2afb1ab1
-- title:
--   Courtade–Kumar proof module `CKLaneN1.CEStatCapital` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1.CEStatCapital` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1.CEStatCapital` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1.CEStatCapital (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1/CEStatCapital.lean)

import Definitions.Def_CK_CKLaneN1_CapShard_K00
import Definitions.Def_CK_CKLaneN1_CapShard_K01
import Definitions.Def_CK_CKLaneN1_CapShard_K02
import Definitions.Def_CK_CKLaneN1_CapShard_K03
import Definitions.Def_CK_CKLaneN1_CapShard_K04
import Definitions.Def_CK_CKLaneN1_CapShard_K05
import Definitions.Def_CK_CKLaneN1_CapShard_K06
import Definitions.Def_CK_CKLaneN1_CapShard_K07
import Definitions.Def_CK_CKLaneN1_CapShard_K08
import Definitions.Def_CK_CKLaneN1_Chunks
import Definitions.Def_CK_CKLaneN1_CapKey

-- ===== source module CKLaneN1.CEStatCapital =====
section

set_option autoImplicit false

/-!
# Lane N1: CE-stat S.3 row 2 — capital exclusion

`capTree_ok`: all 531 capital boxes pass the kernel check (fleet shards `CapShard.K00..K08`,
`decide +kernel`). With the analytic tails of `CapTail` this gives the concavity-free pure-`Θ`
inequality `theta_capital` and the S.3 owner `capitalExclusion : CapitalExclusion`.
-/

namespace CKLaneN1.Capital

open GeneralCK CKLaneN1.CEStat

theorem capTree_length : capTree.leaves.length = 531 := by decide +kernel

/-- Every capital box passes the kernel check. -/
theorem capTree_ok : capTree.allLeaves (fun p w => capLeafOK (capRoot.ofPath p) w) = true := by
  unfold PT.allLeaves
  apply all_of_chunks (fun q => capLeafOK (capRoot.ofPath q.1) q.2) 60 9 capTree.leaves
    (by rw [capTree_length]; decide)
  intro k hk
  interval_cases k
  · exact CapShard.K00
  · exact CapShard.K01
  · exact CapShard.K02
  · exact CapShard.K03
  · exact CapShard.K04
  · exact CapShard.K05
  · exact CapShard.K06
  · exact CapShard.K07
  · exact CapShard.K08

/-- **Pure-Θ capital inequality** (concavity-free) on `[21/200, ∞) × [303/50, ∞)`. -/
theorem theta_capital {U W : ℝ} (hU : 21 / 200 ≤ U) (hW : 303 / 50 ≤ W) :
    e8Theta (U + 2 * W) ≤ e8Theta U + e8Theta W :=
  theta_capital_of_tree capTree_ok hU hW

/-- **S.3 row 2 (CE-stat capital exclusion).** -/
theorem capitalExclusion : CapitalExclusion := capitalExclusion_of_tree capTree_ok

end CKLaneN1.Capital

end


