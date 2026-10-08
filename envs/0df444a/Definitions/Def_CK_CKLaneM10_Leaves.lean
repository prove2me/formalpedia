-- Prove2me | Definitions.Def_CK_CKLaneM10_Leaves
-- name    : CK_CKLaneM10_Leaves
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T05:16:19.684099+00:00
-- url     : https://prove2.me/theorems/f580c806-bdb8-4e64-af11-27f94ac1b120
-- title:
--   Courtade–Kumar proof module `CKLaneM10.Leaves` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM10.Leaves` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM10.Leaves` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM10.Leaves (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM10/Leaves.lean)

import Definitions.Def_CK_CKLaneM10_Leaves_q101

namespace CKLaneM10.Leaves
open CKLaneD CKLaneM10
/-- Owner form (psi-active branch) for Lane G. -/
theorem feasibleSplit_leaves_gap_le_cost :
    ∀ q ∈ ArchTree.archTree.leaves, q.2 = 3 → ∀ (k : ℕ) (μ : GeneralCK.InteriorLaw (Fin k)),
      InUVT (uvtBox q.1) μ.a μ.b μ.meanEntropy →
      GeneralCK.phi μ.midpoint μ.meanEntropy ≤ GeneralCK.psi μ.midpoint μ.meanEntropy →
      μ.gap ≤ μ.cost := by
  intro q hq h3 k μ hin hact
  exact semUVT_gap_le_cost (feasibleSplit_leaves_sem q hq h3) μ hin hact

end CKLaneM10.Leaves


