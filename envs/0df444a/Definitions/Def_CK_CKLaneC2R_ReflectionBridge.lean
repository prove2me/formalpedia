-- Prove2me | Definitions.Def_CK_CKLaneC2R_ReflectionBridge
-- name    : CK_CKLaneC2R_ReflectionBridge
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-11T16:21:16.517054+00:00
-- url     : https://prove2.me/theorems/fada2897-2570-421d-8386-3d52ed5e74af
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.ReflectionBridge` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.ReflectionBridge` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.ReflectionBridge` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.ReflectionBridge (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/ReflectionBridge.lean)

import Definitions.Def_CK_CKLaneC2R_ReflectionBridge_q00

namespace CKLaneC2R
/-- The reflection field (`Theorem71Components.reflection` / `ProductionOwners.reflection`). -/
theorem reflection_certified :
    ∀ a b : ℝ, 0 < b → b < a → a < 1 → 0 ≤ GeneralCK.Reflection.curvature a b :=
  reflection_of_hsmall GeneralCK.Reflection.curvature_nonneg_small_bias

end CKLaneC2R


