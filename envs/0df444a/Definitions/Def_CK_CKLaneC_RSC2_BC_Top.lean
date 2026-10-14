-- Prove2me | Definitions.Def_CK_CKLaneC_RSC2_BC_Top
-- name    : CK_CKLaneC_RSC2_BC_Top
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-11T22:23:31.42889+00:00
-- url     : https://prove2.me/theorems/45e1910a-cd8b-416d-b525-96fbabf33d72
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSC2.BC_Top` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSC2.BC_Top` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSC2.BC_Top` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSC2.BC_Top (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSC2/BC_Top.lean)

import Definitions.Def_CK_CKLaneC_RSC2_BC_Top_q01

namespace CKLaneC.RSC2.BC_Top
open CKLaneC.RSCell
theorem root_region : RegionPos (3 / 8 : ℝ) (7 / 16 : ℝ) (0 : ℝ) (1 : ℝ) (1 / 8 : ℝ) (1 : ℝ) :=
  RegionPosI.toReal rootI (by norm_num [one]) (by norm_num [one]) (by norm_num [one]) (by norm_num [one]) (by norm_num [one]) (by norm_num [one])

end CKLaneC.RSC2.BC_Top


