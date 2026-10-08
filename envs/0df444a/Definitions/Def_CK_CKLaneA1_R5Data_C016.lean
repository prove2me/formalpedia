-- Prove2me | Definitions.Def_CK_CKLaneA1_R5Data_C016
-- name    : CK_CKLaneA1_R5Data_C016
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T12:03:28.491975+00:00
-- url     : https://prove2.me/theorems/ff0bc0e7-94c8-4df2-8567-787417a8db6b
-- title:
--   Courtade–Kumar proof module `CKLaneA1.R5Data.C016` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.R5Data.C016` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.R5Data.C016` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.R5Data.C016 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/R5Data/C016.lean)

import Definitions.Def_CK_CKLaneA1_R5Data_C016_part00

/-! Generated CE-stat row-5 cover chunk 16 (9 strips, 664 cells, est 223 s kernel).
Each strip is checked by kernel evaluation of the Boolean checker `CKLaneA1.R5.stripOK`
(one declaration per strip, so kernel caches stay small). -/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace CKLaneA1.R5Data

open CKLaneA1.R5

theorem s016_08_ok : stripOK s016_08 = true := by decide +kernel

def strips016 : List Strip := [s016_00, s016_01, s016_02, s016_03, s016_04, s016_05, s016_06, s016_07, s016_08]

theorem strips016_ok : strips016.all stripOK = true := by
  simp only [strips016, List.all_cons, List.all_nil, s016_00_ok, s016_01_ok, s016_02_ok, s016_03_ok, s016_04_ok, s016_05_ok, s016_06_ok, s016_07_ok, s016_08_ok, Bool.and_true]

end CKLaneA1.R5Data


