-- Prove2me | Definitions.Def_CK_CKLaneA1_R5Data_C000
-- name    : CK_CKLaneA1_R5Data_C000
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T15:35:46.082976+00:00
-- url     : https://prove2.me/theorems/a4f70677-7a57-4547-8f78-287cb256853a
-- title:
--   Courtade–Kumar proof module `CKLaneA1.R5Data.C000` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.R5Data.C000` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.R5Data.C000` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.R5Data.C000 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/R5Data/C000.lean)

import Definitions.Def_CK_CKLaneA1_R5Data_C000_part00

/-! Generated CE-stat row-5 cover chunk 0 (8 strips, 251 cells, est 125 s kernel).
Each strip is checked by kernel evaluation of the Boolean checker `CKLaneA1.R5.stripOK`
(one declaration per strip, so kernel caches stay small). -/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace CKLaneA1.R5Data

open CKLaneA1.R5

theorem s000_07_ok : stripOK s000_07 = true := by decide +kernel

def strips000 : List Strip := [s000_00, s000_01, s000_02, s000_03, s000_04, s000_05, s000_06, s000_07]

theorem strips000_ok : strips000.all stripOK = true := by
  simp only [strips000, List.all_cons, List.all_nil, s000_00_ok, s000_01_ok, s000_02_ok, s000_03_ok, s000_04_ok, s000_05_ok, s000_06_ok, s000_07_ok, Bool.and_true]

end CKLaneA1.R5Data


