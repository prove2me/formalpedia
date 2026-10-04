-- Prove2me | Definitions.Def_CK_CKLaneC_SAxis_Data_TableSuf07
-- name    : CK_CKLaneC_SAxis_Data_TableSuf07
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T10:24:39.42972+00:00
-- url     : https://prove2.me/theorems/a5e1d315-7ce6-43dd-a25e-e1bf13b8a534
-- title:
--   Courtade–Kumar proof module `CKLaneC.SAxis.Data.Table (suffix chain 07)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.SAxis.Data.Table (suffix chain 07)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.SAxis.Data.Table (suffix chain 07)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.SAxis.Data.Table (suffix chain 07) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/SAxis/Data/Table (suffix chain 07).lean)

import Definitions.Def_CK_CKLaneC_SAxis_Data_Tab07
import Definitions.Def_CK_CKLaneC_SAxis_Data_TableSuf08

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
open CKLaneC.S3.SlopeTable CKLaneC.S3.SlopeChain
namespace CKLaneC.SAxis.Data
theorem tabsuf07_valid : TableValid [tab07, tab08, tab09, tab10, tab11, tab12, tab13] :=
  tableValid_cons tab07_valid tabsuf08_valid

end CKLaneC.SAxis.Data


