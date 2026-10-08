-- Prove2me | Definitions.Def_CK_CKRoute_Bindings2
-- name    : CK_CKRoute_Bindings2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T23:48:12.479035+00:00
-- url     : https://prove2.me/theorems/1bc81531-5b1b-46f6-99e5-cae15148af81
-- title:
--   Courtade–Kumar proof module `CKRoute.Bindings2` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKRoute.Bindings2` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKRoute.Bindings2` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKRoute.Bindings2 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKRoute/Bindings2.lean)

import Definitions.Def_CK_CKRoute_Bindings2_q02

namespace CKRoute
open GeneralCK
/-- Conditional: General CK from the remaining rows. -/
theorem generalCourtadeKumar_of_remainingRows2 (h : RemainingRows2) : GeneralCourtadeKumar :=
  generalCourtadeKumar_of_manuscriptRoute h.toRoute

end CKRoute


