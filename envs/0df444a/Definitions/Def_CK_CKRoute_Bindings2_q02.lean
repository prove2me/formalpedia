-- Prove2me | Definitions.Def_CK_CKRoute_Bindings2_q02
-- name    : CK_CKRoute_Bindings2_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T22:58:44.352033+00:00
-- url     : https://prove2.me/theorems/aaf0ea8f-6606-41ce-b41c-e8df7cab4a4e
-- title:
--   Courtade–Kumar proof module `CKRoute.Bindings2 (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKRoute.Bindings2 (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKRoute.Bindings2 (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKRoute.Bindings2 (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKRoute/Bindings2 (piece 3 of 4).lean)

import Definitions.Def_CK_CKRoute_Bindings2_q01

namespace CKRoute
open GeneralCK
theorem RemainingRows2.toRoute (h : RemainingRows2) : ManuscriptRoute where
  phiBranch := h.theorem71.phiBranch
  centralSquare := h.centralSquare
  ssSmallMean := row_ssSmallMean
  ssRatioTail := row_ssRatioTail
  ssCompact := h.ssCompact
  opBoundaryStrip := route_opBoundaryStrip
  opCorner := route_opCorner
  opLowEntropy := row_opLowEntropy
  opCompact := opCompact_of_labels013 h.oLabel0 h.oLabel1 h.oLabel3

end CKRoute


