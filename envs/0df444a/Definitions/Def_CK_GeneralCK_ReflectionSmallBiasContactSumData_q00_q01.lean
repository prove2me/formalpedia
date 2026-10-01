-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionSmallBiasContactSumData_q00_q01
-- name    : CK_GeneralCK_ReflectionSmallBiasContactSumData_q00_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T08:03:55.114441+00:00
-- url     : https://prove2.me/theorems/33e3a3fa-5975-4225-a25e-412033bf8218
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionSmallBiasContactSumData (piece 1 of 4) (piece 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionSmallBiasContactSumData (piece 1 of 4) (piece 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionSmallBiasContactSumData (piece 1 of 4) (piece 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionSmallBiasContactSumData (piece 1 of 4) (piece 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionSmallBiasContactSumData (piece 1 of 4) (piece 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasContactSumData_q00_q01_q00

namespace GeneralCK.Reflection.SmallBiasContactSum
open SmallBiasPolynomial SmallBiasJet SmallBiasPerspectiveJet
open SmallBiasContactDegrees SmallBiasHalfSumPowers SmallBiasBivariateBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def contactSum6_raw : List Term := contactSum4 ++ group6

end GeneralCK.Reflection.SmallBiasContactSum


