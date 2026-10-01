-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionSmallBiasContactSumChecks2
-- name    : CK_GeneralCK_ReflectionSmallBiasContactSumChecks2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T10:08:12.849992+00:00
-- url     : https://prove2.me/theorems/67f7471c-2c32-4b22-8b5c-ac89b0c4888c
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionSmallBiasContactSumChecks2` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionSmallBiasContactSumChecks2` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionSmallBiasContactSumChecks2` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionSmallBiasContactSumChecks2 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionSmallBiasContactSumChecks2.lean)

import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasContactSumData

-- ===== source module GeneralCK.ReflectionSmallBiasContactSumChecks2 =====
section

namespace GeneralCK.Reflection.SmallBiasContactSum

open SmallBiasPolynomial SmallBiasJet SmallBiasPerspectiveJet
open SmallBiasContactDegrees SmallBiasHalfSumPowers SmallBiasBivariateBase

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem contactSum6_raw_bound : fineBound 48 contactSum6_raw = true := by
  decide +kernel

theorem contactSum6_result_bound : fineBound 48 contactSum6 = true := by
  decide +kernel

theorem contactSum6_degree0 : equalityCheck (finePart 0 contactSum6_raw) (finePart 0 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree1 : equalityCheck (finePart 1 contactSum6_raw) (finePart 1 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree2 : equalityCheck (finePart 2 contactSum6_raw) (finePart 2 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree3 : equalityCheck (finePart 3 contactSum6_raw) (finePart 3 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree4 : equalityCheck (finePart 4 contactSum6_raw) (finePart 4 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree5 : equalityCheck (finePart 5 contactSum6_raw) (finePart 5 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree6 : equalityCheck (finePart 6 contactSum6_raw) (finePart 6 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree7 : equalityCheck (finePart 7 contactSum6_raw) (finePart 7 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree8 : equalityCheck (finePart 8 contactSum6_raw) (finePart 8 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree9 : equalityCheck (finePart 9 contactSum6_raw) (finePart 9 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree10 : equalityCheck (finePart 10 contactSum6_raw) (finePart 10 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree11 : equalityCheck (finePart 11 contactSum6_raw) (finePart 11 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree12 : equalityCheck (finePart 12 contactSum6_raw) (finePart 12 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree13 : equalityCheck (finePart 13 contactSum6_raw) (finePart 13 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree14 : equalityCheck (finePart 14 contactSum6_raw) (finePart 14 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree15 : equalityCheck (finePart 15 contactSum6_raw) (finePart 15 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree16 : equalityCheck (finePart 16 contactSum6_raw) (finePart 16 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree17 : equalityCheck (finePart 17 contactSum6_raw) (finePart 17 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree18 : equalityCheck (finePart 18 contactSum6_raw) (finePart 18 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree19 : equalityCheck (finePart 19 contactSum6_raw) (finePart 19 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree20 : equalityCheck (finePart 20 contactSum6_raw) (finePart 20 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree21 : equalityCheck (finePart 21 contactSum6_raw) (finePart 21 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree22 : equalityCheck (finePart 22 contactSum6_raw) (finePart 22 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree23 : equalityCheck (finePart 23 contactSum6_raw) (finePart 23 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree24 : equalityCheck (finePart 24 contactSum6_raw) (finePart 24 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree25 : equalityCheck (finePart 25 contactSum6_raw) (finePart 25 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree26 : equalityCheck (finePart 26 contactSum6_raw) (finePart 26 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree27 : equalityCheck (finePart 27 contactSum6_raw) (finePart 27 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree28 : equalityCheck (finePart 28 contactSum6_raw) (finePart 28 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree29 : equalityCheck (finePart 29 contactSum6_raw) (finePart 29 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree30 : equalityCheck (finePart 30 contactSum6_raw) (finePart 30 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree31 : equalityCheck (finePart 31 contactSum6_raw) (finePart 31 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree32 : equalityCheck (finePart 32 contactSum6_raw) (finePart 32 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree33 : equalityCheck (finePart 33 contactSum6_raw) (finePart 33 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree34 : equalityCheck (finePart 34 contactSum6_raw) (finePart 34 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree35 : equalityCheck (finePart 35 contactSum6_raw) (finePart 35 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree36 : equalityCheck (finePart 36 contactSum6_raw) (finePart 36 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree37 : equalityCheck (finePart 37 contactSum6_raw) (finePart 37 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree38 : equalityCheck (finePart 38 contactSum6_raw) (finePart 38 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree39 : equalityCheck (finePart 39 contactSum6_raw) (finePart 39 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree40 : equalityCheck (finePart 40 contactSum6_raw) (finePart 40 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree41 : equalityCheck (finePart 41 contactSum6_raw) (finePart 41 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree42 : equalityCheck (finePart 42 contactSum6_raw) (finePart 42 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree43 : equalityCheck (finePart 43 contactSum6_raw) (finePart 43 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree44 : equalityCheck (finePart 44 contactSum6_raw) (finePart 44 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree45 : equalityCheck (finePart 45 contactSum6_raw) (finePart 45 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree46 : equalityCheck (finePart 46 contactSum6_raw) (finePart 46 contactSum6) = true := by
  decide +kernel

theorem contactSum6_degree47 : equalityCheck (finePart 47 contactSum6_raw) (finePart 47 contactSum6) = true := by
  decide +kernel


end GeneralCK.Reflection.SmallBiasContactSum

end


