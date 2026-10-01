-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionSmallBiasContactSumChecks1
-- name    : CK_GeneralCK_ReflectionSmallBiasContactSumChecks1
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T10:09:11.838053+00:00
-- url     : https://prove2.me/theorems/5848cc5f-0496-4c7f-a2c9-3b2cc57f0734
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionSmallBiasContactSumChecks1` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionSmallBiasContactSumChecks1` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionSmallBiasContactSumChecks1` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionSmallBiasContactSumChecks1 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionSmallBiasContactSumChecks1.lean)

import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasContactSumData

-- ===== source module GeneralCK.ReflectionSmallBiasContactSumChecks1 =====
section

namespace GeneralCK.Reflection.SmallBiasContactSum

open SmallBiasPolynomial SmallBiasJet SmallBiasPerspectiveJet
open SmallBiasContactDegrees SmallBiasHalfSumPowers SmallBiasBivariateBase

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem contactSum4_raw_bound : fineBound 48 contactSum4_raw = true := by
  decide +kernel

theorem contactSum4_result_bound : fineBound 48 contactSum4 = true := by
  decide +kernel

theorem contactSum4_degree0 : equalityCheck (finePart 0 contactSum4_raw) (finePart 0 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree1 : equalityCheck (finePart 1 contactSum4_raw) (finePart 1 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree2 : equalityCheck (finePart 2 contactSum4_raw) (finePart 2 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree3 : equalityCheck (finePart 3 contactSum4_raw) (finePart 3 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree4 : equalityCheck (finePart 4 contactSum4_raw) (finePart 4 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree5 : equalityCheck (finePart 5 contactSum4_raw) (finePart 5 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree6 : equalityCheck (finePart 6 contactSum4_raw) (finePart 6 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree7 : equalityCheck (finePart 7 contactSum4_raw) (finePart 7 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree8 : equalityCheck (finePart 8 contactSum4_raw) (finePart 8 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree9 : equalityCheck (finePart 9 contactSum4_raw) (finePart 9 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree10 : equalityCheck (finePart 10 contactSum4_raw) (finePart 10 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree11 : equalityCheck (finePart 11 contactSum4_raw) (finePart 11 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree12 : equalityCheck (finePart 12 contactSum4_raw) (finePart 12 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree13 : equalityCheck (finePart 13 contactSum4_raw) (finePart 13 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree14 : equalityCheck (finePart 14 contactSum4_raw) (finePart 14 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree15 : equalityCheck (finePart 15 contactSum4_raw) (finePart 15 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree16 : equalityCheck (finePart 16 contactSum4_raw) (finePart 16 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree17 : equalityCheck (finePart 17 contactSum4_raw) (finePart 17 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree18 : equalityCheck (finePart 18 contactSum4_raw) (finePart 18 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree19 : equalityCheck (finePart 19 contactSum4_raw) (finePart 19 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree20 : equalityCheck (finePart 20 contactSum4_raw) (finePart 20 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree21 : equalityCheck (finePart 21 contactSum4_raw) (finePart 21 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree22 : equalityCheck (finePart 22 contactSum4_raw) (finePart 22 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree23 : equalityCheck (finePart 23 contactSum4_raw) (finePart 23 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree24 : equalityCheck (finePart 24 contactSum4_raw) (finePart 24 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree25 : equalityCheck (finePart 25 contactSum4_raw) (finePart 25 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree26 : equalityCheck (finePart 26 contactSum4_raw) (finePart 26 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree27 : equalityCheck (finePart 27 contactSum4_raw) (finePart 27 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree28 : equalityCheck (finePart 28 contactSum4_raw) (finePart 28 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree29 : equalityCheck (finePart 29 contactSum4_raw) (finePart 29 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree30 : equalityCheck (finePart 30 contactSum4_raw) (finePart 30 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree31 : equalityCheck (finePart 31 contactSum4_raw) (finePart 31 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree32 : equalityCheck (finePart 32 contactSum4_raw) (finePart 32 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree33 : equalityCheck (finePart 33 contactSum4_raw) (finePart 33 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree34 : equalityCheck (finePart 34 contactSum4_raw) (finePart 34 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree35 : equalityCheck (finePart 35 contactSum4_raw) (finePart 35 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree36 : equalityCheck (finePart 36 contactSum4_raw) (finePart 36 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree37 : equalityCheck (finePart 37 contactSum4_raw) (finePart 37 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree38 : equalityCheck (finePart 38 contactSum4_raw) (finePart 38 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree39 : equalityCheck (finePart 39 contactSum4_raw) (finePart 39 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree40 : equalityCheck (finePart 40 contactSum4_raw) (finePart 40 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree41 : equalityCheck (finePart 41 contactSum4_raw) (finePart 41 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree42 : equalityCheck (finePart 42 contactSum4_raw) (finePart 42 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree43 : equalityCheck (finePart 43 contactSum4_raw) (finePart 43 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree44 : equalityCheck (finePart 44 contactSum4_raw) (finePart 44 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree45 : equalityCheck (finePart 45 contactSum4_raw) (finePart 45 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree46 : equalityCheck (finePart 46 contactSum4_raw) (finePart 46 contactSum4) = true := by
  decide +kernel

theorem contactSum4_degree47 : equalityCheck (finePart 47 contactSum4_raw) (finePart 47 contactSum4) = true := by
  decide +kernel


end GeneralCK.Reflection.SmallBiasContactSum

end


