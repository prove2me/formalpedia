-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionSmallBiasContactSumChecks3
-- name    : CK_GeneralCK_ReflectionSmallBiasContactSumChecks3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T10:10:33.102088+00:00
-- url     : https://prove2.me/theorems/7c237749-5ad2-40fa-a336-583fad2bcb1c
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionSmallBiasContactSumChecks3` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionSmallBiasContactSumChecks3` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionSmallBiasContactSumChecks3` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionSmallBiasContactSumChecks3 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionSmallBiasContactSumChecks3.lean)

import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasContactSumData

-- ===== source module GeneralCK.ReflectionSmallBiasContactSumChecks3 =====
section

namespace GeneralCK.Reflection.SmallBiasContactSum

open SmallBiasPolynomial SmallBiasJet SmallBiasPerspectiveJet
open SmallBiasContactDegrees SmallBiasHalfSumPowers SmallBiasBivariateBase

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem contactSum8_raw_bound : fineBound 48 contactSum8_raw = true := by
  decide +kernel

theorem contactSum8_result_bound : fineBound 48 contactSum8 = true := by
  decide +kernel

theorem contactSum8_degree0 : equalityCheck (finePart 0 contactSum8_raw) (finePart 0 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree1 : equalityCheck (finePart 1 contactSum8_raw) (finePart 1 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree2 : equalityCheck (finePart 2 contactSum8_raw) (finePart 2 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree3 : equalityCheck (finePart 3 contactSum8_raw) (finePart 3 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree4 : equalityCheck (finePart 4 contactSum8_raw) (finePart 4 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree5 : equalityCheck (finePart 5 contactSum8_raw) (finePart 5 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree6 : equalityCheck (finePart 6 contactSum8_raw) (finePart 6 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree7 : equalityCheck (finePart 7 contactSum8_raw) (finePart 7 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree8 : equalityCheck (finePart 8 contactSum8_raw) (finePart 8 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree9 : equalityCheck (finePart 9 contactSum8_raw) (finePart 9 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree10 : equalityCheck (finePart 10 contactSum8_raw) (finePart 10 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree11 : equalityCheck (finePart 11 contactSum8_raw) (finePart 11 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree12 : equalityCheck (finePart 12 contactSum8_raw) (finePart 12 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree13 : equalityCheck (finePart 13 contactSum8_raw) (finePart 13 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree14 : equalityCheck (finePart 14 contactSum8_raw) (finePart 14 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree15 : equalityCheck (finePart 15 contactSum8_raw) (finePart 15 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree16 : equalityCheck (finePart 16 contactSum8_raw) (finePart 16 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree17 : equalityCheck (finePart 17 contactSum8_raw) (finePart 17 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree18 : equalityCheck (finePart 18 contactSum8_raw) (finePart 18 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree19 : equalityCheck (finePart 19 contactSum8_raw) (finePart 19 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree20 : equalityCheck (finePart 20 contactSum8_raw) (finePart 20 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree21 : equalityCheck (finePart 21 contactSum8_raw) (finePart 21 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree22 : equalityCheck (finePart 22 contactSum8_raw) (finePart 22 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree23 : equalityCheck (finePart 23 contactSum8_raw) (finePart 23 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree24 : equalityCheck (finePart 24 contactSum8_raw) (finePart 24 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree25 : equalityCheck (finePart 25 contactSum8_raw) (finePart 25 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree26 : equalityCheck (finePart 26 contactSum8_raw) (finePart 26 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree27 : equalityCheck (finePart 27 contactSum8_raw) (finePart 27 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree28 : equalityCheck (finePart 28 contactSum8_raw) (finePart 28 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree29 : equalityCheck (finePart 29 contactSum8_raw) (finePart 29 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree30 : equalityCheck (finePart 30 contactSum8_raw) (finePart 30 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree31 : equalityCheck (finePart 31 contactSum8_raw) (finePart 31 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree32 : equalityCheck (finePart 32 contactSum8_raw) (finePart 32 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree33 : equalityCheck (finePart 33 contactSum8_raw) (finePart 33 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree34 : equalityCheck (finePart 34 contactSum8_raw) (finePart 34 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree35 : equalityCheck (finePart 35 contactSum8_raw) (finePart 35 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree36 : equalityCheck (finePart 36 contactSum8_raw) (finePart 36 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree37 : equalityCheck (finePart 37 contactSum8_raw) (finePart 37 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree38 : equalityCheck (finePart 38 contactSum8_raw) (finePart 38 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree39 : equalityCheck (finePart 39 contactSum8_raw) (finePart 39 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree40 : equalityCheck (finePart 40 contactSum8_raw) (finePart 40 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree41 : equalityCheck (finePart 41 contactSum8_raw) (finePart 41 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree42 : equalityCheck (finePart 42 contactSum8_raw) (finePart 42 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree43 : equalityCheck (finePart 43 contactSum8_raw) (finePart 43 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree44 : equalityCheck (finePart 44 contactSum8_raw) (finePart 44 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree45 : equalityCheck (finePart 45 contactSum8_raw) (finePart 45 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree46 : equalityCheck (finePart 46 contactSum8_raw) (finePart 46 contactSum8) = true := by
  decide +kernel

theorem contactSum8_degree47 : equalityCheck (finePart 47 contactSum8_raw) (finePart 47 contactSum8) = true := by
  decide +kernel


end GeneralCK.Reflection.SmallBiasContactSum

end


