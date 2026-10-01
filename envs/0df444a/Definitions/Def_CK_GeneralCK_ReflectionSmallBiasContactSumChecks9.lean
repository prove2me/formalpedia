-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionSmallBiasContactSumChecks9
-- name    : CK_GeneralCK_ReflectionSmallBiasContactSumChecks9
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T10:10:40.559884+00:00
-- url     : https://prove2.me/theorems/42b0149c-8889-4b31-88e6-4275a45567fd
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionSmallBiasContactSumChecks9` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionSmallBiasContactSumChecks9` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionSmallBiasContactSumChecks9` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionSmallBiasContactSumChecks9 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionSmallBiasContactSumChecks9.lean)

import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasContactSumData

-- ===== source module GeneralCK.ReflectionSmallBiasContactSumChecks9 =====
section

namespace GeneralCK.Reflection.SmallBiasContactSum

open SmallBiasPolynomial SmallBiasJet SmallBiasPerspectiveJet
open SmallBiasContactDegrees SmallBiasHalfSumPowers SmallBiasBivariateBase

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem contactSum20_raw_bound : fineBound 48 contactSum20_raw = true := by
  decide +kernel

theorem contactSum20_result_bound : fineBound 48 contactSum20 = true := by
  decide +kernel

theorem contactSum20_degree0 : equalityCheck (finePart 0 contactSum20_raw) (finePart 0 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree1 : equalityCheck (finePart 1 contactSum20_raw) (finePart 1 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree2 : equalityCheck (finePart 2 contactSum20_raw) (finePart 2 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree3 : equalityCheck (finePart 3 contactSum20_raw) (finePart 3 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree4 : equalityCheck (finePart 4 contactSum20_raw) (finePart 4 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree5 : equalityCheck (finePart 5 contactSum20_raw) (finePart 5 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree6 : equalityCheck (finePart 6 contactSum20_raw) (finePart 6 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree7 : equalityCheck (finePart 7 contactSum20_raw) (finePart 7 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree8 : equalityCheck (finePart 8 contactSum20_raw) (finePart 8 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree9 : equalityCheck (finePart 9 contactSum20_raw) (finePart 9 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree10 : equalityCheck (finePart 10 contactSum20_raw) (finePart 10 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree11 : equalityCheck (finePart 11 contactSum20_raw) (finePart 11 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree12 : equalityCheck (finePart 12 contactSum20_raw) (finePart 12 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree13 : equalityCheck (finePart 13 contactSum20_raw) (finePart 13 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree14 : equalityCheck (finePart 14 contactSum20_raw) (finePart 14 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree15 : equalityCheck (finePart 15 contactSum20_raw) (finePart 15 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree16 : equalityCheck (finePart 16 contactSum20_raw) (finePart 16 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree17 : equalityCheck (finePart 17 contactSum20_raw) (finePart 17 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree18 : equalityCheck (finePart 18 contactSum20_raw) (finePart 18 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree19 : equalityCheck (finePart 19 contactSum20_raw) (finePart 19 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree20 : equalityCheck (finePart 20 contactSum20_raw) (finePart 20 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree21 : equalityCheck (finePart 21 contactSum20_raw) (finePart 21 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree22 : equalityCheck (finePart 22 contactSum20_raw) (finePart 22 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree23 : equalityCheck (finePart 23 contactSum20_raw) (finePart 23 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree24 : equalityCheck (finePart 24 contactSum20_raw) (finePart 24 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree25 : equalityCheck (finePart 25 contactSum20_raw) (finePart 25 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree26 : equalityCheck (finePart 26 contactSum20_raw) (finePart 26 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree27 : equalityCheck (finePart 27 contactSum20_raw) (finePart 27 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree28 : equalityCheck (finePart 28 contactSum20_raw) (finePart 28 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree29 : equalityCheck (finePart 29 contactSum20_raw) (finePart 29 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree30 : equalityCheck (finePart 30 contactSum20_raw) (finePart 30 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree31 : equalityCheck (finePart 31 contactSum20_raw) (finePart 31 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree32 : equalityCheck (finePart 32 contactSum20_raw) (finePart 32 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree33 : equalityCheck (finePart 33 contactSum20_raw) (finePart 33 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree34 : equalityCheck (finePart 34 contactSum20_raw) (finePart 34 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree35 : equalityCheck (finePart 35 contactSum20_raw) (finePart 35 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree36 : equalityCheck (finePart 36 contactSum20_raw) (finePart 36 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree37 : equalityCheck (finePart 37 contactSum20_raw) (finePart 37 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree38 : equalityCheck (finePart 38 contactSum20_raw) (finePart 38 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree39 : equalityCheck (finePart 39 contactSum20_raw) (finePart 39 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree40 : equalityCheck (finePart 40 contactSum20_raw) (finePart 40 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree41 : equalityCheck (finePart 41 contactSum20_raw) (finePart 41 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree42 : equalityCheck (finePart 42 contactSum20_raw) (finePart 42 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree43 : equalityCheck (finePart 43 contactSum20_raw) (finePart 43 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree44 : equalityCheck (finePart 44 contactSum20_raw) (finePart 44 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree45 : equalityCheck (finePart 45 contactSum20_raw) (finePart 45 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree46 : equalityCheck (finePart 46 contactSum20_raw) (finePart 46 contactSum20) = true := by
  decide +kernel

theorem contactSum20_degree47 : equalityCheck (finePart 47 contactSum20_raw) (finePart 47 contactSum20) = true := by
  decide +kernel


end GeneralCK.Reflection.SmallBiasContactSum

end


