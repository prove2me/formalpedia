-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree20Checks2
-- name    : CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree20Checks2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T02:14:08.593276+00:00
-- url     : https://prove2.me/theorems/3d026428-6df2-4f5d-aca4-9c748ea72757
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree20Checks2` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree20Checks2` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree20Checks2` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.ReflectionSmallBiasContactDegree20Checks2 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/ReflectionSmallBiasContactDegree20Checks2.lean)

import Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree20Data

-- ===== source module GeneralCK.Certificates.ReflectionSmallBiasContactDegree20Checks2 =====
section

namespace GeneralCK.Reflection.SmallBiasContactDegrees

open SmallBiasPolynomial SmallBiasJet SmallBiasPerspectiveJet
open SmallBiasHalfSumPowers SmallBiasBivariateBase SmallBiasBivariateInverse

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem group20_raw_bound : fineBound 48 group20_raw = true := by
  decide +kernel

theorem group20_result_bound : fineBound 48 group20 = true := by
  decide +kernel

theorem group20_degree0 : equalityCheck (finePart 0 group20_raw) (finePart 0 group20) = true := by
  decide +kernel

theorem group20_degree1 : equalityCheck (finePart 1 group20_raw) (finePart 1 group20) = true := by
  decide +kernel

theorem group20_degree2 : equalityCheck (finePart 2 group20_raw) (finePart 2 group20) = true := by
  decide +kernel

theorem group20_degree3 : equalityCheck (finePart 3 group20_raw) (finePart 3 group20) = true := by
  decide +kernel

theorem group20_degree4 : equalityCheck (finePart 4 group20_raw) (finePart 4 group20) = true := by
  decide +kernel

theorem group20_degree5 : equalityCheck (finePart 5 group20_raw) (finePart 5 group20) = true := by
  decide +kernel

theorem group20_degree6 : equalityCheck (finePart 6 group20_raw) (finePart 6 group20) = true := by
  decide +kernel

theorem group20_degree7 : equalityCheck (finePart 7 group20_raw) (finePart 7 group20) = true := by
  decide +kernel

theorem group20_degree8 : equalityCheck (finePart 8 group20_raw) (finePart 8 group20) = true := by
  decide +kernel

theorem group20_degree9 : equalityCheck (finePart 9 group20_raw) (finePart 9 group20) = true := by
  decide +kernel

theorem group20_degree10 : equalityCheck (finePart 10 group20_raw) (finePart 10 group20) = true := by
  decide +kernel

theorem group20_degree11 : equalityCheck (finePart 11 group20_raw) (finePart 11 group20) = true := by
  decide +kernel

theorem group20_degree12 : equalityCheck (finePart 12 group20_raw) (finePart 12 group20) = true := by
  decide +kernel

theorem group20_degree13 : equalityCheck (finePart 13 group20_raw) (finePart 13 group20) = true := by
  decide +kernel

theorem group20_degree14 : equalityCheck (finePart 14 group20_raw) (finePart 14 group20) = true := by
  decide +kernel

theorem group20_degree15 : equalityCheck (finePart 15 group20_raw) (finePart 15 group20) = true := by
  decide +kernel

theorem group20_degree16 : equalityCheck (finePart 16 group20_raw) (finePart 16 group20) = true := by
  decide +kernel

theorem group20_degree17 : equalityCheck (finePart 17 group20_raw) (finePart 17 group20) = true := by
  decide +kernel

theorem group20_degree18 : equalityCheck (finePart 18 group20_raw) (finePart 18 group20) = true := by
  decide +kernel

theorem group20_degree19 : equalityCheck (finePart 19 group20_raw) (finePart 19 group20) = true := by
  decide +kernel

theorem group20_degree20 : equalityCheck (finePart 20 group20_raw) (finePart 20 group20) = true := by
  decide +kernel

theorem group20_degree21 : equalityCheck (finePart 21 group20_raw) (finePart 21 group20) = true := by
  decide +kernel

theorem group20_degree22 : equalityCheck (finePart 22 group20_raw) (finePart 22 group20) = true := by
  decide +kernel

theorem group20_degree23 : equalityCheck (finePart 23 group20_raw) (finePart 23 group20) = true := by
  decide +kernel

theorem group20_degree24 : equalityCheck (finePart 24 group20_raw) (finePart 24 group20) = true := by
  decide +kernel

theorem group20_degree25 : equalityCheck (finePart 25 group20_raw) (finePart 25 group20) = true := by
  decide +kernel

theorem group20_degree26 : equalityCheck (finePart 26 group20_raw) (finePart 26 group20) = true := by
  decide +kernel

theorem group20_degree27 : equalityCheck (finePart 27 group20_raw) (finePart 27 group20) = true := by
  decide +kernel

theorem group20_degree28 : equalityCheck (finePart 28 group20_raw) (finePart 28 group20) = true := by
  decide +kernel

theorem group20_degree29 : equalityCheck (finePart 29 group20_raw) (finePart 29 group20) = true := by
  decide +kernel

theorem group20_degree30 : equalityCheck (finePart 30 group20_raw) (finePart 30 group20) = true := by
  decide +kernel

theorem group20_degree31 : equalityCheck (finePart 31 group20_raw) (finePart 31 group20) = true := by
  decide +kernel

theorem group20_degree32 : equalityCheck (finePart 32 group20_raw) (finePart 32 group20) = true := by
  decide +kernel

theorem group20_degree33 : equalityCheck (finePart 33 group20_raw) (finePart 33 group20) = true := by
  decide +kernel

theorem group20_degree34 : equalityCheck (finePart 34 group20_raw) (finePart 34 group20) = true := by
  decide +kernel

theorem group20_degree35 : equalityCheck (finePart 35 group20_raw) (finePart 35 group20) = true := by
  decide +kernel

theorem group20_degree36 : equalityCheck (finePart 36 group20_raw) (finePart 36 group20) = true := by
  decide +kernel

theorem group20_degree37 : equalityCheck (finePart 37 group20_raw) (finePart 37 group20) = true := by
  decide +kernel

theorem group20_degree38 : equalityCheck (finePart 38 group20_raw) (finePart 38 group20) = true := by
  decide +kernel

theorem group20_degree39 : equalityCheck (finePart 39 group20_raw) (finePart 39 group20) = true := by
  decide +kernel

theorem group20_degree40 : equalityCheck (finePart 40 group20_raw) (finePart 40 group20) = true := by
  decide +kernel

theorem group20_degree41 : equalityCheck (finePart 41 group20_raw) (finePart 41 group20) = true := by
  decide +kernel

theorem group20_degree42 : equalityCheck (finePart 42 group20_raw) (finePart 42 group20) = true := by
  decide +kernel

theorem group20_degree43 : equalityCheck (finePart 43 group20_raw) (finePart 43 group20) = true := by
  decide +kernel

theorem group20_degree44 : equalityCheck (finePart 44 group20_raw) (finePart 44 group20) = true := by
  decide +kernel

theorem group20_degree45 : equalityCheck (finePart 45 group20_raw) (finePart 45 group20) = true := by
  decide +kernel

theorem group20_degree46 : equalityCheck (finePart 46 group20_raw) (finePart 46 group20) = true := by
  decide +kernel

theorem group20_degree47 : equalityCheck (finePart 47 group20_raw) (finePart 47 group20) = true := by
  decide +kernel


end GeneralCK.Reflection.SmallBiasContactDegrees

end


