-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree10Checks1
-- name    : CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree10Checks1
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T23:14:53.368819+00:00
-- url     : https://prove2.me/theorems/eda21afa-3468-44af-84fe-b281ea8aff16
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree10Checks1` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree10Checks1` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree10Checks1` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.ReflectionSmallBiasContactDegree10Checks1 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/ReflectionSmallBiasContactDegree10Checks1.lean)

import Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree10Data

-- ===== source module GeneralCK.Certificates.ReflectionSmallBiasContactDegree10Checks1 =====
section

namespace GeneralCK.Reflection.SmallBiasContactDegrees

open SmallBiasPolynomial SmallBiasJet SmallBiasPerspectiveJet
open SmallBiasHalfSumPowers SmallBiasBivariateBase SmallBiasBivariateInverse

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem body10_raw_bound : fineBound 48 body10_raw = true := by
  decide +kernel

theorem body10_result_bound : fineBound 48 body10 = true := by
  decide +kernel

theorem body10_degree0 : equalityCheck (finePart 0 body10_raw) (finePart 0 body10) = true := by
  decide +kernel

theorem body10_degree1 : equalityCheck (finePart 1 body10_raw) (finePart 1 body10) = true := by
  decide +kernel

theorem body10_degree2 : equalityCheck (finePart 2 body10_raw) (finePart 2 body10) = true := by
  decide +kernel

theorem body10_degree3 : equalityCheck (finePart 3 body10_raw) (finePart 3 body10) = true := by
  decide +kernel

theorem body10_degree4 : equalityCheck (finePart 4 body10_raw) (finePart 4 body10) = true := by
  decide +kernel

theorem body10_degree5 : equalityCheck (finePart 5 body10_raw) (finePart 5 body10) = true := by
  decide +kernel

theorem body10_degree6 : equalityCheck (finePart 6 body10_raw) (finePart 6 body10) = true := by
  decide +kernel

theorem body10_degree7 : equalityCheck (finePart 7 body10_raw) (finePart 7 body10) = true := by
  decide +kernel

theorem body10_degree8 : equalityCheck (finePart 8 body10_raw) (finePart 8 body10) = true := by
  decide +kernel

theorem body10_degree9 : equalityCheck (finePart 9 body10_raw) (finePart 9 body10) = true := by
  decide +kernel

theorem body10_degree10 : equalityCheck (finePart 10 body10_raw) (finePart 10 body10) = true := by
  decide +kernel

theorem body10_degree11 : equalityCheck (finePart 11 body10_raw) (finePart 11 body10) = true := by
  decide +kernel

theorem body10_degree12 : equalityCheck (finePart 12 body10_raw) (finePart 12 body10) = true := by
  decide +kernel

theorem body10_degree13 : equalityCheck (finePart 13 body10_raw) (finePart 13 body10) = true := by
  decide +kernel

theorem body10_degree14 : equalityCheck (finePart 14 body10_raw) (finePart 14 body10) = true := by
  decide +kernel

theorem body10_degree15 : equalityCheck (finePart 15 body10_raw) (finePart 15 body10) = true := by
  decide +kernel

theorem body10_degree16 : equalityCheck (finePart 16 body10_raw) (finePart 16 body10) = true := by
  decide +kernel

theorem body10_degree17 : equalityCheck (finePart 17 body10_raw) (finePart 17 body10) = true := by
  decide +kernel

theorem body10_degree18 : equalityCheck (finePart 18 body10_raw) (finePart 18 body10) = true := by
  decide +kernel

theorem body10_degree19 : equalityCheck (finePart 19 body10_raw) (finePart 19 body10) = true := by
  decide +kernel

theorem body10_degree20 : equalityCheck (finePart 20 body10_raw) (finePart 20 body10) = true := by
  decide +kernel

theorem body10_degree21 : equalityCheck (finePart 21 body10_raw) (finePart 21 body10) = true := by
  decide +kernel

theorem body10_degree22 : equalityCheck (finePart 22 body10_raw) (finePart 22 body10) = true := by
  decide +kernel

theorem body10_degree23 : equalityCheck (finePart 23 body10_raw) (finePart 23 body10) = true := by
  decide +kernel

theorem body10_degree24 : equalityCheck (finePart 24 body10_raw) (finePart 24 body10) = true := by
  decide +kernel

theorem body10_degree25 : equalityCheck (finePart 25 body10_raw) (finePart 25 body10) = true := by
  decide +kernel

theorem body10_degree26 : equalityCheck (finePart 26 body10_raw) (finePart 26 body10) = true := by
  decide +kernel

theorem body10_degree27 : equalityCheck (finePart 27 body10_raw) (finePart 27 body10) = true := by
  decide +kernel

theorem body10_degree28 : equalityCheck (finePart 28 body10_raw) (finePart 28 body10) = true := by
  decide +kernel

theorem body10_degree29 : equalityCheck (finePart 29 body10_raw) (finePart 29 body10) = true := by
  decide +kernel

theorem body10_degree30 : equalityCheck (finePart 30 body10_raw) (finePart 30 body10) = true := by
  decide +kernel

theorem body10_degree31 : equalityCheck (finePart 31 body10_raw) (finePart 31 body10) = true := by
  decide +kernel

theorem body10_degree32 : equalityCheck (finePart 32 body10_raw) (finePart 32 body10) = true := by
  decide +kernel

theorem body10_degree33 : equalityCheck (finePart 33 body10_raw) (finePart 33 body10) = true := by
  decide +kernel

theorem body10_degree34 : equalityCheck (finePart 34 body10_raw) (finePart 34 body10) = true := by
  decide +kernel

theorem body10_degree35 : equalityCheck (finePart 35 body10_raw) (finePart 35 body10) = true := by
  decide +kernel

theorem body10_degree36 : equalityCheck (finePart 36 body10_raw) (finePart 36 body10) = true := by
  decide +kernel

theorem body10_degree37 : equalityCheck (finePart 37 body10_raw) (finePart 37 body10) = true := by
  decide +kernel

theorem body10_degree38 : equalityCheck (finePart 38 body10_raw) (finePart 38 body10) = true := by
  decide +kernel

theorem body10_degree39 : equalityCheck (finePart 39 body10_raw) (finePart 39 body10) = true := by
  decide +kernel

theorem body10_degree40 : equalityCheck (finePart 40 body10_raw) (finePart 40 body10) = true := by
  decide +kernel

theorem body10_degree41 : equalityCheck (finePart 41 body10_raw) (finePart 41 body10) = true := by
  decide +kernel

theorem body10_degree42 : equalityCheck (finePart 42 body10_raw) (finePart 42 body10) = true := by
  decide +kernel

theorem body10_degree43 : equalityCheck (finePart 43 body10_raw) (finePart 43 body10) = true := by
  decide +kernel

theorem body10_degree44 : equalityCheck (finePart 44 body10_raw) (finePart 44 body10) = true := by
  decide +kernel

theorem body10_degree45 : equalityCheck (finePart 45 body10_raw) (finePart 45 body10) = true := by
  decide +kernel

theorem body10_degree46 : equalityCheck (finePart 46 body10_raw) (finePart 46 body10) = true := by
  decide +kernel

theorem body10_degree47 : equalityCheck (finePart 47 body10_raw) (finePart 47 body10) = true := by
  decide +kernel


end GeneralCK.Reflection.SmallBiasContactDegrees

end


