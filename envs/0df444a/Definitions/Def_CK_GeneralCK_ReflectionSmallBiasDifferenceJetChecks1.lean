-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionSmallBiasDifferenceJetChecks1
-- name    : CK_GeneralCK_ReflectionSmallBiasDifferenceJetChecks1
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T07:25:48.754982+00:00
-- url     : https://prove2.me/theorems/69378c27-8fe5-4b0e-904f-d744b79487d1
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionSmallBiasDifferenceJetChecks1` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionSmallBiasDifferenceJetChecks1` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionSmallBiasDifferenceJetChecks1` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionSmallBiasDifferenceJetChecks1 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionSmallBiasDifferenceJetChecks1.lean)

import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasDifferenceJetData

-- ===== source module GeneralCK.ReflectionSmallBiasDifferenceJetChecks1 =====
section

namespace GeneralCK.Reflection.SmallBiasDifferenceJet

open Filter Asymptotics SmallBiasPolynomial SmallBiasJet SmallBiasDifferenceTable
open SmallBiasHalfSumPowers SmallBiasBivariateBase SmallBiasContactSum
open scoped Topology

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem preDifference_raw_bound : fineBound 48 preDifference_raw = true := by
  decide +kernel

theorem preDifference_result_bound : fineBound 48 preDifference = true := by
  decide +kernel

theorem preDifference_degree0 : equalityCheck (finePart 0 preDifference_raw) (finePart 0 preDifference) = true := by
  decide +kernel

theorem preDifference_degree1 : equalityCheck (finePart 1 preDifference_raw) (finePart 1 preDifference) = true := by
  decide +kernel

theorem preDifference_degree2 : equalityCheck (finePart 2 preDifference_raw) (finePart 2 preDifference) = true := by
  decide +kernel

theorem preDifference_degree3 : equalityCheck (finePart 3 preDifference_raw) (finePart 3 preDifference) = true := by
  decide +kernel

theorem preDifference_degree4 : equalityCheck (finePart 4 preDifference_raw) (finePart 4 preDifference) = true := by
  decide +kernel

theorem preDifference_degree5 : equalityCheck (finePart 5 preDifference_raw) (finePart 5 preDifference) = true := by
  decide +kernel

theorem preDifference_degree6 : equalityCheck (finePart 6 preDifference_raw) (finePart 6 preDifference) = true := by
  decide +kernel

theorem preDifference_degree7 : equalityCheck (finePart 7 preDifference_raw) (finePart 7 preDifference) = true := by
  decide +kernel

theorem preDifference_degree8 : equalityCheck (finePart 8 preDifference_raw) (finePart 8 preDifference) = true := by
  decide +kernel

theorem preDifference_degree9 : equalityCheck (finePart 9 preDifference_raw) (finePart 9 preDifference) = true := by
  decide +kernel

theorem preDifference_degree10 : equalityCheck (finePart 10 preDifference_raw) (finePart 10 preDifference) = true := by
  decide +kernel

theorem preDifference_degree11 : equalityCheck (finePart 11 preDifference_raw) (finePart 11 preDifference) = true := by
  decide +kernel

theorem preDifference_degree12 : equalityCheck (finePart 12 preDifference_raw) (finePart 12 preDifference) = true := by
  decide +kernel

theorem preDifference_degree13 : equalityCheck (finePart 13 preDifference_raw) (finePart 13 preDifference) = true := by
  decide +kernel

theorem preDifference_degree14 : equalityCheck (finePart 14 preDifference_raw) (finePart 14 preDifference) = true := by
  decide +kernel

theorem preDifference_degree15 : equalityCheck (finePart 15 preDifference_raw) (finePart 15 preDifference) = true := by
  decide +kernel

theorem preDifference_degree16 : equalityCheck (finePart 16 preDifference_raw) (finePart 16 preDifference) = true := by
  decide +kernel

theorem preDifference_degree17 : equalityCheck (finePart 17 preDifference_raw) (finePart 17 preDifference) = true := by
  decide +kernel

theorem preDifference_degree18 : equalityCheck (finePart 18 preDifference_raw) (finePart 18 preDifference) = true := by
  decide +kernel

theorem preDifference_degree19 : equalityCheck (finePart 19 preDifference_raw) (finePart 19 preDifference) = true := by
  decide +kernel

theorem preDifference_degree20 : equalityCheck (finePart 20 preDifference_raw) (finePart 20 preDifference) = true := by
  decide +kernel

theorem preDifference_degree21 : equalityCheck (finePart 21 preDifference_raw) (finePart 21 preDifference) = true := by
  decide +kernel

theorem preDifference_degree22 : equalityCheck (finePart 22 preDifference_raw) (finePart 22 preDifference) = true := by
  decide +kernel

theorem preDifference_degree23 : equalityCheck (finePart 23 preDifference_raw) (finePart 23 preDifference) = true := by
  decide +kernel

theorem preDifference_degree24 : equalityCheck (finePart 24 preDifference_raw) (finePart 24 preDifference) = true := by
  decide +kernel

theorem preDifference_degree25 : equalityCheck (finePart 25 preDifference_raw) (finePart 25 preDifference) = true := by
  decide +kernel

theorem preDifference_degree26 : equalityCheck (finePart 26 preDifference_raw) (finePart 26 preDifference) = true := by
  decide +kernel

theorem preDifference_degree27 : equalityCheck (finePart 27 preDifference_raw) (finePart 27 preDifference) = true := by
  decide +kernel

theorem preDifference_degree28 : equalityCheck (finePart 28 preDifference_raw) (finePart 28 preDifference) = true := by
  decide +kernel

theorem preDifference_degree29 : equalityCheck (finePart 29 preDifference_raw) (finePart 29 preDifference) = true := by
  decide +kernel

theorem preDifference_degree30 : equalityCheck (finePart 30 preDifference_raw) (finePart 30 preDifference) = true := by
  decide +kernel

theorem preDifference_degree31 : equalityCheck (finePart 31 preDifference_raw) (finePart 31 preDifference) = true := by
  decide +kernel

theorem preDifference_degree32 : equalityCheck (finePart 32 preDifference_raw) (finePart 32 preDifference) = true := by
  decide +kernel

theorem preDifference_degree33 : equalityCheck (finePart 33 preDifference_raw) (finePart 33 preDifference) = true := by
  decide +kernel

theorem preDifference_degree34 : equalityCheck (finePart 34 preDifference_raw) (finePart 34 preDifference) = true := by
  decide +kernel

theorem preDifference_degree35 : equalityCheck (finePart 35 preDifference_raw) (finePart 35 preDifference) = true := by
  decide +kernel

theorem preDifference_degree36 : equalityCheck (finePart 36 preDifference_raw) (finePart 36 preDifference) = true := by
  decide +kernel

theorem preDifference_degree37 : equalityCheck (finePart 37 preDifference_raw) (finePart 37 preDifference) = true := by
  decide +kernel

theorem preDifference_degree38 : equalityCheck (finePart 38 preDifference_raw) (finePart 38 preDifference) = true := by
  decide +kernel

theorem preDifference_degree39 : equalityCheck (finePart 39 preDifference_raw) (finePart 39 preDifference) = true := by
  decide +kernel

theorem preDifference_degree40 : equalityCheck (finePart 40 preDifference_raw) (finePart 40 preDifference) = true := by
  decide +kernel

theorem preDifference_degree41 : equalityCheck (finePart 41 preDifference_raw) (finePart 41 preDifference) = true := by
  decide +kernel

theorem preDifference_degree42 : equalityCheck (finePart 42 preDifference_raw) (finePart 42 preDifference) = true := by
  decide +kernel

theorem preDifference_degree43 : equalityCheck (finePart 43 preDifference_raw) (finePart 43 preDifference) = true := by
  decide +kernel

theorem preDifference_degree44 : equalityCheck (finePart 44 preDifference_raw) (finePart 44 preDifference) = true := by
  decide +kernel

theorem preDifference_degree45 : equalityCheck (finePart 45 preDifference_raw) (finePart 45 preDifference) = true := by
  decide +kernel

theorem preDifference_degree46 : equalityCheck (finePart 46 preDifference_raw) (finePart 46 preDifference) = true := by
  decide +kernel

theorem preDifference_degree47 : equalityCheck (finePart 47 preDifference_raw) (finePart 47 preDifference) = true := by
  decide +kernel


end GeneralCK.Reflection.SmallBiasDifferenceJet

end


