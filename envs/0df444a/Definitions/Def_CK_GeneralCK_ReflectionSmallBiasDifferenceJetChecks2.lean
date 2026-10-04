-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionSmallBiasDifferenceJetChecks2
-- name    : CK_GeneralCK_ReflectionSmallBiasDifferenceJetChecks2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T12:34:03.155489+00:00
-- url     : https://prove2.me/theorems/42e73520-e435-4ade-ac7f-b6ebc6f6b155
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionSmallBiasDifferenceJetChecks2` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionSmallBiasDifferenceJetChecks2` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionSmallBiasDifferenceJetChecks2` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionSmallBiasDifferenceJetChecks2 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionSmallBiasDifferenceJetChecks2.lean)

import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasDifferenceJetData

-- ===== source module GeneralCK.ReflectionSmallBiasDifferenceJetChecks2 =====
section

namespace GeneralCK.Reflection.SmallBiasDifferenceJet

open Filter Asymptotics SmallBiasPolynomial SmallBiasJet SmallBiasDifferenceTable
open SmallBiasHalfSumPowers SmallBiasBivariateBase SmallBiasContactSum
open scoped Topology

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem difference_raw_bound : fineBound 48 difference_raw = true := by
  decide +kernel

theorem difference_result_bound : fineBound 48 candidateTable = true := by
  decide +kernel

theorem difference_degree0 : equalityCheck (finePart 0 difference_raw) (finePart 0 candidateTable) = true := by
  decide +kernel

theorem difference_degree1 : equalityCheck (finePart 1 difference_raw) (finePart 1 candidateTable) = true := by
  decide +kernel

theorem difference_degree2 : equalityCheck (finePart 2 difference_raw) (finePart 2 candidateTable) = true := by
  decide +kernel

theorem difference_degree3 : equalityCheck (finePart 3 difference_raw) (finePart 3 candidateTable) = true := by
  decide +kernel

theorem difference_degree4 : equalityCheck (finePart 4 difference_raw) (finePart 4 candidateTable) = true := by
  decide +kernel

theorem difference_degree5 : equalityCheck (finePart 5 difference_raw) (finePart 5 candidateTable) = true := by
  decide +kernel

theorem difference_degree6 : equalityCheck (finePart 6 difference_raw) (finePart 6 candidateTable) = true := by
  decide +kernel

theorem difference_degree7 : equalityCheck (finePart 7 difference_raw) (finePart 7 candidateTable) = true := by
  decide +kernel

theorem difference_degree8 : equalityCheck (finePart 8 difference_raw) (finePart 8 candidateTable) = true := by
  decide +kernel

theorem difference_degree9 : equalityCheck (finePart 9 difference_raw) (finePart 9 candidateTable) = true := by
  decide +kernel

theorem difference_degree10 : equalityCheck (finePart 10 difference_raw) (finePart 10 candidateTable) = true := by
  decide +kernel

theorem difference_degree11 : equalityCheck (finePart 11 difference_raw) (finePart 11 candidateTable) = true := by
  decide +kernel

theorem difference_degree12 : equalityCheck (finePart 12 difference_raw) (finePart 12 candidateTable) = true := by
  decide +kernel

theorem difference_degree13 : equalityCheck (finePart 13 difference_raw) (finePart 13 candidateTable) = true := by
  decide +kernel

theorem difference_degree14 : equalityCheck (finePart 14 difference_raw) (finePart 14 candidateTable) = true := by
  decide +kernel

theorem difference_degree15 : equalityCheck (finePart 15 difference_raw) (finePart 15 candidateTable) = true := by
  decide +kernel

theorem difference_degree16 : equalityCheck (finePart 16 difference_raw) (finePart 16 candidateTable) = true := by
  decide +kernel

theorem difference_degree17 : equalityCheck (finePart 17 difference_raw) (finePart 17 candidateTable) = true := by
  decide +kernel

theorem difference_degree18 : equalityCheck (finePart 18 difference_raw) (finePart 18 candidateTable) = true := by
  decide +kernel

theorem difference_degree19 : equalityCheck (finePart 19 difference_raw) (finePart 19 candidateTable) = true := by
  decide +kernel

theorem difference_degree20 : equalityCheck (finePart 20 difference_raw) (finePart 20 candidateTable) = true := by
  decide +kernel

theorem difference_degree21 : equalityCheck (finePart 21 difference_raw) (finePart 21 candidateTable) = true := by
  decide +kernel

theorem difference_degree22 : equalityCheck (finePart 22 difference_raw) (finePart 22 candidateTable) = true := by
  decide +kernel

theorem difference_degree23 : equalityCheck (finePart 23 difference_raw) (finePart 23 candidateTable) = true := by
  decide +kernel

theorem difference_degree24 : equalityCheck (finePart 24 difference_raw) (finePart 24 candidateTable) = true := by
  decide +kernel

theorem difference_degree25 : equalityCheck (finePart 25 difference_raw) (finePart 25 candidateTable) = true := by
  decide +kernel

theorem difference_degree26 : equalityCheck (finePart 26 difference_raw) (finePart 26 candidateTable) = true := by
  decide +kernel

theorem difference_degree27 : equalityCheck (finePart 27 difference_raw) (finePart 27 candidateTable) = true := by
  decide +kernel

theorem difference_degree28 : equalityCheck (finePart 28 difference_raw) (finePart 28 candidateTable) = true := by
  decide +kernel

theorem difference_degree29 : equalityCheck (finePart 29 difference_raw) (finePart 29 candidateTable) = true := by
  decide +kernel

theorem difference_degree30 : equalityCheck (finePart 30 difference_raw) (finePart 30 candidateTable) = true := by
  decide +kernel

theorem difference_degree31 : equalityCheck (finePart 31 difference_raw) (finePart 31 candidateTable) = true := by
  decide +kernel

theorem difference_degree32 : equalityCheck (finePart 32 difference_raw) (finePart 32 candidateTable) = true := by
  decide +kernel

theorem difference_degree33 : equalityCheck (finePart 33 difference_raw) (finePart 33 candidateTable) = true := by
  decide +kernel

theorem difference_degree34 : equalityCheck (finePart 34 difference_raw) (finePart 34 candidateTable) = true := by
  decide +kernel

theorem difference_degree35 : equalityCheck (finePart 35 difference_raw) (finePart 35 candidateTable) = true := by
  decide +kernel

theorem difference_degree36 : equalityCheck (finePart 36 difference_raw) (finePart 36 candidateTable) = true := by
  decide +kernel

theorem difference_degree37 : equalityCheck (finePart 37 difference_raw) (finePart 37 candidateTable) = true := by
  decide +kernel

theorem difference_degree38 : equalityCheck (finePart 38 difference_raw) (finePart 38 candidateTable) = true := by
  decide +kernel

theorem difference_degree39 : equalityCheck (finePart 39 difference_raw) (finePart 39 candidateTable) = true := by
  decide +kernel

theorem difference_degree40 : equalityCheck (finePart 40 difference_raw) (finePart 40 candidateTable) = true := by
  decide +kernel

theorem difference_degree41 : equalityCheck (finePart 41 difference_raw) (finePart 41 candidateTable) = true := by
  decide +kernel

theorem difference_degree42 : equalityCheck (finePart 42 difference_raw) (finePart 42 candidateTable) = true := by
  decide +kernel

theorem difference_degree43 : equalityCheck (finePart 43 difference_raw) (finePart 43 candidateTable) = true := by
  decide +kernel

theorem difference_degree44 : equalityCheck (finePart 44 difference_raw) (finePart 44 candidateTable) = true := by
  decide +kernel

theorem difference_degree45 : equalityCheck (finePart 45 difference_raw) (finePart 45 candidateTable) = true := by
  decide +kernel

theorem difference_degree46 : equalityCheck (finePart 46 difference_raw) (finePart 46 candidateTable) = true := by
  decide +kernel

theorem difference_degree47 : equalityCheck (finePart 47 difference_raw) (finePart 47 candidateTable) = true := by
  decide +kernel


end GeneralCK.Reflection.SmallBiasDifferenceJet

end


