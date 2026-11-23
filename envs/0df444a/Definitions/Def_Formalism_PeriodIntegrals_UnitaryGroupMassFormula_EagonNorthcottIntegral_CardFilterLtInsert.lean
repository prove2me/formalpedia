-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_CardFilterLtInsert
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_CardFilterLtInsert
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:10:38.061898+00:00
-- url     : https://prove2.me/theorems/7715d7b5-9c12-4035-b0e1-e6c5aba3eeb1
-- title:
--   Card Filter Lt Insert
-- statement:
--   Definitions and structural lemmas for Card Filter Lt Insert, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EagonNorthcottIntegral/CardFilterLtInsert.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_ExactSecondDegreeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_DivisionPartitionTotal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.EagonNorthcottZ
open MvPolynomial PI.EagonNorthcott
def nn (m : ℕ) (r : ℕ → ℕ) : ℕ → ℕ
  | 0 => m
  | j + 1 => r (j + 1)
def BB {D m : ℕ} (e0 : Fin m → W D) (r : ℕ → ℕ) (b : ∀ j, Fin (r j) → W D) : ∀ j, Fin (nn m r j) → W D
  | 0 => e0
  | j + 1 => b (j + 1)
end PI.EagonNorthcottZ


