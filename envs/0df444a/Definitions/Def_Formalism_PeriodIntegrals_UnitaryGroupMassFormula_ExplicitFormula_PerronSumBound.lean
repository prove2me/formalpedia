-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronSumBound
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronSumBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:24:25.33607+00:00
-- url     : https://prove2.me/theorems/32edd39c-4445-4eaf-9e3e-8a7cb4e25402
-- title:
--   Perron Sum Bound
-- statement:
--   Definitions and structural lemmas for Perron Sum Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronSumBound.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.EF
open Finset
def nearB (u T : ℝ) (n : ℕ) : ℝ :=
  if n < ⌊u⌋₊ then (4 * u / T) / ((⌊u⌋₊ : ℝ) - n)
  else if n ≤ ⌊u⌋₊ + 1 then 2 else (4 * u / T) / ((n : ℝ) - ⌊u⌋₊ - 1)
def pTerm (u T : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * (u / n) ^ cLine u * kb T (u / n)
end PI.EF


