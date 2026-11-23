-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PrimeLogarithmTail_SumLogBlock
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PrimeLogarithmTail_SumLogBlock
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:52:00.623514+00:00
-- url     : https://prove2.me/theorems/388d7999-d489-4a86-b50c-8e802bb2cda4
-- title:
--   Sum Log Block
-- statement:
--   Definitions and structural lemmas for Sum Log Block, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PrimeLogarithmTail/SumLogBlock.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.TailWork
open Finset
noncomputable def g (n : ℕ) : ℝ := 1 / ((n : ℝ) * ((n : ℝ) - 1))
noncomputable def h (n : ℕ) : ℝ := 1 / ((n : ℝ) - 1) + 1 / (n : ℝ)
end PI.TailWork


