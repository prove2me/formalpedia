-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_SumAntidiagonalTuple
-- name    : Formalism_PeriodIntegrals_SumAntidiagonalTuple
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:08:58.125414+00:00
-- url     : https://prove2.me/theorems/3d5f0345-8e03-4fff-ae16-e0b604605361
-- title:
--   Sum Antidiagonal Tuple
-- statement:
--   Definitions and structural lemmas for Sum Antidiagonal Tuple, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/SumAntidiagonalTuple.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI
def SumAntidiagonalTuple : Prop :=
  ∀ D T : ℕ, D < T →
    ∑ k ∈ Finset.range (T - D), (Finset.Nat.antidiagonalTuple D k).card = Nat.choose (T - 1) D
end PI


