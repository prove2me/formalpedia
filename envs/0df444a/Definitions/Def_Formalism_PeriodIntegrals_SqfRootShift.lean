-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_SqfRootShift
-- name    : Formalism_PeriodIntegrals_SqfRootShift
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:49:25.476161+00:00
-- url     : https://prove2.me/theorems/0c3c592f-fbff-46b2-9ce4-09bdcdb002e2
-- title:
--   Sqf Root Shift
-- statement:
--   Definitions and structural lemmas for Sqf Root Shift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/SqfRootShift.lean

import Definitions.Def_Formalism_PeriodIntegrals_SqfLab
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
namespace PI.SqfRootShift
open PI.SqfLab
def Claim : Prop :=
  ∀ (g r q d e : ℕ) [Fact g.Prime], q.Prime → d.Prime → q % 8 = 3 → d % 16 = 7 → 2 ≤ e →
    16 ≤ q → 16 ≤ d → g % (4 * 2 ^ e * q * d) = 1 → 100 ≤ r → 2 ^ 12 ≤ g →
    ∀ (c : (ZMod g)ˣ) (T : Finset (ZMod g)[X]), (∀ f ∈ T, Eiii g r c f) →
      (T.card : ℝ) ≤ (1 / (4 * ((min q d : ℕ) : ℝ)) + (1 + Real.log r) / ((g : ℝ) - 1)) *
        (g : ℝ) ^ r
end PI.SqfRootShift


