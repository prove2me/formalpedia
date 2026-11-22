-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_SqfRootsInj
-- name    : Formalism_PeriodIntegrals_SqfRootsInj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:49:30.96456+00:00
-- url     : https://prove2.me/theorems/22d5722c-3064-4fa9-abe8-33ba5bc13331
-- title:
--   Sqf Roots Inj
-- statement:
--   Definitions and structural lemmas for Sqf Roots Inj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/SqfRootsInj.lean

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
namespace PI.SqfRootsInj
open PI.SqfLab
def Claim : Prop :=
  ∀ (g r : ℕ) [Fact g.Prime], 100 ≤ r → 2 ^ 12 ≤ g →
    ∀ T : Finset (ZMod g)[X], (∀ f ∈ T, Eii g r f) →
      (T.card : ℝ) ≤ 23 * Real.log g * (g : ℝ) ^ (-(1 / 2 : ℝ)) * (g : ℝ) ^ r
end PI.SqfRootsInj


