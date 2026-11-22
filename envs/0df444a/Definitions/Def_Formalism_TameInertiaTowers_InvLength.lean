-- Prove2me | Definitions.Def_Formalism_TameInertiaTowers_InvLength
-- name    : Formalism_TameInertiaTowers_InvLength
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:47:56.995447+00:00
-- url     : https://prove2.me/theorems/df11fdb1-72f7-454b-8f44-ef4ce5a5a633
-- title:
--   Inv Length
-- statement:
--   Definitions and structural lemmas for Inv Length, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/InvLength.lean

import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.TwoAdicCyclotomicDecomposition
def InvLength : Prop :=
  ∀ (N : ℕ) (u : ℤ), u ≠ 1 →
    Nat.card {x : ZMod (2 ^ N) // ((u - 1 : ℤ) : ZMod (2 ^ N)) * x = 0} =
      2 ^ min N (padicValInt 2 (u - 1))
end Formalism.TwoAdicCyclotomicDecomposition


