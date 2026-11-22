-- Prove2me | Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OrderOfThreeUnitsTwoPow
-- name    : Formalism_TameInertiaTowers_CentralOrderTwo_OrderOfThreeUnitsTwoPow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:50:28.712167+00:00
-- url     : https://prove2.me/theorems/3d2f3753-5c06-4680-9c76-cb16e199a7b6
-- title:
--   Order Of Three Units Two Pow
-- statement:
--   Definitions and structural lemmas for Order Of Three Units Two Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OrderOfThreeUnitsTwoPow.lean

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.TwoAdicCyclotomicDecomposition
namespace AdmissibleUnits
def r4 (N : ℕ) (h : 4 ∣ 2 ^ N) : (ZMod (2 ^ N))ˣ →* ZMod 4 :=
  (ZMod.castHom h (ZMod 4)).toMonoidHom.comp (Units.coeHom _)
def r8 (N : ℕ) (h : 8 ∣ 2 ^ N) : (ZMod (2 ^ N))ˣ →* ZMod 8 :=
  (ZMod.castHom h (ZMod 8)).toMonoidHom.comp (Units.coeHom _)
end AdmissibleUnits
end Formalism.TwoAdicCyclotomicDecomposition


