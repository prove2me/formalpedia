-- Prove2me | Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_SecondWayHolds
-- name    : Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_SecondWayHolds
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T00:37:19.197+00:00
-- url     : https://prove2.me/theorems/e3e47454-667b-4704-9c1f-f3ebde7adf9f
-- title:
--   Second Way Holds
-- statement:
--   Definitions and structural lemmas for Second Way Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/SecondWayHolds.lean

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_ChainI
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_BaseCaseKOneHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
namespace Formalism.BaseCaseIdentities
noncomputable section
open Classical
namespace Data
variable {k : Type*} [Field k] {Z C : Type*} [Fintype Z] [Fintype C] (D : Data k Z C)
def mu (J : ℕ) (c : C) : MvPowerSeries Z k := if D.lev c < J then D.m (D.lev c) c else 0
def main (J : ℕ) (c b : C) : MvPowerSeries Z k :=
  if D.lev c < J ∧ D.lev c + 1 < D.K then
    MvPowerSeries.C (-(D.l : k)⁻¹ * D.g c b) * frob D.q (D.m (D.lev c) c) else 0
end Data
end
end Formalism.BaseCaseIdentities


