-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_Interface
-- name    : ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_Interface
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T21:26:44.821803+00:00
-- url     : https://prove2.me/theorems/cb27b64e-4d9e-46b0-b9f8-2abc7f9a7abb
-- title:
--   Interface
-- statement:
--   Definitions and structural lemmas for Interface, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/Interface.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_CMGoodModels_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.L2.Th1.CM
namespace ReciprocityTheory.ChartRestriction.L1
def JInt : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), Squarefree d → d % 4 = 3 → HasCMBy d L →
    ∀ (l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]), ‖ι (jInv L)‖ ≤ 1
def JUnram : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), Squarefree d → d % 4 = 3 → HasCMBy d L →
    ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ¬ l ∣ d → ∀ ι : ℂ ≃+* ℂ_[l], ι (jInv L) ∈ MaximalUnramifiedExtension l
end ReciprocityTheory.ChartRestriction.L1


