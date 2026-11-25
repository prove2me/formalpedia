-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_InvNatMemWf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_InvNatMemWf
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T09:48:19.981494+00:00
-- url     : https://prove2.me/theorems/3ee4e2c2-a44f-4d89-b322-a648453b9290
-- title:
--   Inv Nat Mem Wf
-- statement:
--   Definitions and structural lemmas for Inv Nat Mem Wf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialIntegrality/InvNatMemWf.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_InvNatCastMemWittIntegers
import Theorems.Thm_PI_ExpIntWProof_p_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.ExpIntWProof
open PI
def Wf (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] where
  carrier := {x | InWf x}
  mul_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    have : (p : ℂ_[p]) ^ (a + b) * (x * y) = ((p : ℂ_[p]) ^ a * x) * ((p : ℂ_[p]) ^ b * y) := by ring
    rw [this]
    exact Subring.mul_mem _ ha hb
  one_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    have : (p : ℂ_[p]) ^ (a + b) * (x + y) =
        (p : ℂ_[p]) ^ b * ((p : ℂ_[p]) ^ a * x) + (p : ℂ_[p]) ^ a * ((p : ℂ_[p]) ^ b * y) := by ring
    rw [this]
    exact Subring.add_mem _ (Subring.mul_mem _ (Subring.pow_mem _ (p_mem p) b) ha)
      (Subring.mul_mem _ (Subring.pow_mem _ (p_mem p) a) hb)
  zero_mem' := ⟨0, by simp⟩
  neg_mem' := by
    rintro x ⟨a, ha⟩
    exact ⟨a, by rw [mul_neg]; exact Subring.neg_mem _ ha⟩
end PI.ExpIntWProof
end


