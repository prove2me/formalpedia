-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDual
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDual
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T13:54:47.779873+00:00
-- url     : https://prove2.me/theorems/7f9a0ebd-23dd-4f7d-8c97-7795fcdf4b95
-- title:
--   Index Dual
-- statement:
--   Definitions and structural lemmas for Index Dual, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/IndexDual.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
namespace PI.UnitaryGroupMassFormula.LCG
namespace DIdx
def qI {S : Type} [CommRing S] (𝔞 : Ideal S) (a : S) : Ideal S where
  carrier := {y | ∀ c ∈ 𝔞, c * y ∈ Ideal.span {a}}
  add_mem' := by
    intro y y' hy hy' c hc
    rw [mul_add]
    exact add_mem (hy c hc) (hy' c hc)
  zero_mem' := by
    intro c _
    rw [mul_zero]
    exact zero_mem _
  smul_mem' := by
    intro r y hy c hc
    rw [smul_eq_mul, mul_left_comm]
    exact Ideal.mul_mem_left _ r (hy c hc)
def aI {K : Type} [Field K] [NumberField K] {k : ℕ} (X : Submodule (𝓞 K) (Fin k → K)) (x : Fin k → K) :
    Ideal (𝓞 K) where
  carrier := {c | c • x ∈ X}
  add_mem' := by
    intro c c' hc hc'
    rw [Set.mem_ofPred_eq, add_smul]
    exact add_mem hc hc'
  zero_mem' := by
    rw [Set.mem_ofPred_eq, zero_smul]
    exact zero_mem _
  smul_mem' := by
    intro r c hc
    rw [Set.mem_ofPred_eq, smul_eq_mul, mul_smul]
    exact X.smul_mem r hc
end DIdx
end PI.UnitaryGroupMassFormula.LCG


