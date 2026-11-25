-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_SenTateCharClosure
-- name    : GroundTheory_PAdicHodge_SenTateCharClosure
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T00:38:05.615656+00:00
-- url     : https://prove2.me/theorems/523cc396-e010-4b82-9036-ef3468c1d716
-- title:
--   Sen Tate Char Closure
-- statement:
--   Definitions and structural lemmas for Sen Tate Char Closure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SenTateCharClosure.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_SenTateCharUnits
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceClosure
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Definitions.Def_GroundTheory_PAdicHodge_TateCpTwist
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_zero
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.normTrace_zero
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867


set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.PAdicHodge
open IntermediateField
variable {p : ℕ} [hp : Fact p.Prime]
def inertiaGal (K : IntermediateField ℚ_[p] (PadicAlgCl p)) : Subgroup Gal(PadicAlgCl p/K) where
  carrier := {σ | ∀ y : PadicAlgCl p, ‖y‖ ≤ 1 → ‖σ y - y‖ < 1}
  one_mem' := fun y _ => by simp
  mul_mem' := fun {σ τ} hσ hτ y hy => by
    have hτy : ‖τ y‖ ≤ 1 := by rwa [norm_gal_apply]
    have e : (σ * τ) y - y = (σ (τ y) - τ y) + (τ y - y) := by
      rw [AlgEquiv.mul_apply]; ring
    rw [e]
    exact lt_of_le_of_lt ((PadicAlgCl.isNonarchimedean p) _ _) (max_lt (hσ _ hτy) (hτ y hy))
  inv_mem' := fun {σ} hσ y hy => by
    have e : σ (σ⁻¹ y - y) = -(σ y - y) := by
      rw [map_sub, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]; ring
    rw [← norm_gal_apply σ, e, norm_neg]
    exact hσ y hy
namespace SenTateChar
open SenTateChar
end SenTateChar
end GroundTheory.PAdicHodge


