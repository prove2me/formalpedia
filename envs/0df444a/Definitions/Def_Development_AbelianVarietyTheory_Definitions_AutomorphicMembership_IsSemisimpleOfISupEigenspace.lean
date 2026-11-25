-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsSemisimpleOfISupEigenspace
-- name    : Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsSemisimpleOfISupEigenspace
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T15:44:24.898979+00:00
-- url     : https://prove2.me/theorems/827fade7-97d9-58cd-83cf-f93909d142c9
-- title:
--   Is Semisimple Of ISup Eigenspace
-- statement:
--   Definitions and structural lemmas for Is Semisimple Of ISup Eigenspace, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsSemisimpleOfISupEigenspace.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Theorems.Thm_GlobalTheory_WeilDeligne_coe_qPow
import Theorems.Thm_GlobalTheory_WeilDeligne_deg_ineIncl
import Theorems.Thm_GlobalTheory_WeilDeligne_qPow_zero
import Theorems.Thm_GlobalTheory_WeilDeligne_unrChar_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeilDeligne.coe_qPow
attribute [local simp] GlobalTheory.WeilDeligne.deg_ineIncl
attribute [local simp] GlobalTheory.WeilDeligne.qPow_zero
attribute [local simp] GlobalTheory.WeilDeligne.unrChar_apply


set_option autoImplicit false
noncomputable section
open Polynomial TensorProduct Module
namespace GlobalTheory.WeilDeligne
section Lin
variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
def diagEnd {ι : Type*} (c : ι → ℂ) : End ℂ (ι → ℂ) where
  toFun v i := c i * v i
  map_add' v v' := by ext; simp [mul_add]
  map_smul' a v := by ext; simp [mul_left_comm]
@[simp] theorem diagEnd_apply {ι : Type*} (c v : ι → ℂ) (i : ι) : diagEnd c v i = c i * v i := rfl
def absSpace (f : End ℂ V) (r : ℝ) : Submodule ℂ V := ⨆ (α : ℂ) (_ : ‖α‖ = r), f.eigenspace α
def IsPurePair (q : ℝ) (f N : End ℂ V) : Prop :=
  ⨆ i : ℤ, absSpace f (q ^ ((i : ℝ) / 2)) = ⊤ ∧
    ∀ i : ℕ, Set.BijOn (N ^ i) (absSpace f (q ^ (-(i : ℝ) / 2))) (absSpace f (q ^ ((i : ℝ) / 2)))
def shiftEnd (n : ℕ) : End ℂ (Fin n → ℂ) where
  toFun v i := if 1 ≤ (i : ℕ) then v ⟨i - 1, by omega⟩ else 0
  map_add' v v' := by ext i; by_cases hi : 1 ≤ (i : ℕ) <;> simp [hi]
  map_smul' a v := by ext i; by_cases hi : 1 ≤ (i : ℕ) <;> simp [hi]
end Lin
end GlobalTheory.WeilDeligne


