-- Prove2me | Definitions.Def_FD1D_Averaging
-- name    : FD1D_Averaging
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T09:42:47.756798+00:00
-- url     : https://prove2.me/theorems/9a6cbd45-a25e-4f5f-ad7c-ce16f3d8b03a
-- title:
--   Averaging
-- statement:
--   Definitions and structural lemmas for Averaging, from Yash Kanoria (ykanoria/FD1d-Lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Tight upper bound for fully dynamic matching on the line development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Averaging.lean

import Definitions.Def_FD1D_Expectations
import Theorems.Thm_FD1D_DeletionRule_kernel_apply
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.DeletionRule.kernel_apply
attribute [local simp] FD1D.FiniteLaw.expect_const


set_option autoImplicit true
namespace FD1D
noncomputable section
open scoped BigOperators
namespace FiniteLaw
variable {α : Type*} [Fintype α]
def timeAverage {T : ℕ} (hT : 0 < T)
    (μ : Fin T → FiniteLaw α) : FiniteLaw (Fin T × α) where
  mass z := (1 / (T : ℝ)) * (μ z.1).mass z.2
  mass_nonneg z :=
    mul_nonneg (by positivity) ((μ z.1).mass_nonneg z.2)
  sum_mass := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ t : Fin T, ∑ x : α,
          (1 / (T : ℝ)) * (μ t).mass x) =
          ∑ _t : Fin T, (1 / (T : ℝ)) := by
            apply Finset.sum_congr rfl
            intro t _
            rw [← Finset.mul_sum, (μ t).sum_mass, mul_one]
      _ = 1 := by
        simp [hT.ne']
def timeLiftPerm {T : ℕ} (e : Equiv.Perm α) :
    Equiv.Perm (Fin T × α) :=
  (Equiv.refl (Fin T)).prodCongr e
end FiniteLaw
end
end FD1D


