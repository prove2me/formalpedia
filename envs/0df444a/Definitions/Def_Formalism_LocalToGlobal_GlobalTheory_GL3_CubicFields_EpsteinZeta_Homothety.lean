-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_Homothety
-- name    : Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_Homothety
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T21:26:00.052146+00:00
-- url     : https://prove2.me/theorems/83fed3d0-7600-4fa4-8ce7-2b31951d4b17
-- title:
--   Homothety
-- statement:
--   Definitions and structural lemmas for Homothety, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/EpsteinZeta/Homothety.lean

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_DedekindFactorK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
open NumberField Classical
open scoped Pointwise
theorem mem_smul_iff' (Λ : AddSubgroup ℂ) (c : ℂ) (w : ℂ) :
    w ∈ c • Λ ↔ ∃ x ∈ Λ, c * x = w := by
  rw [AddSubgroup.mem_smul_pointwise_iff_exists]
  simp only [smul_eq_mul]
def smulEquivNZ (Λ : AddSubgroup ℂ) (c : ℂ) (hc : c ≠ 0) :
    {w : ℂ // w ∈ Λ ∧ w ≠ 0} ≃ {w : ℂ // w ∈ c • Λ ∧ w ≠ 0} where
  toFun w := ⟨c * w.1, (mem_smul_iff' Λ c _).2 ⟨w.1, w.2.1, rfl⟩, mul_ne_zero hc w.2.2⟩
  invFun w := ⟨c⁻¹ * w.1, by
    obtain ⟨x, hx, hxw⟩ := (mem_smul_iff' Λ c _).1 w.2.1
    refine ⟨?_, mul_ne_zero (inv_ne_zero hc) w.2.2⟩
    rw [← hxw, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]; exact hx⟩
  left_inv w := by ext; simp [hc]
  right_inv w := by ext; simp [hc]
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5


