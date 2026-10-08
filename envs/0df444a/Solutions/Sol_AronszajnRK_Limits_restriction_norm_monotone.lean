-- Prove2me | solution 1 for AronszajnRK.Limits.restriction_norm_monotone
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T17:16:02.449616+00:00
-- url     : https://prove2.me/submissions/39ae9b4f-fb77-48f9-a1f0-283cd7d450e0

import Mathlib
import Definitions.Def_AronszajnRK_Sum_kernelFn
import Definitions.Def_AronszajnRK_Limits_IsDecreasingRKSequence

open Filter Topology

open Filter Topology AronszajnRK.Limits in
theorem solution {X : Type*} (E : ℕ → Set X) (H : ℕ → Type*)
    [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)]
    [∀ n, RKHS ℂ (H n) (E n) ℂ] (hS : IsDecreasingRKSequence E H) (f₀ : X → ℂ)
    (g : ∀ n, H n) (hg : ∀ (n : ℕ) (x : E n), g n x = f₀ x.1) :
    Monotone (fun n => ‖g n‖) ∧
      ∃ L : EReal, Tendsto (fun n => ((‖g n‖ : ℝ) : EReal)) atTop (𝓝 L) := by
  have hmono : Monotone (fun n => ‖g n‖) := by
    intro m n hmn
    exact hS.norm_restrict_le hmn (g n) (g m) (fun x hm hn => by
      rw [hg m ⟨x, hm⟩, hg n ⟨x, hn⟩])
  refine ⟨hmono, ?_⟩
  have h2 : Monotone (fun n => ((‖g n‖ : ℝ) : EReal)) :=
    fun m n hmn => EReal.coe_le_coe_iff.mpr (hmono hmn)
  exact ⟨_, tendsto_atTop_iSup h2⟩
