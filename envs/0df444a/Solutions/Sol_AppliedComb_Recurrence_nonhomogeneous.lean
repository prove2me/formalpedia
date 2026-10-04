-- Prove2me | solution 1 for AppliedComb.Recurrence.nonhomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T11:34:41.081987+00:00
-- url     : https://prove2.me/submissions/00406e6f-38b7-46af-90f3-bdfbfca72757

import Mathlib
import Definitions.Def_AppliedComb_Recurrence_advance

open AppliedComb.Recurrence in
theorem solution (k : ℕ) (c : Fin (k + 1) → ℝ) (hc0 : c 0 ≠ 0)
    (hck : c (Fin.last k) ≠ 0) (g f₀ : ℤ → ℝ) (hf₀ : opPoly k c f₀ = g) :
    ∀ f : ℤ → ℝ, opPoly k c f = g → ∃ f₁ ∈ solutionSpace k c, f = f₀ + f₁ := by
  intro f hf
  refine ⟨f - f₀, ?_, by abel⟩
  show f - f₀ ∈ LinearMap.ker (opPoly k c)
  rw [LinearMap.mem_ker, map_sub, hf, hf₀, sub_self]
