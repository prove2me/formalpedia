-- Prove2me | solution 1 for Arxiv1906_02008.indicators_constant_on_hyperplanes
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T01:47:27.735253+00:00
-- url     : https://prove2.me/submissions/c6aaa60d-6179-4f23-bbb4-8088122de290

import Mathlib
import Definitions.Def_Arxiv1906_02008_Basic

open MeasureTheory Set
open scoped RealInnerProductSpace
open Arxiv1906_02008

theorem solution {n : ℕ} (hn : n = 2 ∨ n = 3)
    (u : Rn n → Rn n → ℝ → ℂ) (km kp : ℝ) (hkm : 0 < km) (hk : km < kp)
    (xh θ : Rn n) (hxh : ‖xh‖ = 1) (hθ : ‖θ‖ = 1) (hne : xh ≠ θ)
    (α : ℝ) (z₁ z₂ : Rn n) (h₁ : z₁ ∈ hyperplane xh θ α) (h₂ : z₂ ∈ hyperplane xh θ α) :
    indicatorI1 u km kp xh θ z₁ = indicatorI1 u km kp xh θ z₂ ∧
      indicatorI2 u km kp xh θ z₁ = indicatorI2 u km kp xh θ z₂ := by
  have e : ⟪z₁, θ - xh⟫ = ⟪z₂, θ - xh⟫ := by
    simp only [hyperplane, Set.mem_ofPred_eq] at h₁ h₂; linarith
  simp only [indicatorI1, indicatorI2, e]
  exact ⟨trivial, trivial⟩
