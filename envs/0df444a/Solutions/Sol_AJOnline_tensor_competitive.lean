-- Prove2me | solution 1 for AJOnline.tensor_competitive
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T16:12:50.550923+00:00
-- url     : https://prove2.me/submissions/bfec1862-0389-492b-bf0a-e032107959d2

import Mathlib
import Definitions.Def_AJOnline_CostedGame

open AJGames AJOnline
open scoped ENNReal NNReal

universe u

theorem solution (C D : CostedGame.{u}) (σ : Strategy C.G) (τ : Strategy D.G)
    (ρ₁ β₁ ρ₂ β₂ : ℝ≥0) (hσ : Competitive C σ ρ₁ β₁) (hτ : Competitive D τ ρ₂ β₂) :
    Competitive (C.tensor D) (tensorS σ τ) (max ρ₁ ρ₂) (β₁ + β₂) := by
  intro s hs
  have h1 := hσ (projL s) hs.2.1
  have h2 := hτ (projR s) hs.2.2
  have m1 : (ρ₁ : ℝ≥0∞) ≤ ((max ρ₁ ρ₂ : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast le_max_left ρ₁ ρ₂
  have m2 : (ρ₂ : ℝ≥0∞) ≤ ((max ρ₁ ρ₂ : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast le_max_right ρ₁ ρ₂
  show C.alg (projL s) + D.alg (projR s) ≤
    ((max ρ₁ ρ₂ : ℝ≥0) : ℝ≥0∞) * (C.opt (projL s) + D.opt (projR s)) + ((β₁ + β₂ : ℝ≥0) : ℝ≥0∞)
  calc C.alg (projL s) + D.alg (projR s)
      ≤ ((ρ₁ : ℝ≥0∞) * C.opt (projL s) + β₁) + ((ρ₂ : ℝ≥0∞) * D.opt (projR s) + β₂) := add_le_add h1 h2
    _ ≤ (((max ρ₁ ρ₂ : ℝ≥0) : ℝ≥0∞) * C.opt (projL s) + β₁) +
        (((max ρ₁ ρ₂ : ℝ≥0) : ℝ≥0∞) * D.opt (projR s) + β₂) := by gcongr
    _ = _ := by push_cast; ring
