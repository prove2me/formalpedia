-- Prove2me | solution 1 for ADH2015.algebraic_noCloning
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T14:21:45.730646+00:00
-- url     : https://prove2.me/submissions/c8b4d2b9-b6ea-4290-a8d0-8bc9d9e5d3c9

import Mathlib
import Definitions.Def_ADH2015_defs

open Matrix
open scoped Kronecker
open ADH2015

lemma adh_nocl_core {e ē : Type*} [Fintype e] [Fintype ē] [DecidableEq e]
    [DecidableEq ē] (C : Submodule ℂ (e × ē → ℂ)) (O₁ O₂ : Matrix (e × ē) (e × ē) ℂ)
    (h1 : ADH2015.ActsWithin C O₁) (h2 : ADH2015.ActsWithin C O₂)
    (hb : ADH2015.HasRepOnBar C O₁) (he : ADH2015.HasRepOnE C O₂) :
    ∀ v ∈ C, O₁ *ᵥ (O₂ *ᵥ v) = O₂ *ᵥ (O₁ *ᵥ v) := by
  intro v hv
  obtain ⟨Y, hY⟩ := hb
  obtain ⟨X, hX⟩ := he
  have e1 : O₁ *ᵥ (O₂ *ᵥ v) = (X ⊗ₖ Y) *ᵥ v := by
    rw [← (hY _ (h2 v hv).1).1, ← (hX v hv).1, mulVec_mulVec, ← mul_kronecker_mul,
      one_mul, mul_one]
  have e2 : O₂ *ᵥ (O₁ *ᵥ v) = (X ⊗ₖ Y) *ᵥ v := by
    rw [← (hX _ (h1 v hv).1).1, ← (hY v hv).1, mulVec_mulVec, ← mul_kronecker_mul,
      one_mul, mul_one]
  rw [e1, e2]

theorem solution {e ē : Type*} [Fintype e] [Fintype ē] [DecidableEq e]
    [DecidableEq ē] (C : Submodule ℂ (e × ē → ℂ)) :
    (∀ O₁ O₂ : Matrix (e × ē) (e × ē) ℂ, ADH2015.ActsWithin C O₁ → ADH2015.ActsWithin C O₂ →
      ADH2015.HasRepOnBar C O₁ → ADH2015.HasRepOnE C O₂ →
      ∀ v ∈ C, O₁ *ᵥ (O₂ *ᵥ v) = O₂ *ᵥ (O₁ *ᵥ v)) ∧
    (∀ S : Set (Matrix (e × ē) (e × ē) ℂ),
      (∀ O ∈ S, ADH2015.ActsWithin C O ∧ ADH2015.HasRepOnBar C O ∧ ADH2015.HasRepOnE C O) →
      ∀ O₁ ∈ S, ∀ O₂ ∈ S, ∀ v ∈ C, O₁ *ᵥ (O₂ *ᵥ v) = O₂ *ᵥ (O₁ *ᵥ v)) := by
  refine ⟨fun O₁ O₂ h1 h2 hb he => adh_nocl_core C O₁ O₂ h1 h2 hb he, ?_⟩
  intro S hS O₁ hO₁ O₂ hO₂
  exact adh_nocl_core C O₁ O₂ (hS O₁ hO₁).1 (hS O₂ hO₂).1 (hS O₁ hO₁).2.1 (hS O₂ hO₂).2.2
