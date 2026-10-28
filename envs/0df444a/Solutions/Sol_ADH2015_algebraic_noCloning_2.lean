-- Prove2me | solution 2 for ADH2015.algebraic_noCloning
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T14:22:24.797324+00:00
-- url     : https://prove2.me/submissions/4a212eb7-6208-4bd8-9a0c-eb3785ae1ade

import Mathlib
import Definitions.Def_ADH2015_defs

open Matrix
open scoped Kronecker

namespace S216ADH
open ADH2015

lemma part1 {e ē : Type*} [Fintype e] [Fintype ē] [DecidableEq e]
    [DecidableEq ē] (C : Submodule ℂ (e × ē → ℂ)) (O₁ O₂ : Matrix (e × ē) (e × ē) ℂ)
    (h₁ : ActsWithin C O₁) (h₂ : ActsWithin C O₂) (hb : HasRepOnBar C O₁) (he : HasRepOnE C O₂) :
    ∀ v ∈ C, O₁ *ᵥ (O₂ *ᵥ v) = O₂ *ᵥ (O₁ *ᵥ v) := by
  obtain ⟨Y, hY⟩ := hb
  obtain ⟨X, hX⟩ := he
  intro v hv
  have h2v : O₂ *ᵥ v ∈ C := (h₂ v hv).1
  have h1v : O₁ *ᵥ v ∈ C := (h₁ v hv).1
  have hc : ((1 : Matrix e e ℂ) ⊗ₖ Y) * (X ⊗ₖ (1 : Matrix ē ē ℂ)) =
      (X ⊗ₖ (1 : Matrix ē ē ℂ)) * ((1 : Matrix e e ℂ) ⊗ₖ Y) := by
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]; simp
  calc O₁ *ᵥ (O₂ *ᵥ v) = ((1 : Matrix e e ℂ) ⊗ₖ Y) *ᵥ (O₂ *ᵥ v) := ((hY _ h2v).1).symm
    _ = ((1 : Matrix e e ℂ) ⊗ₖ Y) *ᵥ ((X ⊗ₖ (1 : Matrix ē ē ℂ)) *ᵥ v) := by rw [(hX v hv).1]
    _ = (X ⊗ₖ (1 : Matrix ē ē ℂ)) *ᵥ (((1 : Matrix e e ℂ) ⊗ₖ Y) *ᵥ v) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hc]
    _ = (X ⊗ₖ (1 : Matrix ē ē ℂ)) *ᵥ (O₁ *ᵥ v) := by rw [(hY v hv).1]
    _ = O₂ *ᵥ (O₁ *ᵥ v) := (hX _ h1v).1

end S216ADH

open ADH2015 in
theorem solution {e ē : Type*} [Fintype e] [Fintype ē] [DecidableEq e]
    [DecidableEq ē] (C : Submodule ℂ (e × ē → ℂ)) :
    (∀ O₁ O₂ : Matrix (e × ē) (e × ē) ℂ, ActsWithin C O₁ → ActsWithin C O₂ →
      HasRepOnBar C O₁ → HasRepOnE C O₂ →
      ∀ v ∈ C, O₁ *ᵥ (O₂ *ᵥ v) = O₂ *ᵥ (O₁ *ᵥ v)) ∧
    (∀ S : Set (Matrix (e × ē) (e × ē) ℂ),
      (∀ O ∈ S, ActsWithin C O ∧ HasRepOnBar C O ∧ HasRepOnE C O) →
      ∀ O₁ ∈ S, ∀ O₂ ∈ S, ∀ v ∈ C, O₁ *ᵥ (O₂ *ᵥ v) = O₂ *ᵥ (O₁ *ᵥ v)) := by
  refine ⟨fun O₁ O₂ h₁ h₂ hb he => S216ADH.part1 C O₁ O₂ h₁ h₂ hb he, ?_⟩
  intro S hS O₁ h1 O₂ h2
  exact S216ADH.part1 C O₁ O₂ (hS O₁ h1).1 (hS O₂ h2).1 (hS O₁ h1).2.1 (hS O₂ h2).2.2
