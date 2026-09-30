-- Prove2me | solution 1 for AlgMechDesign.LowerBound.independence
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:33:36.632933+00:00
-- url     : https://prove2.me/submissions/819b83db-7a3f-4613-8c0c-1ace0982093c

import Definitions.Def_AlgMechDesign_LowerBound_Model

set_option autoImplicit false
open AlgMechDesign.LowerBound

theorem solution {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (htr : IsTruthful alloc pay)
    (t₁ t₂ : Fin n → Fin k → ℝ) (h₁ : IsType t₁) (h₂ : IsType t₂) (i : Fin n)
    (hoth : ∀ i' : Fin n, i' ≠ i → t₁ i' = t₂ i')
    (hx : taskSet (alloc t₁) i = taskSet (alloc t₂) i) :
    pay t₁ i = pay t₂ i := by
  have hu₁ : Function.update t₁ i (t₂ i) = t₂ := by
    funext l
    by_cases hl : l = i
    · subst l
      simp
    · simp [hl, hoth l hl]
  have hu₂ : Function.update t₂ i (t₁ i) = t₁ := by
    funext l
    by_cases hl : l = i
    · subst l
      simp
    · simp [hl, hoth l hl]
  have hforward := htr t₁ h₁ i (t₁ i) (t₂ i) (h₁ i) (h₂ i)
  have hreverse := htr t₂ h₂ i (t₂ i) (t₁ i) (h₂ i) (h₁ i)
  simp only [Function.update_eq_self, hu₁, utility, hx] at hforward
  simp only [Function.update_eq_self, hu₂, utility, hx] at hreverse
  linarith
