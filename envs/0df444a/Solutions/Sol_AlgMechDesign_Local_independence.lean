-- Prove2me | solution 1 for AlgMechDesign.Local.independence
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:34:27.23201+00:00
-- url     : https://prove2.me/submissions/10c944ae-31ef-4cac-968d-665c2fdd2b58

import Definitions.Def_AlgMechDesign_Local_Prices

set_option autoImplicit false
open AlgMechDesign.Local

theorem solution {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (htr : IsTruthful alloc pay)
    (t₁ t₂ : Fin n → Fin k → ℝ) (h₁ : IsType t₁) (h₂ : IsType t₂) (i : Fin n)
    (hoth : ∀ i' : Fin n, i' ≠ i → t₁ i' = t₂ i')
    (hx : agentSet alloc t₁ i = agentSet alloc t₂ i) :
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
  dsimp only [agentSet] at hx
  have hforward := htr t₁ h₁ i (t₁ i) (t₂ i) (h₁ i) (h₂ i)
  have hreverse := htr t₂ h₂ i (t₂ i) (t₁ i) (h₂ i) (h₁ i)
  simp only [Function.update_eq_self, hu₁, utility, hx] at hforward
  simp only [Function.update_eq_self, hu₂, utility, hx] at hreverse
  linarith

