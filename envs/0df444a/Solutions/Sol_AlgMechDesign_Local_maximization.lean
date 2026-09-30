-- Prove2me | solution 1 for AlgMechDesign.Local.maximization
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:34:29.11406+00:00
-- url     : https://prove2.me/submissions/e6dc2cf5-f376-418e-ab12-d4afc6cf5643

import Definitions.Def_AlgMechDesign_Local_Prices

set_option autoImplicit false
open AlgMechDesign.Local

private theorem independence {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
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

private theorem price_at_allocation {n k : ℕ}
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (htr : IsTruthful alloc pay)
    (t : Fin n → Fin k → ℝ) (ht : IsType t) (i : Fin n)
    (ti : Fin k → ℝ) (hti : IsAgentType ti) :
    price alloc pay i (agentSet alloc (Function.update t i ti) i) t =
      pay (Function.update t i ti) i := by
  classical
  have hX : IsAttainable alloc i (agentSet alloc (Function.update t i ti) i) t :=
    ⟨ti, hti, rfl⟩
  have hc := Classical.choose_spec hX
  unfold price
  rw [dif_pos hX]
  apply independence alloc pay htr
  · intro l j
    by_cases hl : l = i
    · subst l
      simpa using hc.1 j
    · simpa [hl] using ht l j
  · intro l j
    by_cases hl : l = i
    · subst l
      simpa using hti j
    · simpa [hl] using ht l j
  · intro l hl
    simp [hl]
  · exact hc.2

private theorem maximize {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (htr : IsTruthful alloc pay)
    (t : Fin n → Fin k → ℝ) (ht : IsType t) (i : Fin n) (X : Finset (Fin k))
    (hX : IsAttainable alloc i X t) :
    price alloc pay i X t - ∑ j ∈ X, t i j ≤
      price alloc pay i (agentSet alloc t i) t - ∑ j ∈ agentSet alloc t i, t i j := by
  obtain ⟨ti, hti, hset⟩ := hX
  have h := htr t ht i (t i) ti (ht i) hti
  have hprice := price_at_allocation alloc pay htr t ht i ti hti
  have hself := price_at_allocation alloc pay htr t ht i (t i) (ht i)
  simp only [Function.update_eq_self] at hself h
  rw [hset] at hprice
  rw [hprice, hself]
  dsimp only [agentSet] at hset
  simpa only [utility, agentSet, hset] using h

theorem solution {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (htr : IsTruthful alloc pay)
    (t : Fin n → Fin k → ℝ) (ht : IsType t) (i : Fin n) :
    IsAttainable alloc i (agentSet alloc t i) t ∧
      ∀ X : Finset (Fin k), IsAttainable alloc i X t →
        setUtility alloc pay i X t ≤ setUtility alloc pay i (agentSet alloc t i) t := by
  constructor
  · refine ⟨t i, ht i, ?_⟩
    simp
  · exact maximize alloc pay htr t ht i
