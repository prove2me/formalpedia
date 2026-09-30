-- Prove2me | solution 1 for AlgMechDesign.LowerBound.maximization
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:34:28.3615+00:00
-- url     : https://prove2.me/submissions/69fd545f-75af-4c97-99a3-89157d761890

import Definitions.Def_AlgMechDesign_LowerBound_Price

set_option autoImplicit false
open AlgMechDesign.LowerBound

private theorem independence {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
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

private theorem price_at_allocation {n k : ℕ}
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (htr : IsTruthful alloc pay)
    (t : Fin n → Fin k → ℝ) (ht : IsType t) (i : Fin n)
    (ti : Fin k → ℝ) (hti : IsAgentType ti) :
    price alloc pay i (taskSet (alloc (Function.update t i ti)) i) t =
      pay (Function.update t i ti) i := by
  classical
  have hX : IsAttainable alloc i t (taskSet (alloc (Function.update t i ti)) i) :=
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
    (hX : IsAttainable alloc i t X) :
    price alloc pay i X t - ∑ j ∈ X, t i j ≤
      price alloc pay i (taskSet (alloc t) i) t - ∑ j ∈ taskSet (alloc t) i, t i j := by
  obtain ⟨ti, hti, hset⟩ := hX
  have h := htr t ht i (t i) ti (ht i) hti
  have hprice := price_at_allocation alloc pay htr t ht i ti hti
  have hself := price_at_allocation alloc pay htr t ht i (t i) (ht i)
  simp only [Function.update_eq_self] at hself h
  rw [hset] at hprice
  rw [hprice, hself]
  simpa only [utility, taskTime, hset] using h

theorem solution {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (htruth : IsTruthful alloc pay)
    (t : Fin n → Fin k → ℝ) (ht : IsType t) (i : Fin n) :
    IsAttainable alloc i t (taskSet (alloc t) i) ∧
      ∀ X : Finset (Fin k), IsAttainable alloc i t X →
        price alloc pay i X t - taskTime (t i) X ≤
          price alloc pay i (taskSet (alloc t) i) t - taskTime (t i) (taskSet (alloc t) i) := by
  constructor
  · refine ⟨t i, ht i, ?_⟩
    simp
  · exact maximize alloc pay htruth t ht i
