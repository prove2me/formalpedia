-- Prove2me | solution 1 for ArrowDebreu.ThmI.E_equilibrium_is_competitive
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T21:35:46.310743+00:00
-- url     : https://prove2.me/submissions/6b525d24-8f3b-42f0-a8b9-44f6d4c6ca02

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_ThmI_AssumptionsItoIV
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
import Definitions.Def_ArrowDebreu_ThmI_economyE
import Theorems.Thm_ArrowDebreu_ThmI_budget_exhausted
import Theorems.Thm_ArrowDebreu_ThmI_condition2_at_E_equilibrium
open ArrowDebreu.Shared

namespace ArrowDebreu.ThmI

namespace EqCompAux

variable {l m n : ℕ}

/-- Updating a producer's or consumer's action does not change the price. -/
theorem priceOf_update_of_ne (a : Player m n → Fin l → ℝ) (k : Player m n)
    (hk : k ≠ Sum.inr (Sum.inr ())) (v : Fin l → ℝ) :
    priceOf (Function.update a k v) = priceOf a := by
  unfold priceOf
  rw [Function.update_of_ne (Ne.symm hk)]

/-- Updating the price does not change the consumption vectors. -/
theorem consOf_update_price (a : Player m n → Fin l → ℝ) (p : Fin l → ℝ) :
    consOf (Function.update a (Sum.inr (Sum.inr ())) p) = consOf a := by
  funext i
  unfold consOf
  rw [Function.update_of_ne (by simp)]

/-- Updating the price does not change the production plans. -/
theorem prodOf_update_price (a : Player m n → Fin l → ℝ) (p : Fin l → ℝ) :
    prodOf (Function.update a (Sum.inr (Sum.inr ())) p) = prodOf a := by
  funext j
  unfold prodOf
  rw [Function.update_of_ne (by simp)]

/-- **Condition 1** at an equilibrium point of `E`: producer `j` maximizes profit over `Y_j`. -/
theorem condition1_at_E_equilibrium (E : Economy l m n) (a : Player m n → Fin l → ℝ)
    (ha : (economyE E E.X E.Y).IsEquilibriumPoint a) :
    Condition1 E (priceOf a) (prodOf a) := by
  intro j
  obtain ⟨hmem, hmax⟩ := ha.2 (Sum.inr (Sum.inl j))
  refine ⟨hmem, fun y' hy' => ?_⟩
  have h := hmax y' hy'
  change priceOf (Function.update a (Sum.inr (Sum.inl j)) y') ⬝ᵥ
      (Function.update a (Sum.inr (Sum.inl j)) y') (Sum.inr (Sum.inl j)) ≤
      priceOf a ⬝ᵥ a (Sum.inr (Sum.inl j)) at h
  rw [priceOf_update_of_ne a _ (by simp), Function.update_self] at h
  exact h

/-- **Condition 3** at an equilibrium point of `E`: the price lies in the simplex. -/
theorem condition3_at_E_equilibrium (E : Economy l m n) (a : Player m n → Fin l → ℝ)
    (ha : (economyE E E.X E.Y).IsEquilibriumPoint a) :
    Condition3 (priceOf a) :=
  (ha.2 (Sum.inr (Sum.inr ()))).1

/-- The market participant's optimality: `p·z^* ≤ p^*·z^*` for every `p ∈ P`. -/
theorem market_optimal (E : Economy l m n) (a : Player m n → Fin l → ℝ)
    (ha : (economyE E E.X E.Y).IsEquilibriumPoint a) (p : Fin l → ℝ) (hp : p ∈ priceSimplex l) :
    p ⬝ᵥ excessDemand E (consOf a) (prodOf a) ≤
      priceOf a ⬝ᵥ excessDemand E (consOf a) (prodOf a) := by
  have h := (ha.2 (Sum.inr (Sum.inr ()))).2 p hp
  change priceOf (Function.update a (Sum.inr (Sum.inr ())) p) ⬝ᵥ
      excessDemand E (consOf (Function.update a (Sum.inr (Sum.inr ())) p))
        (prodOf (Function.update a (Sum.inr (Sum.inr ())) p)) ≤
      priceOf a ⬝ᵥ excessDemand E (consOf a) (prodOf a) at h
  rw [consOf_update_price, prodOf_update_price] at h
  have hp' : priceOf (Function.update a (Sum.inr (Sum.inr ())) p) = p := by
    unfold priceOf
    rw [Function.update_self]
  rw [hp'] at h
  exact h

/-- The unit vector `e_h` lies in the price simplex. -/
theorem single_mem_priceSimplex (h : Fin l) : (Pi.single h (1:ℝ) : Fin l → ℝ) ∈ priceSimplex l := by
  refine ⟨?_, ?_⟩
  · intro k
    by_cases hk : k = h
    · subst hk; simp
    · simp [hk]
  · simp

/-- `p^*·z^* = 0` from budget exhaustion and `Σ_i α_{ij} = 1`. -/
theorem price_dot_excess_eq_zero (E : Economy l m n) (hIVb : AssumptionIVb E)
    (p : Fin l → ℝ) (x : Fin m → Fin l → ℝ) (y : Fin n → Fin l → ℝ)
    (hbudget : ∀ i, p ⬝ᵥ x i = income E p y i) :
    p ⬝ᵥ excessDemand E x y = 0 := by
  unfold excessDemand
  rw [dotProduct_sub, dotProduct_sub, dotProduct_sum, dotProduct_sum, dotProduct_sum]
  have h1 : ∑ i, p ⬝ᵥ x i = ∑ i, (p ⬝ᵥ E.ζ i + ∑ j, E.α i j * (p ⬝ᵥ y j)) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hbudget i]
    rfl
  rw [h1, Finset.sum_add_distrib, Finset.sum_comm]
  have h2 : ∑ j, ∑ i, E.α i j * (p ⬝ᵥ y j) = ∑ j, p ⬝ᵥ y j := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_mul, hIVb.2 j, one_mul]
  rw [h2]
  ring

/-- **Condition 4** at an equilibrium point of `E`. -/
theorem condition4_at_E_equilibrium (E : Economy l m n) (hII : AssumptionII E)
    (hIa : AssumptionIa E) (hIIIb : AssumptionIIIb E) (hIIIc : AssumptionIIIc E)
    (hIVb : AssumptionIVb E) (a : Player m n → Fin l → ℝ)
    (ha : (economyE E E.X E.Y).IsEquilibriumPoint a) :
    Condition4 E (priceOf a) (consOf a) (prodOf a) := by
  have h2 : Condition2 E (priceOf a) (consOf a) (prodOf a) :=
    condition2_at_E_equilibrium E hIa hIVb a ha
  have hb := budget_exhausted E hII hIIIb hIIIc (priceOf a) (consOf a) (prodOf a) h2
  have hz0 : priceOf a ⬝ᵥ excessDemand E (consOf a) (prodOf a) = 0 :=
    price_dot_excess_eq_zero E hIVb _ _ _ hb
  refine ⟨?_, hz0⟩
  intro h
  have hm := market_optimal E a ha (Pi.single h 1) (single_mem_priceSimplex h)
  rw [hz0, single_dotProduct, one_mul] at hm
  exact hm

end EqCompAux

end ArrowDebreu.ThmI

open ArrowDebreu.ThmI ArrowDebreu.ThmI.EqCompAux
open ArrowDebreu.Shared

theorem solution {l m n : ℕ} (E : Economy l m n) (hE : AssumptionsItoIV E)
    (a : Player m n → Fin l → ℝ) (ha : (economyE E E.X E.Y).IsEquilibriumPoint a) :
    IsCompetitiveEquilibrium E (consOf a) (prodOf a) (priceOf a) :=
  ⟨condition1_at_E_equilibrium E a ha,
   condition2_at_E_equilibrium E hE.Ia hE.IVb a ha,
   condition3_at_E_equilibrium E a ha,
   condition4_at_E_equilibrium E hE.II hE.Ia hE.IIIb hE.IIIc hE.IVb a ha⟩
