-- Prove2me | solution 1 for ArrowDebreu.ThmI.condition2_at_E_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:48:21.149509+00:00
-- url     : https://prove2.me/submissions/cf4b601b-a66e-4725-91da-bc10e9007aa7

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_ThmI_AssumptionsItoIV
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
import Definitions.Def_ArrowDebreu_ThmI_economyE
open ArrowDebreu.Shared

namespace ArrowDebreu.ThmI

theorem aux_c2E_profit_nonneg {l m n : ℕ} (E : Economy l m n) (hIa : AssumptionIa E)
    (a : Player m n → Fin l → ℝ)
    (ha : (economyE E E.X E.Y).IsEquilibriumPoint a) (j : Fin n) :
    0 ≤ priceOf a ⬝ᵥ prodOf a j := by
  have h := (ha.2 (Sum.inr (Sum.inl j))).2 0 (by
    show (0 : Fin l → ℝ) ∈ E.Y j
    exact (hIa j).2.2)
  have hp : priceOf (Function.update a (Sum.inr (Sum.inl j)) 0) = priceOf a := by
    unfold priceOf
    rw [Function.update_of_ne (by simp)]
  change priceOf (Function.update a (Sum.inr (Sum.inl j)) 0) ⬝ᵥ
      (Function.update a (Sum.inr (Sum.inl j)) 0) (Sum.inr (Sum.inl j)) ≤
      priceOf a ⬝ᵥ a (Sum.inr (Sum.inl j)) at h
  rw [hp, Function.update_self, dotProduct_zero] at h
  exact h

theorem aux_c2E_constr_eq {l m n : ℕ} (E : Economy l m n) (hIa : AssumptionIa E)
    (hIVb : AssumptionIVb E) (a : Player m n → Fin l → ℝ)
    (ha : (economyE E E.X E.Y).IsEquilibriumPoint a) (i : Fin m) :
    (economyE E E.X E.Y).constr (Sum.inl i) a = budgetSet E (priceOf a) (prodOf a) i := by
  have hs : 0 ≤ ∑ j, E.α i j * (priceOf a ⬝ᵥ prodOf a j) :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hIVb.1 i j) (aux_c2E_profit_nonneg E hIa a ha j)
  change {x | x ∈ E.X i ∧ priceOf a ⬝ᵥ x ≤
          priceOf a ⬝ᵥ E.ζ i + max 0 (∑ j, E.α i j * (priceOf a ⬝ᵥ prodOf a j))} = _
  rw [max_eq_right hs]
  rfl

end ArrowDebreu.ThmI

open ArrowDebreu.ThmI
open ArrowDebreu.Shared

theorem solution {l m n : ℕ} (E : Economy l m n) (hIa : AssumptionIa E)
    (hIVb : AssumptionIVb E) (a : Player m n → Fin l → ℝ)
    (ha : (economyE E E.X E.Y).IsEquilibriumPoint a) :
    Condition2 E (priceOf a) (consOf a) (prodOf a) := by
  intro i
  have hc := aux_c2E_constr_eq E hIa hIVb a ha i
  obtain ⟨hmem, hmax⟩ := ha.2 (Sum.inl i)
  rw [hc] at hmem hmax
  refine ⟨hmem, fun x' hx' => ?_⟩
  have h := hmax x' hx'
  change E.u i ((Function.update a (Sum.inl i) x') (Sum.inl i)) ≤ E.u i (a (Sum.inl i)) at h
  rw [Function.update_self] at h
  exact h
