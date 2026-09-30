-- Prove2me | solution 1 for ArrowDebreu.ThmI.theorem_I
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T22:04:37.665446+00:00
-- url     : https://prove2.me/submissions/fe0b988c-1cce-409d-8488-baa0c10e12a4

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_ThmI_AssumptionsItoIV
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
import Definitions.Def_ArrowDebreu_ThmI_economyE
import Theorems.Thm_ArrowDebreu_ThmI_Xhat_bounded
import Theorems.Thm_ArrowDebreu_ThmI_Yhat_bounded
import Theorems.Thm_ArrowDebreu_ThmI_Etilde_has_equilibrium
import Theorems.Thm_ArrowDebreu_ThmI_Etilde_equilibrium_is_E_equilibrium
import Theorems.Thm_ArrowDebreu_ThmI_E_equilibrium_is_competitive
open ArrowDebreu.Shared

namespace ArrowDebreu.ThmI

namespace ThmIAux

/-- The cube of §3.3.3 is the closed ball of radius `c` for the sup norm. -/
theorem cube_eq_closedBall (l : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    cube l c = Metric.closedBall (0 : Fin l → ℝ) c := by
  ext x
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hc]
  constructor
  · intro h i
    rw [Real.norm_eq_abs]
    exact h i
  · intro h i
    rw [← Real.norm_eq_abs]
    exact h i

/-- A bounded set lies in the interior of a large enough cube (§3.3.3). -/
theorem subset_interior_cube_of_norm_le {l : ℕ} {S : Set (Fin l → ℝ)} {B c : ℝ}
    (hS : ∀ x ∈ S, ‖x‖ ≤ B) (hBc : B < c) (hc : 0 ≤ c) : S ⊆ interior (cube l c) := by
  rw [cube_eq_closedBall l hc]
  intro x hx
  have hx' : x ∈ Metric.ball (0 : Fin l → ℝ) c := by
    rw [mem_ball_zero_iff]
    exact lt_of_le_of_lt (hS x hx) hBc
  rw [← Metric.isOpen_ball.interior_eq] at hx'
  exact interior_mono Metric.ball_subset_closedBall hx'

end ThmIAux

end ArrowDebreu.ThmI

open ArrowDebreu.ThmI ArrowDebreu.ThmI.ThmIAux
open ArrowDebreu.Shared

theorem solution {l m n : ℕ} (hl : 0 < l) (E : Economy l m n) (hE : AssumptionsItoIV E) :
    ∃ (x : Fin m → Fin l → ℝ) (y : Fin n → Fin l → ℝ) (p : Fin l → ℝ),
      IsCompetitiveEquilibrium E x y p := by
  classical
  -- §3.3.1–§3.3.2: the attainable sets are bounded
  choose C hC using fun i =>
    isBounded_iff_forall_norm_le.1 (Xhat_bounded E hE.Ia hE.Ib hE.Ic hE.II i)
  choose D hD using fun j =>
    isBounded_iff_forall_norm_le.1 (Yhat_bounded E hE.Ia hE.Ib hE.Ic hE.II j)
  -- §3.3.3: choose the cube
  set B : ℝ := ∑ i, |C i| + ∑ j, |D j| with hB
  have hB0 : 0 ≤ B := by
    rw [hB]
    exact add_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _))
      (Finset.sum_nonneg (fun j _ => abs_nonneg _))
  set c : ℝ := B + 1 with hcdef
  have hc : 0 < c := by rw [hcdef]; linarith
  have hX : ∀ i, Xhat E i ⊆ interior (cube l c) := by
    intro i
    refine subset_interior_cube_of_norm_le (B := |C i|) (fun x hx => ?_) ?_ hc.le
    · exact le_trans (hC i x hx) (le_abs_self _)
    · have h1 : |C i| ≤ ∑ i', |C i'| :=
        Finset.single_le_sum (fun i' _ => abs_nonneg (C i')) (Finset.mem_univ i)
      have h2 : 0 ≤ ∑ j, |D j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
      rw [hcdef, hB]
      linarith
  have hY : ∀ j, Yhat E j ⊆ interior (cube l c) := by
    intro j
    refine subset_interior_cube_of_norm_le (B := |D j|) (fun y hy => ?_) ?_ hc.le
    · exact le_trans (hD j y hy) (le_abs_self _)
    · have h1 : |D j| ≤ ∑ j', |D j'| :=
        Finset.single_le_sum (fun j' _ => abs_nonneg (D j')) (Finset.mem_univ j)
      have h2 : 0 ≤ ∑ i, |C i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
      rw [hcdef, hB]
      linarith
  -- §3.4.0: the truncated economy has an equilibrium point
  obtain ⟨a, ha⟩ := Etilde_has_equilibrium hl E hE c hc hX hY
  -- §3.4.1: it is an equilibrium point of `E`
  have ha' := Etilde_equilibrium_is_E_equilibrium E hE c hc hX hY a ha
  -- §3.2: hence a competitive equilibrium
  exact ⟨consOf a, prodOf a, priceOf a, E_equilibrium_is_competitive E hE a ha'⟩

