-- Prove2me | solution 1 for AsyncSA.Contraction.lemma8
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:52:41.659472+00:00
-- url     : https://prove2.me/submissions/be0b237b-77bb-40e9-a4ca-b3d23e660a99

import Mathlib
import Definitions.Def_AsyncSA_Contraction_Model

open MeasureTheory Filter Topology

open AsyncSA.Contraction in
theorem solution {n : ℕ} {Ω : Type*} (alg : Algorithm n Ω) (ω : Ω)
    (β Dₖ : ℝ) (tₖ τₖ : ℕ) (Y : Fin n → ℕ → ℝ)
    (hβ : 0 ≤ β ∧ β < 1) (hDₖ : 0 ≤ Dₖ)
    (hF : ∀ y : Fin n → ℝ, ‖alg.F y‖ ≤ β * ‖y‖)
    (hτ : tₖ ≤ τₖ)
    (hx : ∀ t ≥ tₖ, ∀ j : Fin n, |alg.x t ω j| ≤ Dₖ)
    (hxi : ∀ t ≥ τₖ, ∀ i j : Fin n, |alg.xi i t ω j| ≤ Dₖ)
    (hYinit : ∀ i, Y i τₖ = Dₖ)
    (hYstep : ∀ i t, τₖ ≤ t →
      Y i (t + 1) = (1 - alg.α i t ω) * Y i t + alg.α i t ω * β * Dₖ) :
    ∀ i : Fin n, ∀ t ≥ τₖ,
      -Y i t + tailW (fun s => alg.α i s ω) (fun s => alg.w i s ω) τₖ t ≤
          alg.x t ω i ∧
        alg.x t ω i ≤
          Y i t + tailW (fun s => alg.α i s ω) (fun s => alg.w i s ω) τₖ t := by
  intro i t ht
  induction t, ht using Nat.le_induction with
  | base =>
    have h0 : tailW (fun s => alg.α i s ω) (fun s => alg.w i s ω) τₖ τₖ = 0 := by
      cases τₖ with
      | zero => rfl
      | succ t' =>
        show (if t' + 1 ≤ t' then _ else 0) = 0
        rw [if_neg (by omega)]
    rw [h0, hYinit, add_zero, add_zero]
    exact abs_le.mp (hx τₖ hτ i)
  | succ t ht ih =>
    have hW : tailW (fun s => alg.α i s ω) (fun s => alg.w i s ω) τₖ (t + 1) =
        (1 - alg.α i t ω) * tailW (fun s => alg.α i s ω) (fun s => alg.w i s ω) τₖ t +
          alg.α i t ω * alg.w i t ω := by
      show (if τₖ ≤ t then _ else 0) = _
      rw [if_pos ht]
    rw [hW, hYstep i t ht, alg.update i t ω]
    obtain ⟨ha0, ha1⟩ := alg.α_mem i t ω
    have hxinorm : ‖alg.xi i t ω‖ ≤ Dₖ := by
      rw [pi_norm_le_iff_of_nonneg hDₖ]
      intro j
      rw [Real.norm_eq_abs]
      exact hxi t ht i j
    have hFi : |alg.F (fun j => alg.x (alg.τ i j t ω) ω j) i| ≤ β * Dₖ := by
      have h1 := norm_le_pi_norm (alg.F (alg.xi i t ω)) i
      have h2 := hF (alg.xi i t ω)
      rw [Real.norm_eq_abs] at h1
      have h3 : β * ‖alg.xi i t ω‖ ≤ β * Dₖ := mul_le_mul_of_nonneg_left hxinorm hβ.1
      exact h1.trans (h2.trans h3)
    obtain ⟨hF1, hF2⟩ := abs_le.mp hFi
    obtain ⟨ih1, ih2⟩ := ih
    have hb : 0 ≤ 1 - alg.α i t ω := by linarith
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left ih1 hb, mul_le_mul_of_nonneg_left hF1 ha0]
    · nlinarith [mul_le_mul_of_nonneg_left ih2 hb, mul_le_mul_of_nonneg_left hF2 ha0]
