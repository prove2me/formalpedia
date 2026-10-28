-- Prove2me | solution 1 for AccelMM.BTMap.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:29:12.53653+00:00
-- url     : https://prove2.me/submissions/3a3e4d13-3f32-4b1a-aafe-6f2ee1e3ee57

import Mathlib
import Definitions.Def_AccelMM_BTMap_Framework
import Definitions.Def_AccelMM_BTMap_Model

open scoped InnerProductSpace

namespace Aux_AccelMM_L42

open AccelMM.BTMap

lemma coord {n : ℕ} (x : E n) (s : ℝ) (i : Fin n) : (x + s • ones n) i = x i + s := by
  simp [ones]

lemma log_shift (a b s : ℝ) :
    Real.log (Real.exp (a + s) + Real.exp (b + s)) = s + Real.log (Real.exp a + Real.exp b) := by
  rw [Real.exp_add, Real.exp_add, mul_comm (Real.exp a), mul_comm (Real.exp b), ← mul_add,
    Real.log_mul (Real.exp_pos s).ne' (add_pos (Real.exp_pos a) (Real.exp_pos b)).ne',
    Real.log_exp]

lemma loglik_shift {n : ℕ} (d : Fin n → Fin n → ℕ) (x : E n) (s : ℝ) :
    loglik d (x + s • ones n) = loglik d x := by
  unfold loglik
  simp only [coord, log_shift]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

lemma rho_shift {n : ℕ} (d : Fin n → Fin n → ℕ) (α β : ℝ) (x : E n) (s : ℝ) :
    rho α β d (x + s • ones n) = loglik d x +
      ∑ i, ((α - 1) * (x i + s) - β * Real.exp (x i + s)) := by
  unfold rho logPrior
  rw [loglik_shift]
  simp only [coord]

lemma rho_shift' {n : ℕ} (d : Fin n → Fin n → ℕ) (α β : ℝ) (x : E n) (s : ℝ) :
    rho α β d (x + s • ones n) = rho α β d x +
      ((α - 1) * n * s - β * (∑ i, Real.exp (x i)) * (Real.exp s - 1)) := by
  have h0 := rho_shift d α β x 0
  simp only [zero_smul, add_zero] at h0
  rw [rho_shift, h0]
  have : ∀ i, (α - 1) * (x i + s) - β * Real.exp (x i + s) =
      ((α - 1) * (x i + 0) - β * Real.exp (x i + 0)) +
        ((α - 1) * s - β * Real.exp (x i) * (Real.exp s - 1)) := by
    intro i; rw [add_zero, Real.exp_add]; ring
  simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end Aux_AccelMM_L42

open AccelMM.BTMap Aux_AccelMM_L42 in
theorem solution {n : ℕ} (d : Fin n → Fin n → ℕ) (α β : ℝ) (hα : 1 < α) (hβ : 0 < β) :
    (∀ w : E n, rho α β d (Pi α β w) ≥ rho α β d w) ∧
      (∀ w : E n, ⟪gradient (rho α β d) (Pi α β w), ones n⟫_ℝ = 0) := by
  -- key facts about the shift
  have key : ∀ w : E n, 0 < n →
      Real.exp (shift α β w) * (∑ i, Real.exp (w i)) = (α - 1) / β * n := by
    intro w hn
    have hS : 0 < ∑ i, Real.exp (w i) := by
      have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      exact Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
    have hA : 0 < (α - 1) / β * n := by
      have : (0 : ℝ) < n := by exact_mod_cast hn
      have : 0 < α - 1 := by linarith
      positivity
    unfold shift
    rw [Real.exp_sub, Real.exp_log hA, Real.exp_log hS, div_mul_cancel₀ _ hS.ne']
  constructor
  · intro w
    unfold Pi
    rw [rho_shift']
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · set s := shift α β w
      set S := ∑ i, Real.exp (w i)
      have hS : 0 < S := by
        have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
        exact Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
      have hk := key w hn
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hc : 0 ≤ (α - 1) * n := by nlinarith
      -- β S = (α-1) n e^{-s}
      have hβS : β * S = (α - 1) * n * Real.exp (-s) := by
        have h1 : Real.exp (-s) * Real.exp s = 1 := by
          rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
        have : β * (Real.exp s * S) = (α - 1) * n := by
          rw [hk]; field_simp
        calc β * S = β * S * (Real.exp (-s) * Real.exp s) := by rw [h1, mul_one]
          _ = Real.exp (-s) * (β * (Real.exp s * S)) := by ring
          _ = _ := by rw [this]; ring
      have hE : 1 - s ≤ Real.exp (-s) := by linarith [Real.add_one_le_exp (-s)]
      have hβSe : β * S * Real.exp s = (α - 1) * n := by
        have : β * (Real.exp s * S) = (α - 1) * n := by rw [hk]; field_simp
        linarith [this]
      nlinarith [mul_le_mul_of_nonneg_left hE hc]
  · intro w
    set p := Pi α β w with hp
    by_cases hdiff : DifferentiableAt ℝ (rho α β d) p
    · -- directional derivative along `ones`
      have hline : HasDerivAt (fun s : ℝ => p + s • ones n) (ones n) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (ones n)).const_add p
      have h1 : HasDerivAt (fun s : ℝ => rho α β d (p + s • ones n))
          (fderiv ℝ (rho α β d) p (ones n)) 0 := by
        exact HasFDerivAt.comp_hasDerivAt_of_eq 0 hdiff.hasFDerivAt hline (by simp)
      have hterm : ∀ i, HasDerivAt (fun s : ℝ => (α - 1) * (p i + s) - β * Real.exp (p i + s))
          ((α - 1) * 1 - β * (Real.exp (p i + 0) * 1)) 0 := by
        intro i
        have h := (hasDerivAt_id (0 : ℝ)).const_add (p i)
        exact (h.const_mul (α - 1)).sub (h.exp.const_mul β)
      have h2 : HasDerivAt (fun s : ℝ => rho α β d (p + s • ones n))
          (∑ i, ((α - 1) * 1 - β * (Real.exp (p i + 0) * 1))) 0 := by
        have := (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hterm i)).const_add
          (loglik d p)
        refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s => ?_))
        exact rho_shift d α β p s
      have huniq := h1.unique h2
      rw [gradient, InnerProductSpace.toDual_symm_apply, huniq]
      simp only [add_zero, mul_one]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; simp
      · have hpS : ∑ i, Real.exp (p i) = Real.exp (shift α β w) * ∑ i, Real.exp (w i) := by
          rw [hp, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro i _
          unfold Pi
          rw [coord, Real.exp_add, mul_comm]
        rw [hpS, key w hn]
        field_simp
        ring
    · rw [gradient_eq_zero_of_not_differentiableAt hdiff, inner_zero_left]
