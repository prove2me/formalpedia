-- Prove2me | solution 1 for AppliedComb.Recurrence.distinct_roots
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T17:52:54.920899+00:00
-- url     : https://prove2.me/submissions/317d77db-5164-4f61-8a60-c45db65fd759

import Mathlib
import Definitions.Def_AppliedComb_Recurrence_advance

set_option autoImplicit false

open AppliedComb.Recurrence in
theorem factor_apply_49b3 (s : ℝ) (f : ℤ → ℝ) (n : ℤ) :
    (advance - s • (1 : Module.End ℝ (ℤ → ℝ))) f n = f (n + 1) - s * f n := by
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rfl

open AppliedComb.Recurrence in
theorem first_order_49b3 (s : ℝ) (hs : s ≠ 0) (f : ℤ → ℝ)
    (hf : (advance - s • (1 : Module.End ℝ (ℤ → ℝ))) f = 0) :
    ∀ n : ℤ, f n = f 0 * s ^ n := by
  have step : ∀ n : ℤ, f (n + 1) = s * f n := by
    intro n
    have h := congrFun hf n
    rw [factor_apply_49b3] at h
    simp only [Pi.zero_apply] at h
    linarith
  intro n
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [step, ih, zpow_add_one₀ hs]
    ring
  | pred k ih =>
    have h1 := step (-(k : ℤ) - 1)
    have e : -(k : ℤ) - 1 + 1 = -(k : ℤ) := by ring
    rw [e, ih] at h1
    rw [zpow_sub_one₀ hs, show f (-(k : ℤ) - 1) = s⁻¹ * (s * f (-(k : ℤ) - 1)) by
      rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul], ← h1]
    ring

open AppliedComb.Recurrence in
theorem solution (k : ℕ) (r : Fin k → ℝ) (hr : Function.Injective r)
    (hr0 : ∀ i, r i ≠ 0) (f : ℤ → ℝ)
    (hf : (List.ofFn fun i : Fin k => advance - r i • (1 : Module.End ℝ (ℤ → ℝ))).prod f = 0) :
    ∃ c : Fin k → ℝ, ∀ n : ℤ, f n = ∑ i : Fin k, c i * r i ^ n := by
  induction k generalizing f with
  | zero =>
    refine ⟨fun i => i.elim0, fun n => ?_⟩
    simp only [List.ofFn_zero, List.prod_nil, Module.End.one_apply] at hf
    simp [hf]
  | succ k ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton,
      Module.End.mul_apply] at hf
    set h := (advance - r (Fin.last k) • (1 : Module.End ℝ (ℤ → ℝ))) f with hh
    have hinj : Function.Injective (fun i : Fin k => r i.castSucc) :=
      hr.comp (Fin.castSucc_injective k)
    obtain ⟨c, hc⟩ := ih (fun i => r i.castSucc) hinj (fun i => hr0 _) h hf
    have hne : ∀ i : Fin k, r i.castSucc - r (Fin.last k) ≠ 0 := by
      intro i hi
      have := hr (sub_eq_zero.mp hi)
      exact (Fin.castSucc_lt_last i).ne this
    set fp : ℤ → ℝ := fun n => ∑ i : Fin k, c i / (r i.castSucc - r (Fin.last k)) * r i.castSucc ^ n
      with hfp
    have hg : (advance - r (Fin.last k) • (1 : Module.End ℝ (ℤ → ℝ))) (f - fp) = 0 := by
      funext n
      rw [factor_apply_49b3]
      have h1 : h n = f (n + 1) - r (Fin.last k) * f n := factor_apply_49b3 _ _ _
      rw [hc] at h1
      simp only [Pi.sub_apply, Pi.zero_apply, hfp]
      have key : ∑ i : Fin k, c i / (r i.castSucc - r (Fin.last k)) * r i.castSucc ^ (n + 1)
          - r (Fin.last k) * ∑ i : Fin k, c i / (r i.castSucc - r (Fin.last k)) * r i.castSucc ^ n
          = ∑ i : Fin k, c i * r i.castSucc ^ n := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [zpow_add_one₀ (hr0 _)]
        field_simp [hne i]
      linarith
    have hg2 := first_order_49b3 (r (Fin.last k)) (hr0 (Fin.last k)) (f - fp) hg
    refine ⟨Fin.lastCases ((f - fp) 0) (fun i => c i / (r i.castSucc - r (Fin.last k))), fun n => ?_⟩
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
    have := hg2 n
    simp only [Pi.sub_apply, hfp] at this ⊢
    linarith
