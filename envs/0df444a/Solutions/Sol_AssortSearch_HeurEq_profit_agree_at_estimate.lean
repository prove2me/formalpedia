-- Prove2me | solution 1 for AssortSearch.HeurEq.profit_agree_at_estimate
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:32:16.309607+00:00
-- url     : https://prove2.me/submissions/5a2f802b-43ac-415a-8cb1-f998b0dd221e

import Mathlib
import Definitions.Def_AssortSearch_HeurEq_Model

set_option autoImplicit false
open RetailVariety.Structure AssortSearch.HeurEq

lemma ash_sumPref_pos {n : ℕ} (v : Fin n → ℝ) (v0 : ℝ) (hv : ∀ i, 0 < v i) (hv0 : 0 < v0)
    (S : Finset (Fin n)) : 0 < ∑ i ∈ S, v i + v0 :=
  add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun i _ => (hv i).le) hv0

lemma ash_H_lt_one {n : ℕ} (lam : ℝ) (v : Fin n → ℝ) (v0 : ℝ) (hv : ∀ i, 0 < v i)
    (hv0 : 0 < v0) (hlam : 0 < lam) (x : ℕ) : searchH lam v v0 x < 1 := by
  unfold searchH prefTotal
  have h := ash_sumPref_pos v v0 hv hv0 (popularSet n x)
  have h2 : 0 < lam * (v0 + ∑ j ∈ popularSet n x, v j) := mul_pos hlam (by linarith)
  calc Real.exp (-(lam * (v0 + ∑ j ∈ popularSet n x, v j))) < Real.exp 0 :=
        Real.exp_lt_exp.mpr (by linarith)
    _ = 1 := Real.exp_zero

lemma ash_demand_eq {n : ℕ} (lam : ℝ) (v : Fin n → ℝ) (v0 : ℝ) (x : ℕ) (i : Fin n) :
    demand lam v v0 x i =
      v i / (∑ j ∈ popularSet n x, v j + v0) * (1 - searchH lam v v0 x) := rfl

lemma ash_demand_div {n : ℕ} (lam : ℝ) (v : Fin n → ℝ) (v0 : ℝ) (hv : ∀ i, 0 < v i)
    (hv0 : 0 < v0) (hlam : 0 < lam) (x : ℕ) (i j : Fin n) :
    demand lam v v0 x i / demand lam v v0 x j = v i / v j := by
  have hs := ash_sumPref_pos v v0 hv hv0 (popularSet n x)
  have hH := ash_H_lt_one lam v v0 hv hv0 hlam x
  have h1 : 1 - searchH lam v v0 x ≠ 0 := (sub_pos.mpr hH).ne'
  have hj := (hv j).ne'
  rw [ash_demand_eq, ash_demand_eq]
  field_simp

theorem solution {n : ℕ} (lam : ℝ) (m : Fin n → ℝ) (c : ℝ → ℝ)
    (v : Fin n → ℝ) (v0 : ℝ)
    (hv : ∀ i, 0 < v i) (hv0 : 0 < v0) (hlam : 0 < lam)
    (x : ℕ) (hx1 : 1 ≤ x) (hxn : x ≤ n) :
    trueProfit lam m c v v0 x =
      estProfit m c (estPref lam v v0 x) (estPrefNoPurchase lam v v0 x) x := by
  have hn : 0 < n := by omega
  have hs := ash_sumPref_pos v v0 hv hv0 (popularSet n x)
  have hH := ash_H_lt_one lam v v0 hv hv0 hlam x
  have hd1 : demandFirst lam v v0 x = demand lam v v0 x ⟨0, hn⟩ := by
    unfold demandFirst; rw [dif_pos hn]
  have hpos : 0 < demand lam v v0 x ⟨0, hn⟩ := by
    rw [ash_demand_eq]
    exact mul_pos (div_pos (hv _) hs) (sub_pos.mpr hH)
  have hD : demandFirst lam v v0 x ≠ 0 := by rw [hd1]; exact hpos.ne'
  have hest : ∀ j ∈ popularSet n x,
      estPref lam v v0 x j = demand lam v v0 x j / demandFirst lam v v0 x := by
    intro j hj
    have hj' : j.val < x := by simpa [popularSet] using hj
    unfold estPref
    rw [if_pos hj']
  have hsum : ∑ j ∈ popularSet n x, estPref lam v v0 x j
      = (∑ j ∈ popularSet n x, demand lam v v0 x j) / demandFirst lam v v0 x := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl hest
  have hden : ∑ j ∈ popularSet n x, estPref lam v v0 x j + estPrefNoPurchase lam v v0 x
      = 1 / demandFirst lam v v0 x := by
    rw [hsum]
    unfold estPrefNoPurchase demandNoPurchase
    field_simp
    ring
  have hshare : ∀ i ∈ popularSet n x,
      share (estPref lam v v0 x) (estPrefNoPurchase lam v v0 x) (popularSet n x) i
        = demand lam v v0 x i := by
    intro i hi
    unfold share
    rw [hden, hest i hi]
    field_simp
  unfold trueProfit estProfit
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [hshare i hi]
