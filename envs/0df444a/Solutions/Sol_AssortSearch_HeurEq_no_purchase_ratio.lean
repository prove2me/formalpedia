-- Prove2me | solution 1 for AssortSearch.HeurEq.no_purchase_ratio
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:34:05.268992+00:00
-- url     : https://prove2.me/submissions/089932a3-9947-4088-abe2-b8639fd4bd32

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

theorem solution {n : ℕ} (lam : ℝ) (v : Fin n → ℝ) (v0 : ℝ)
    (hv : ∀ i, 0 < v i) (hv0 : 0 < v0) (hlam : 0 < lam)
    (x : ℕ) (i : Fin n) (hi : i.val < x) :
    demandNoPurchase lam v v0 x / demand lam v v0 x i =
      (shareNoPurchase v v0 x +
          ∑ j ∈ popularSet n x, share v v0 (popularSet n x) j * searchH lam v v0 x) /
        (share v v0 (popularSet n x) i * (1 - searchH lam v v0 x)) := by
  have hs := ash_sumPref_pos v v0 hv hv0 (popularSet n x)
  have hsum : ∑ j ∈ popularSet n x, share v v0 (popularSet n x) j
      = 1 - shareNoPurchase v v0 x := by
    unfold share shareNoPurchase
    rw [← Finset.sum_div]
    field_simp
    ring
  have hnum : demandNoPurchase lam v v0 x = shareNoPurchase v v0 x +
      ∑ j ∈ popularSet n x, share v v0 (popularSet n x) j * searchH lam v v0 x := by
    unfold demandNoPurchase demand
    rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]
    ring
  rw [hnum]
  rfl
