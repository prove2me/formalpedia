-- Prove2me | solution 1 for AssortSearch.HeurEq.estimates_ratio
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:29:48.911012+00:00
-- url     : https://prove2.me/submissions/4c2db34e-fbfa-4227-a5ab-75d657b0c614

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

lemma ash_estPref {n : ℕ} (lam : ℝ) (v : Fin n → ℝ) (v0 : ℝ) (hv : ∀ i, 0 < v i)
    (hv0 : 0 < v0) (hlam : 0 < lam) (hn : 0 < n) (x : ℕ) (i : Fin n) :
    estPref lam v v0 x i = v i / v ⟨0, hn⟩ := by
  have key : ∀ y : ℕ, demand lam v v0 y i / demandFirst lam v v0 y = v i / v ⟨0, hn⟩ := by
    intro y
    unfold demandFirst
    rw [dif_pos hn]
    exact ash_demand_div lam v v0 hv hv0 hlam y i ⟨0, hn⟩
  unfold estPref
  split_ifs
  · exact key x
  · exact key n

theorem solution {n : ℕ} (lam : ℝ) (v : Fin n → ℝ) (v0 : ℝ)
    (hv : ∀ i, 0 < v i) (hv0 : 0 < v0) (hlam : 0 < lam)
    (x : ℕ) (hx1 : 1 ≤ x) (hxn : x ≤ n) (i j : Fin n) (hij : i < j) :
    estPref lam v v0 x i / estPref lam v v0 x j = v i / v j := by
  have hn : 0 < n := i.pos
  rw [ash_estPref lam v v0 hv hv0 hlam hn, ash_estPref lam v v0 hv hv0 hlam hn]
  have h0 := (hv ⟨0, hn⟩).ne'
  have hj := (hv j).ne'
  field_simp
