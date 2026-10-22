-- Prove2me | solution 1 for AssortSearch.HeurEq.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:07:34.071191+00:00
-- url     : https://prove2.me/submissions/3c6d00f6-024a-4ea8-8637-65973402c831

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

lemma z_anti (lam : ℝ) (hlam : 0 < lam) :
    AntitoneOn
      (fun δ : ℝ => δ * Real.exp (-(lam * δ)) / (1 - Real.exp (-(lam * δ))))
      (Set.Ioi 0) := by
  have key : ∀ δ : ℝ, 0 < δ →
      δ * Real.exp (-(lam * δ)) / (1 - Real.exp (-(lam * δ)))
        = δ / (Real.exp (lam * δ) - 1) := by
    intro δ hδ
    have hE : 1 < Real.exp (lam * δ) := Real.one_lt_exp_iff.mpr (mul_pos hlam hδ)
    have h0 : Real.exp (lam * δ) ≠ 0 := (Real.exp_pos _).ne'
    have h1 : Real.exp (lam * δ) - 1 ≠ 0 := by linarith
    rw [Real.exp_neg]
    field_simp
  intro a ha b hb hab
  have ha' : 0 < a := ha
  have hb' : 0 < b := hb
  simp only
  rw [key a ha', key b hb']
  have hsec := convexOn_exp.secant_mono (a := 0) (x := lam * a) (y := lam * b)
    (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _)
    (by positivity) (by positivity) (by nlinarith)
  simp only [Real.exp_zero, sub_zero] at hsec
  have hp : 0 < Real.exp (lam * a) - 1 := by
    have := Real.one_lt_exp_iff.mpr (mul_pos hlam ha'); linarith
  have hq : 0 < Real.exp (lam * b) - 1 := by
    have := Real.one_lt_exp_iff.mpr (mul_pos hlam hb'); linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)] at hsec
  rw [div_le_div_iff₀ hq hp]
  nlinarith [mul_pos hlam hp]

noncomputable def Vs {n : ℕ} (v : Fin n → ℝ) (x : ℕ) : ℝ := ∑ j ∈ popularSet n x, v j

lemma Vs_nonneg {n : ℕ} (v : Fin n → ℝ) (hv : ∀ i, 0 < v i) (x : ℕ) : 0 ≤ Vs v x :=
  Finset.sum_nonneg fun i _ => (hv i).le

lemma Vs_mono {n : ℕ} (v : Fin n → ℝ) (hv : ∀ i, 0 < v i) {x y : ℕ} (hxy : x ≤ y) :
    Vs v x ≤ Vs v y := by
  unfold Vs
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => (hv i).le)
  intro i hi
  simp only [popularSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  omega

lemma ash7_d0 {n : ℕ} (lam : ℝ) (v : Fin n → ℝ) (v0 : ℝ) (hv : ∀ i, 0 < v i)
    (hv0 : 0 < v0) (x : ℕ) :
    demandNoPurchase lam v v0 x
      = (v0 + searchH lam v v0 x * Vs v x) / (Vs v x + v0) := by
  have hs := ash_sumPref_pos v v0 hv hv0 (popularSet n x)
  have hsum : ∑ j ∈ popularSet n x, share v v0 (popularSet n x) j
      = 1 - shareNoPurchase v v0 x := by
    unfold share shareNoPurchase
    rw [← Finset.sum_div]
    field_simp
    ring
  unfold demandNoPurchase demand
  rw [← Finset.sum_mul, hsum]
  unfold shareNoPurchase Vs
  field_simp
  ring

lemma ash7_first {n : ℕ} (lam : ℝ) (v : Fin n → ℝ) (v0 : ℝ) (hn : 0 < n) (x : ℕ) :
    demandFirst lam v v0 x
      = v ⟨0, hn⟩ / (Vs v x + v0) * (1 - searchH lam v v0 x) := by
  unfold demandFirst
  rw [dif_pos hn]
  rfl

lemma ash7_estNP {n : ℕ} (lam : ℝ) (v : Fin n → ℝ) (v0 : ℝ) (hv : ∀ i, 0 < v i)
    (hv0 : 0 < v0) (hlam : 0 < lam) (hn : 0 < n) (x : ℕ) :
    estPrefNoPurchase lam v v0 x
      = ((v0 + searchH lam v v0 x * Vs v x) / (1 - searchH lam v v0 x)) / v ⟨0, hn⟩ := by
  have hH := ash_H_lt_one lam v v0 hv hv0 hlam x
  have hV := Vs_nonneg v hv x
  have h1 : 1 - searchH lam v v0 x ≠ 0 := (sub_pos.mpr hH).ne'
  have h2 : Vs v x + v0 ≠ 0 := by linarith
  have h3 := (hv ⟨0, hn⟩).ne'
  unfold estPrefNoPurchase
  rw [ash7_d0 lam v v0 hv hv0, ash7_first lam v v0 hn]
  field_simp

noncomputable def cf {n : ℕ} (lam : ℝ) (v : Fin n → ℝ) (v0 : ℝ) (y : ℕ) : ℝ :=
  (v0 + searchH lam v v0 y * Vs v y) / (1 - searchH lam v v0 y)

lemma cf_pos {n : ℕ} (lam : ℝ) (v : Fin n → ℝ) (v0 : ℝ) (hv : ∀ i, 0 < v i)
    (hv0 : 0 < v0) (hlam : 0 < lam) (y : ℕ) : 0 < cf lam v v0 y := by
  have hH := ash_H_lt_one lam v v0 hv hv0 hlam y
  have hV := Vs_nonneg v hv y
  have hHp : 0 < searchH lam v v0 y := Real.exp_pos _
  unfold cf
  exact div_pos (by positivity) (sub_pos.mpr hH)

lemma ash7_share {n : ℕ} (lam : ℝ) (v : Fin n → ℝ) (v0 : ℝ) (hv : ∀ i, 0 < v i)
    (hv0 : 0 < v0) (hlam : 0 < lam) (hn : 0 < n) (x x' : ℕ) :
    shareNoPurchase (estPref lam v v0 x) (estPrefNoPurchase lam v v0 x) x'
      = cf lam v v0 x / (Vs v x' + cf lam v v0 x) := by
  have hcpos := cf_pos lam v v0 hv hv0 hlam x
  have h3 := (hv ⟨0, hn⟩).ne'
  have hV' := Vs_nonneg v hv x'
  have hest : estPrefNoPurchase lam v v0 x = cf lam v v0 x / v ⟨0, hn⟩ :=
    ash7_estNP lam v v0 hv hv0 hlam hn x
  unfold shareNoPurchase
  simp only [ash_estPref lam v v0 hv hv0 hlam hn]
  rw [← Finset.sum_div, hest]
  change _ / (Vs v x' / v ⟨0, hn⟩ + _) = _
  have hd : Vs v x' + cf lam v v0 x ≠ 0 := by positivity
  field_simp

lemma ash7_c_eq {n : ℕ} (lam : ℝ) (v : Fin n → ℝ) (v0 : ℝ) (hv : ∀ i, 0 < v i)
    (hv0 : 0 < v0) (hlam : 0 < lam) (y : ℕ) :
    cf lam v v0 y
      = v0 + (fun δ : ℝ => δ * Real.exp (-(lam * δ)) / (1 - Real.exp (-(lam * δ))))
          (v0 + Vs v y) := by
  have hH := ash_H_lt_one lam v v0 hv hv0 hlam y
  have h1 : 1 - searchH lam v v0 y ≠ 0 := (sub_pos.mpr hH).ne'
  have hHdef : searchH lam v v0 y = Real.exp (-(lam * (v0 + Vs v y))) := rfl
  unfold cf
  simp only
  rw [← hHdef]
  field_simp
  ring

lemma ash7_c_anti {n : ℕ} (lam : ℝ) (v : Fin n → ℝ) (v0 : ℝ) (hv : ∀ i, 0 < v i)
    (hv0 : 0 < v0) (hlam : 0 < lam) {y y' : ℕ} (hyy : y ≤ y') :
    cf lam v v0 y' ≤ cf lam v v0 y := by
  rw [ash7_c_eq lam v v0 hv hv0 hlam, ash7_c_eq lam v v0 hv hv0 hlam]
  have hy := Vs_nonneg v hv y
  have hmono := Vs_mono v hv hyy
  have := z_anti lam hlam (Set.mem_Ioi.mpr (by linarith : 0 < v0 + Vs v y))
    (Set.mem_Ioi.mpr (by linarith : 0 < v0 + Vs v y')) (by linarith)
  simp only at this ⊢
  linarith

lemma ash7_key {n : ℕ} (lam : ℝ) (v : Fin n → ℝ) (v0 : ℝ) (hv : ∀ i, 0 < v i)
    (hv0 : 0 < v0) (hlam : 0 < lam) (x y : ℕ) :
    demandNoPurchase lam v v0 y - cf lam v v0 x / (Vs v y + cf lam v v0 x)
      = Vs v y * (1 - searchH lam v v0 y) * (cf lam v v0 y - cf lam v v0 x) /
        ((Vs v y + v0) * (Vs v y + cf lam v v0 x)) := by
  have hH := ash_H_lt_one lam v v0 hv hv0 hlam y
  have hV := Vs_nonneg v hv y
  have hcpos := cf_pos lam v v0 hv hv0 hlam x
  have h1 : 1 - searchH lam v v0 y ≠ 0 := (sub_pos.mpr hH).ne'
  have h2 : Vs v y + v0 ≠ 0 := by linarith
  have h3 : Vs v y + cf lam v v0 x ≠ 0 := by positivity
  rw [ash7_d0 lam v v0 hv hv0]
  unfold cf at *
  field_simp
  ring

theorem solution {n : ℕ} (lam : ℝ) (v : Fin n → ℝ) (v0 : ℝ)
    (hv : ∀ i, 0 < v i) (hanti : Antitone v) (hv0 : 0 < v0) (hlam : 0 < lam)
    (x : ℕ) (hx1 : 1 ≤ x) (hxn : x ≤ n) :
    (∀ x' : ℕ, x' < x →
        shareNoPurchase (estPref lam v v0 x) (estPrefNoPurchase lam v v0 x) x' ≤
          demandNoPurchase lam v v0 x') ∧
      (∀ x'' : ℕ, x < x'' → x'' ≤ n →
        demandNoPurchase lam v v0 x'' ≤
          shareNoPurchase (estPref lam v v0 x) (estPrefNoPurchase lam v v0 x) x'') := by
  have hn : 0 < n := by omega
  have hcpos := cf_pos lam v v0 hv hv0 hlam x
  refine ⟨fun x' hx' => ?_, fun x'' hx'' _ => ?_⟩
  · rw [ash7_share lam v v0 hv hv0 hlam hn]
    have hk := ash7_key lam v v0 hv hv0 hlam x x'
    have hV := Vs_nonneg v hv x'
    have hH := ash_H_lt_one lam v v0 hv hv0 hlam x'
    have hca := ash7_c_anti lam v v0 hv hv0 hlam hx'.le
    have : 0 ≤ Vs v x' * (1 - searchH lam v v0 x') * (cf lam v v0 x' - cf lam v v0 x) /
        ((Vs v x' + v0) * (Vs v x' + cf lam v v0 x)) := by
      apply div_nonneg
      · exact mul_nonneg (mul_nonneg hV (sub_pos.mpr hH).le) (sub_nonneg.mpr hca)
      · positivity
    linarith
  · rw [ash7_share lam v v0 hv hv0 hlam hn]
    have hk := ash7_key lam v v0 hv hv0 hlam x x''
    have hV := Vs_nonneg v hv x''
    have hH := ash_H_lt_one lam v v0 hv hv0 hlam x''
    have hca := ash7_c_anti lam v v0 hv hv0 hlam hx''.le
    have : Vs v x'' * (1 - searchH lam v v0 x'') * (cf lam v v0 x'' - cf lam v v0 x) /
        ((Vs v x'' + v0) * (Vs v x'' + cf lam v v0 x)) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg
      · exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hV (sub_pos.mpr hH).le)
          (sub_nonpos.mpr hca)
      · positivity
    linarith
