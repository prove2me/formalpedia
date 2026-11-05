-- Prove2me | solution 1 for AssortSearch.HeurEq.overestimate_narrower
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T01:05:43.784699+00:00
-- url     : https://prove2.me/submissions/dcc6834c-bcaa-4b75-b51d-a00992d135bc

import Mathlib
import Definitions.Def_AssortSearch_HeurEq_Model
import Theorems.Thm_AssortSearch_HeurEq_theorem_7
import Theorems.Thm_AssortSearch_HeurEq_equilibrium_profit_nonneg

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

lemma hq_ratio (c : ℝ → ℝ) (hcc : ConcaveOn ℝ (Set.Icc 0 1) c) (hc0 : 0 ≤ c 0)
    {q q' : ℝ} (hq : 0 < q) (hqq : q ≤ q') (hq1 : q' ≤ 1) : q * c q' ≤ q' * c q := by
  have hq' : 0 < q' := lt_of_lt_of_le hq hqq
  have ha : (0:ℝ) ≤ 1 - q / q' := by rw [sub_nonneg, div_le_one hq']; exact hqq
  have hb : (0:ℝ) ≤ q / q' := div_nonneg hq.le hq'.le
  have hab : (1 - q / q') + q / q' = 1 := by ring
  have h := hcc.2 (show (0:ℝ) ∈ Set.Icc (0:ℝ) 1 from ⟨le_refl 0, zero_le_one⟩)
    (show q' ∈ Set.Icc (0:ℝ) 1 from ⟨hq'.le, hq1⟩) ha hb hab
  have e : (1 - q / q') • (0:ℝ) + (q / q') • q' = q := by
    simp only [smul_eq_mul, mul_zero, zero_add]; field_simp
  rw [e] at h
  simp only [smul_eq_mul] at h
  have h2 : q' * ((1 - q / q') * c 0 + q / q' * c q') ≤ q' * c q :=
    mul_le_mul_of_nonneg_left h hq'.le
  have h3 : q' * ((1 - q / q') * c 0 + q / q' * c q') = (q' - q) * c 0 + q * c q' := by
    field_simp
  rw [h3] at h2
  nlinarith [mul_nonneg (sub_nonneg.mpr hqq) hc0]

lemma hq_fratio (c : ℝ → ℝ) (hcc : ConcaveOn ℝ (Set.Icc 0 1) c) (hc0 : 0 ≤ c 0) (mi : ℝ)
    {q q' : ℝ} (hq : 0 < q) (hqq : q ≤ q') (hq1 : q' ≤ 1) :
    q' * (mi * q - c q) ≤ q * (mi * q' - c q') := by
  have := hq_ratio c hcc hc0 hq hqq hq1
  nlinarith


lemma on_estShare {n : ℕ} (lam : ℝ) (v : Fin n → ℝ) (v0 : ℝ) (hv : ∀ i, 0 < v i)
    (hv0 : 0 < v0) (hlam : 0 < lam) (hn : 0 < n) (x x' : ℕ) (i : Fin n) :
    share (estPref lam v v0 x) (estPrefNoPurchase lam v v0 x) (popularSet n x') i
      = v i / (Vs v x' + cf lam v v0 x) := by
  have hcpos := cf_pos lam v v0 hv hv0 hlam x
  have h3 := (hv ⟨0, hn⟩).ne'
  have hV' := Vs_nonneg v hv x'
  have hest : estPrefNoPurchase lam v v0 x = cf lam v v0 x / v ⟨0, hn⟩ :=
    ash7_estNP lam v v0 hv hv0 hlam hn x
  unfold share
  simp only [ash_estPref lam v v0 hv hv0 hlam hn]
  rw [← Finset.sum_div, hest]
  change _ / (Vs v x' / v ⟨0, hn⟩ + _) = _
  have hd : Vs v x' + cf lam v v0 x ≠ 0 := by positivity
  field_simp

theorem solution {n : ℕ} (lam : ℝ) (m : Fin n → ℝ) (c : ℝ → ℝ)
    (v : Fin n → ℝ) (v0 : ℝ)
    (hv : ∀ i, 0 < v i) (hanti : Antitone v) (hv0 : 0 < v0) (hlam : 0 < lam)
    (hm : ∀ j k : Fin n, v k ≤ v j → m k ≤ m j)
    (hcc : ConcaveOn ℝ (Set.Icc 0 1) c) (hcm : MonotoneOn c (Set.Icc 0 1))
    (hc0 : 0 ≤ c 0)
    (xstar : ℕ) (heq : IsHeuristicEquilibrium lam m c v v0 xstar)
    (x : ℕ) (hx1 : 1 ≤ x) (hx : x < xstar) :
    trueProfit lam m c v v0 x ≤
      estProfit m c (estPref lam v v0 xstar) (estPrefNoPurchase lam v v0 xstar) x := by
  have hxs1 := heq.1
  have hxsn := heq.2.1
  have hn : 0 < n := by omega
  -- Theorem 7 at x*: q_0^m(x | v̂(x*)) ≤ d_0(x)
  have h7 := (theorem_7 lam v v0 hv hanti hv0 hlam xstar hxs1 hxsn).1 x hx
  rw [ash7_share lam v v0 hv hv0 hlam hn, ash7_d0 lam v v0 hv hv0] at h7
  set C := cf lam v v0 xstar with hC
  set V := Vs v x with hV
  set H := searchH lam v v0 x with hH
  have hCpos : 0 < C := cf_pos lam v v0 hv hv0 hlam xstar
  have hVnn : 0 ≤ V := Vs_nonneg v hv x
  have hH1 : H < 1 := ash_H_lt_one lam v v0 hv hv0 hlam x
  have hHpos : 0 < H := Real.exp_pos _
  -- the first variant is in the assortment, so V > 0
  have hVpos : 0 < V := by
    have hmem : (⟨0, hn⟩ : Fin n) ∈ popularSet n x := by simp [popularSet]; omega
    have := Finset.single_le_sum (f := v) (fun k _ => (hv k).le) hmem
    have := hv ⟨0, hn⟩
    simp only [hV, Vs]; linarith
  -- (1 - H)/(V + v0) ≤ 1/(V + C)
  have hkey : (1 - H) / (V + v0) ≤ 1 / (V + C) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)] at h7
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  unfold trueProfit estProfit
  apply Finset.sum_le_sum
  intro i hi
  have hix : i.val < x := by simpa [popularSet] using hi
  have hvi := hv i
  rw [on_estShare lam v v0 hv hv0 hlam hn]
  have hd : demand lam v v0 x i = v i * ((1 - H) / (V + v0)) := by
    rw [ash_demand_eq]; simp only [hH, hV, Vs]; ring
  rw [hd]
  set d := v i * ((1 - H) / (V + v0))
  set q := v i / (V + C)
  have hdpos : 0 < d := mul_pos hvi (div_pos (by linarith) (by linarith))
  have hdq : d ≤ q := by
    have := mul_le_mul_of_nonneg_left hkey hvi.le
    simpa [d, q, div_eq_mul_one_div (v i) (V + C)] using this
  have hVi : v i ≤ V := by
    simp only [hV, Vs]
    exact Finset.single_le_sum (f := v) (fun k _ => (hv k).le) hi
  have hq1 : q ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  -- the share at x* is smaller
  set qs := v i / (Vs v xstar + C)
  have hVV : V ≤ Vs v xstar := Vs_mono v hv hx.le
  have hqs : 0 < qs := div_pos hvi (by linarith)
  have hqsq : qs ≤ q := div_le_div_of_nonneg_left hvi.le (by linarith) (by linarith)
  have hnn := equilibrium_profit_nonneg lam m c v v0 hv hanti hv0 hlam hm hcc hcm hc0 xstar heq i
    (by omega)
  rw [on_estShare lam v v0 hv hv0 hlam hn] at hnn
  -- f_i(q) ≥ 0
  have hfq : 0 ≤ m i * q - c q := by
    have h := hq_fratio c hcc hc0 (m i) hqs hqsq hq1
    have : 0 ≤ qs * (m i * q - c q) := le_trans (mul_nonneg (by linarith) hnn) h
    exact le_of_mul_le_mul_left (by simpa using this) hqs
  -- f_i(d) ≤ f_i(q)
  have h := hq_fratio c hcc hc0 (m i) hdpos hdq hq1
  have h2 : q * (m i * d - c d) ≤ q * (m i * q - c q) := by nlinarith
  exact le_of_mul_le_mul_left h2 (by linarith)
