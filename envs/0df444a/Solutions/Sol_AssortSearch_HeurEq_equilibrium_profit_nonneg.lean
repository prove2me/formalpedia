-- Prove2me | solution 1 for AssortSearch.HeurEq.equilibrium_profit_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T01:04:37.935419+00:00
-- url     : https://prove2.me/submissions/bb5e280c-6976-4d3b-96c4-710019ad470b

import Mathlib
import Definitions.Def_AssortSearch_HeurEq_Model

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

lemma hq_popularSet_succ {n x : ℕ} (hx : x < n) :
    popularSet n (x + 1) = insert (⟨x, hx⟩ : Fin n) (popularSet n x) := by
  ext j
  simp only [popularSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · intro h
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
    · exact Or.inr h
    · exact Or.inl (Fin.ext h)
  · rintro (h | h)
    · subst h; simp
    · omega

lemma hq_not_mem {n x : ℕ} (hx : x < n) : (⟨x, hx⟩ : Fin n) ∉ popularSet n x := by
  simp [popularSet]

/-- General form: in an MNL model with positive antitone preferences `w`, positive
no-purchase preference `w0`, margins monotone in `w`, a depth `xs ≥ 1` maximising the profit
over `0, …, n` has no variant of negative profit. -/
lemma hq_general {n : ℕ} (m : Fin n → ℝ) (c : ℝ → ℝ) (w : Fin n → ℝ) (w0 : ℝ)
    (hw : ∀ i, 0 < w i) (hanti : Antitone w) (hw0 : 0 < w0)
    (hm : ∀ j k : Fin n, w k ≤ w j → m k ≤ m j)
    (hcc : ConcaveOn ℝ (Set.Icc 0 1) c) (hc0 : 0 ≤ c 0)
    (xs : ℕ) (h1 : 1 ≤ xs) (hn : xs ≤ n)
    (hmax : ∀ x : ℕ, x ≤ n → estProfit m c w w0 x ≤ estProfit m c w w0 xs)
    (i : Fin n) (hi : i.val < xs) :
    0 ≤ m i * share w w0 (popularSet n xs) i - c (share w w0 (popularSet n xs) i) := by
  obtain ⟨y, rfl⟩ : ∃ y, xs = y + 1 := ⟨xs - 1, by omega⟩
  have hy : y < n := by omega
  set L : Fin n := ⟨y, hy⟩ with hL
  set P := popularSet n y
  have hsucc : popularSet n (y + 1) = insert L P := hq_popularSet_succ hy
  have hLP : L ∉ P := hq_not_mem hy
  set D := ∑ j ∈ popularSet n (y + 1), w j + w0 with hD
  set D' := ∑ j ∈ P, w j + w0 with hD'
  have hD'pos : 0 < D' := add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun j _ => (hw j).le) hw0
  have hDeq : D = w L + D' := by
    rw [hD, hD', hsucc, Finset.sum_insert hLP]; ring
  have hDpos : 0 < D := by rw [hDeq]; linarith [hw L]
  have hDD : D' ≤ D := by rw [hDeq]; linarith [hw L]
  -- shares are in (0,1]
  have hsh_le : ∀ j ∈ popularSet n (y + 1), w j / D ≤ 1 := by
    intro j hj
    rw [div_le_one hDpos, hD]
    have := Finset.single_le_sum (f := w) (fun k _ => (hw k).le) hj
    linarith
  have hsh'_le : ∀ j ∈ P, w j / D' ≤ 1 := by
    intro j hj
    rw [div_le_one hD'pos, hD']
    have := Finset.single_le_sum (f := w) (fun k _ => (hw k).le) hj
    linarith
  let f : Fin n → ℝ → ℝ := fun j q => m j * q - c q
  have hshare : ∀ j, share w w0 (popularSet n (y + 1)) j = w j / D := fun j => rfl
  -- Step A: the last variant has nonnegative profit
  have hLnn : 0 ≤ f L (w L / D) := by
    by_contra hneg
    push Not at hneg
    have hprof : estProfit m c w w0 (y + 1) = (∑ k ∈ P, f k (w k / D)) + f L (w L / D) := by
      unfold estProfit
      rw [hsucc, Finset.sum_insert hLP]
      simp only [share]
      rw [← hsucc]
      ring
    by_cases hA : ∑ k ∈ P, f k (w k / D) < 0
    · have h0 := hmax 0 (Nat.zero_le _)
      have he : popularSet n 0 = ∅ := by ext j; simp [popularSet]
      have : estProfit m c w w0 0 = 0 := by simp [estProfit, he]
      linarith
    · push Not at hA
      have hy' := hmax y hy.le
      have hprof' : estProfit m c w w0 y = ∑ k ∈ P, f k (w k / D') := by
        unfold estProfit; rfl
      have hk : ∀ k ∈ P, (D / D') * f k (w k / D) ≤ f k (w k / D') := by
        intro k hk
        have hq : 0 < w k / D := div_pos (hw k) hDpos
        have hqq : w k / D ≤ w k / D' := div_le_div_of_nonneg_left (hw k).le hD'pos hDD
        have := hq_fratio c hcc hc0 (m k) hq hqq (hsh'_le k hk)
        have e : w k / D' = (D / D') * (w k / D) := by field_simp
        rw [e] at this ⊢
        have : (w k / D) * ((D / D') * f k (w k / D)) ≤ (w k / D) * f k (D / D' * (w k / D)) := by
          simp only [f]; nlinarith
        exact le_of_mul_le_mul_left this hq
      have hsum := Finset.sum_le_sum hk
      rw [← Finset.mul_sum] at hsum
      have ht : 1 ≤ D / D' := by rw [le_div_iff₀ hD'pos]; linarith
      have : ∑ k ∈ P, f k (w k / D) ≤ (D / D') * ∑ k ∈ P, f k (w k / D) := by
        nlinarith
      linarith
  -- Step B: every earlier variant
  have hiL : L ≤ i ∨ i ≤ L := le_total L i
  have hle : i ≤ L := by rw [Fin.le_def]; simp [hL]; omega
  have hwiL : w L ≤ w i := hanti hle
  have hmiL : m L ≤ m i := hm i L hwiL
  have hqL : 0 < w L / D := div_pos (hw L) hDpos
  have hqLi : w L / D ≤ w i / D := div_le_div_of_nonneg_right hwiL hDpos.le
  have hi1 : w i / D ≤ 1 := hsh_le i (by simp [popularSet]; omega)
  have hfi : 0 ≤ f i (w L / D) := by
    have : f L (w L / D) ≤ f i (w L / D) := by
      simp only [f]; nlinarith
    linarith
  have hfr := hq_fratio c hcc hc0 (m i) hqL hqLi hi1
  rw [hshare]
  have h2 : (w L / D) * 0 ≤ (w L / D) * (m i * (w i / D) - c (w i / D)) := by
    have : 0 ≤ (w i / D) * f i (w L / D) := mul_nonneg (by linarith) hfi
    simp only [f] at this; linarith
  exact le_of_mul_le_mul_left h2 hqL

theorem solution {n : ℕ} (lam : ℝ) (m : Fin n → ℝ) (c : ℝ → ℝ)
    (v : Fin n → ℝ) (v0 : ℝ)
    (hv : ∀ i, 0 < v i) (hanti : Antitone v) (hv0 : 0 < v0) (hlam : 0 < lam)
    (hm : ∀ j k : Fin n, v k ≤ v j → m k ≤ m j)
    (hcc : ConcaveOn ℝ (Set.Icc 0 1) c) (hcm : MonotoneOn c (Set.Icc 0 1))
    (hc0 : 0 ≤ c 0)
    (xstar : ℕ) (heq : IsHeuristicEquilibrium lam m c v v0 xstar)
    (i : Fin n) (hi : i.val < xstar) :
    0 ≤ m i * share (estPref lam v v0 xstar) (estPrefNoPurchase lam v v0 xstar)
          (popularSet n xstar) i -
        c (share (estPref lam v v0 xstar) (estPrefNoPurchase lam v v0 xstar)
          (popularSet n xstar) i) := by
  obtain ⟨h1, hxn, hmax⟩ := heq
  have hn : 0 < n := by omega
  have hv1 := hv ⟨0, hn⟩
  have hw : estPref lam v v0 xstar = fun i => v i / v ⟨0, hn⟩ :=
    funext fun i => ash_estPref lam v v0 hv hv0 hlam hn xstar i
  have hw0 : 0 < estPrefNoPurchase lam v v0 xstar := by
    rw [ash7_estNP lam v v0 hv hv0 hlam hn]
    exact div_pos (cf_pos lam v v0 hv hv0 hlam xstar) hv1
  refine hq_general m c _ _ ?_ ?_ hw0 ?_ hcc hc0 xstar h1 hxn hmax i hi
  · intro j; rw [hw]; exact div_pos (hv j) hv1
  · rw [hw]; intro a b hab; exact div_le_div_of_nonneg_right (hanti hab) hv1.le
  · intro j k hjk; rw [hw] at hjk
    exact hm j k ((div_le_div_iff_of_pos_right hv1).mp hjk)
