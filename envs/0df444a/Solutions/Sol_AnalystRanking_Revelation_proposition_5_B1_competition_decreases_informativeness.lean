-- Prove2me | solution 1 for AnalystRanking.Revelation.proposition_5_B1_competition_decreases_informativeness
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-06T13:13:49.057199+00:00
-- url     : https://prove2.me/submissions/21578532-16aa-4181-b25b-9c72db46a3ac

import Mathlib
import Definitions.Def_AnalystRanking_Revelation_IsCompEq
import Definitions.Def_AnalystRanking_Revelation_IsBenchEq
import Definitions.Def_AnalystRanking_Revelation_IsMostInformative
import Definitions.Def_AnalystRanking_Revelation_informativeness
import Definitions.Def_AnalystRanking_Revelation_qminCheck
import Definitions.Def_AnalystRanking_Revelation_phiConvexity

set_option autoImplicit false
set_option linter.all false

namespace P5R

open AnalystRanking.Revelation

/-! ### The concave, 1-homogeneous function `G x y = x y / (x + y)` -/

noncomputable def G (x y : ℝ) : ℝ := x * y / (x + y)

lemma G_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ G x y :=
  div_nonneg (mul_nonneg hx hy) (add_nonneg hx hy)

lemma G_hom {k x y : ℝ} (hk : 0 ≤ k) : G (k * x) (k * y) = k * G x y := by
  unfold G
  rcases hk.eq_or_lt with h | h
  · subst h; simp
  · have e : k * x + k * y = k * (x + y) := by ring
    rw [e, show k * x * (k * y) = k * (k * (x * y)) by ring, mul_div_mul_left _ _ h.ne',
      mul_div_assoc]

lemma G_add {x1 y1 x2 y2 : ℝ} (hx1 : 0 ≤ x1) (hy1 : 0 ≤ y1) (hx2 : 0 ≤ x2) (hy2 : 0 ≤ y2) :
    G x1 y1 + G x2 y2 ≤ G (x1 + x2) (y1 + y2) := by
  unfold G
  rcases (add_nonneg hx1 hy1).eq_or_lt with h1 | h1
  · have e1 : x1 = 0 := by linarith
    have e2 : y1 = 0 := by linarith
    subst e1; subst e2; simp
  rcases (add_nonneg hx2 hy2).eq_or_lt with h2 | h2
  · have e1 : x2 = 0 := by linarith
    have e2 : y2 = 0 := by linarith
    subst e1; subst e2; simp
  have h3 : 0 < x1 + x2 + (y1 + y2) := by linarith
  rw [div_add_div _ _ h1.ne' h2.ne', div_le_div_iff₀ (mul_pos h1 h2) h3]
  nlinarith [sq_nonneg (x1 * y2 - x2 * y1)]

lemma G_add_strict {x1 y1 x2 y2 : ℝ} (hx1 : 0 ≤ x1) (hy1 : 0 ≤ y1) (hx2 : 0 ≤ x2)
    (hy2 : 0 ≤ y2) (h1 : 0 < x1 + y1) (h2 : 0 < x2 + y2) (hne : x1 * y2 ≠ x2 * y1) :
    G x1 y1 + G x2 y2 < G (x1 + x2) (y1 + y2) := by
  unfold G
  have h3 : 0 < x1 + x2 + (y1 + y2) := by linarith
  rw [div_add_div _ _ h1.ne' h2.ne', div_lt_div_iff₀ (mul_pos h1 h2) h3]
  have hsq : 0 < (x1 * y2 - x2 * y1) ^ 2 := by
    have : x1 * y2 - x2 * y1 ≠ 0 := sub_ne_zero.mpr hne
    positivity
  nlinarith [hsq]

lemma G_sum {ι : Type*} (s : Finset ι) (x y : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hy : ∀ i, 0 ≤ y i) :
    ∑ i ∈ s, G (x i) (y i) ≤ G (∑ i ∈ s, x i) (∑ i ∈ s, y i) := by
  classical
  refine Finset.induction_on s (by simp [G]) ?_
  intro a t ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
  calc G (x a) (y a) + ∑ i ∈ t, G (x i) (y i)
      ≤ G (x a) (y a) + G (∑ i ∈ t, x i) (∑ i ∈ t, y i) := by linarith
    _ ≤ _ := G_add (hx a) (hy a) (Finset.sum_nonneg fun i _ => hx i)
        (Finset.sum_nonneg fun i _ => hy i)

lemma G_sum_strict {ι : Type*} [DecidableEq ι] (s : Finset ι) (x y : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j)
    (hpi : 0 < x i + y i) (hpj : 0 < x j + y j) (hne : x i * y j ≠ x j * y i) :
    ∑ k ∈ s, G (x k) (y k) < G (∑ k ∈ s, x k) (∑ k ∈ s, y k) := by
  have hj' : j ∈ s.erase i := Finset.mem_erase.mpr ⟨hij.symm, hj⟩
  have AG : G (x i) (y i) + ∑ k ∈ s.erase i, G (x k) (y k) = ∑ k ∈ s, G (x k) (y k) :=
    Finset.add_sum_erase s (fun k => G (x k) (y k)) hi
  have AX : x i + ∑ k ∈ s.erase i, x k = ∑ k ∈ s, x k := Finset.add_sum_erase s x hi
  have AY : y i + ∑ k ∈ s.erase i, y k = ∑ k ∈ s, y k := Finset.add_sum_erase s y hi
  have BG : G (x j) (y j) + ∑ k ∈ (s.erase i).erase j, G (x k) (y k)
      = ∑ k ∈ s.erase i, G (x k) (y k) :=
    Finset.add_sum_erase (s.erase i) (fun k => G (x k) (y k)) hj'
  have BX : x j + ∑ k ∈ (s.erase i).erase j, x k = ∑ k ∈ s.erase i, x k :=
    Finset.add_sum_erase (s.erase i) x hj'
  have BY : y j + ∑ k ∈ (s.erase i).erase j, y k = ∑ k ∈ s.erase i, y k :=
    Finset.add_sum_erase (s.erase i) y hj'
  rw [← AG, ← AX, ← AY, ← BG, ← BX, ← BY]
  have hR := G_sum ((s.erase i).erase j) x y hx hy
  have hS := G_add_strict (hx i) (hy i) (hx j) (hy j) hpi hpj hne
  set t := (s.erase i).erase j
  have ht1 : 0 ≤ ∑ k ∈ t, x k := Finset.sum_nonneg fun k _ => hx k
  have ht2 : 0 ≤ ∑ k ∈ t, y k := Finset.sum_nonneg fun k _ => hy k
  have hT := G_add (add_nonneg (hx i) (hx j)) (add_nonneg (hy i) (hy j)) ht1 ht2
  have e1 : x i + (x j + ∑ k ∈ t, x k) = (x i + x j) + ∑ k ∈ t, x k := by ring
  have e2 : y i + (y j + ∑ k ∈ t, y k) = (y i + y j) + ∑ k ∈ t, y k := by ring
  rw [e1, e2]
  linarith

/-! ### Garbling inequality -/

lemma garble {S M : Type*} [Fintype S] [Fintype M] (K : S → M → ℝ) (X Y : S → ℝ)
    (hK : ∀ s m, 0 ≤ K s m) (hK1 : ∀ s, ∑ m, K s m = 1) (hX : ∀ s, 0 ≤ X s)
    (hY : ∀ s, 0 ≤ Y s) :
    ∑ s, G (X s) (Y s) ≤ ∑ m, G (∑ s, K s m * X s) (∑ s, K s m * Y s) := by
  calc ∑ s, G (X s) (Y s) = ∑ s, ∑ m, K s m * G (X s) (Y s) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [← Finset.sum_mul, hK1, one_mul]
    _ = ∑ m, ∑ s, K s m * G (X s) (Y s) := Finset.sum_comm
    _ = ∑ m, ∑ s, G (K s m * X s) (K s m * Y s) := by
        refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun s _ => ?_
        rw [G_hom (hK s m)]
    _ ≤ _ := Finset.sum_le_sum fun m _ => G_sum _ _ _ (fun s => mul_nonneg (hK s m) (hX s))
        (fun s => mul_nonneg (hK s m) (hY s))

lemma garble_strict {S M : Type*} [Fintype S] [Fintype M] [DecidableEq S] (K : S → M → ℝ)
    (X Y : S → ℝ) (hK : ∀ s m, 0 ≤ K s m) (hK1 : ∀ s, ∑ m, K s m = 1) (hX : ∀ s, 0 ≤ X s)
    (hY : ∀ s, 0 ≤ Y s) (m0 : M) (s1 s2 : S) (h12 : s1 ≠ s2) (hk1 : 0 < K s1 m0)
    (hk2 : 0 < K s2 m0) (hp1 : 0 < X s1 + Y s1) (hp2 : 0 < X s2 + Y s2)
    (hne : X s1 * Y s2 ≠ X s2 * Y s1) :
    ∑ s, G (X s) (Y s) < ∑ m, G (∑ s, K s m * X s) (∑ s, K s m * Y s) := by
  calc ∑ s, G (X s) (Y s) = ∑ s, ∑ m, K s m * G (X s) (Y s) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [← Finset.sum_mul, hK1, one_mul]
    _ = ∑ m, ∑ s, K s m * G (X s) (Y s) := Finset.sum_comm
    _ = ∑ m, ∑ s, G (K s m * X s) (K s m * Y s) := by
        refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun s _ => ?_
        rw [G_hom (hK s m)]
    _ < _ := by
        apply Finset.sum_lt_sum (fun m _ => G_sum _ _ _ (fun s => mul_nonneg (hK s m) (hX s))
          (fun s => mul_nonneg (hK s m) (hY s)))
        refine ⟨m0, Finset.mem_univ _, ?_⟩
        apply G_sum_strict _ _ _ (fun s => mul_nonneg (hK s m0) (hX s))
          (fun s => mul_nonneg (hK s m0) (hY s)) (Finset.mem_univ s1) (Finset.mem_univ s2) h12
        · rw [← mul_add]; exact mul_pos hk1 hp1
        · rw [← mul_add]; exact mul_pos hk2 hp2
        · intro h
          apply hne
          have h' : K s1 m0 * K s2 m0 * (X s1 * Y s2 - X s2 * Y s1) = 0 := by
            linear_combination h
          rcases mul_eq_zero.1 h' with h'' | h''
          · exact absurd h'' (mul_pos hk1 hk2).ne'
          · linarith

/-! ### Normalized equilibrium conditions -/

def AL (q γ c : ℝ) : ℝ := (1 - q) * (γ ^ 2 + c) + q * ((1 - γ) ^ 2 + c)
def AH (q γ c : ℝ) : ℝ := q * (γ ^ 2 + c) + (1 - q) * ((1 - γ) ^ 2 + c)
def Bc (γ c : ℝ) : ℝ := γ * (1 - γ) - c

/-- `(w0 - w2)⁻¹ Pr(l) [U(l̂|l) - U(ĥ|l)]`, with `k = φ - 1`. -/
def nL (k q γ c h l : ℝ) : ℝ := k * (γ * (γ - q) + c - AL q γ c * l + Bc γ c * h) + (γ - q)
/-- `(w0 - w2)⁻¹ Pr(h) [U(ĥ|h) - U(l̂|h)]`, with `k = φ - 1`. -/
def nH (k q γ c h l : ℝ) : ℝ :=
  k * (γ * (γ - (1 - q)) + c - AH q γ c * h + Bc γ c * l) + (γ - (1 - q))

def CE (k q γ c : ℝ) (σ : ℝ × ℝ) : Prop :=
  0 ≤ σ.1 ∧ σ.1 ≤ 1 ∧ 0 ≤ σ.2 ∧ σ.2 ≤ 1 ∧ 1 - σ.2 ≤ σ.1 ∧
  (σ.1 < 1 → nH k q γ c σ.1 σ.2 ≤ 0) ∧ (0 < σ.1 → 0 ≤ nH k q γ c σ.1 σ.2) ∧
  (σ.2 < 1 → nL k q γ c σ.1 σ.2 ≤ 0) ∧ (0 < σ.2 → 0 ≤ nL k q γ c σ.1 σ.2)

lemma br_iff {x A B K n : ℝ} (hK : 0 < K) (hAB : A - B = K * n) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 → τ * A + (1 - τ) * B ≤ x * A + (1 - x) * B) ↔
      ((x < 1 → n ≤ 0) ∧ (0 < x → 0 ≤ n)) := by
  constructor
  · intro h
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · have h1 := h 1 zero_le_one le_rfl
      by_contra hn
      push_neg at hn
      have : 0 < (1 - x) * (K * n) := mul_pos (by linarith) (mul_pos hK hn)
      have e : (1 - x) * (K * n) = 1 * A + (1 - 1) * B - (x * A + (1 - x) * B) := by
        rw [← hAB]; ring
      linarith
    · have h0 := h 0 le_rfl zero_le_one
      by_contra hn
      push_neg at hn
      have : 0 < x * (K * -n) := mul_pos hx (mul_pos hK (by linarith))
      have e : x * (K * -n) = 0 * A + (1 - 0) * B - (x * A + (1 - x) * B) := by
        rw [mul_neg, ← hAB]; ring
      linarith
  · rintro ⟨h1, h2⟩ τ hτ0 hτ1
    have e : x * A + (1 - x) * B - (τ * A + (1 - τ) * B) = (x - τ) * (K * n) := by
      linear_combination (x - τ) * hAB
    rcases lt_trichotomy n 0 with hn | hn | hn
    · have hx : x = 0 := by
        by_contra hx
        have := h2 (lt_of_le_of_ne hx0 (Ne.symm hx))
        linarith
      subst hx
      have : 0 ≤ τ * (K * -n) := mul_nonneg hτ0 (mul_pos hK (by linarith)).le
      have e2 : (0 - τ) * (K * n) = τ * (K * -n) := by ring
      linarith
    · rw [hn, mul_zero, mul_zero] at e
      linarith
    · have hx : x = 1 := by
        by_contra hx
        have := h1 (lt_of_le_of_ne hx1 hx)
        linarith
      subst hx
      have : 0 ≤ (1 - τ) * (K * n) := mul_nonneg (by linarith) (mul_pos hK hn).le
      linarith

lemma spm_pos {q γ : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1) (s : Bool) :
    0 < sigProbMarg q γ s := by
  have a1 := mul_pos hq0 hγ0
  have a2 := mul_pos (sub_pos.2 hq1) (sub_pos.2 hγ1)
  have a3 := mul_pos hq0 (sub_pos.2 hγ1)
  have a4 := mul_pos (sub_pos.2 hq1) hγ0
  cases s <;> simp [sigProbMarg, Fintype.sum_bool, prior, sigMarg] <;> linarith

lemma dH (w1 w0 w2 q γ ρ : ℝ) (σ : ℝ × ℝ) (hW2 : 0 < w0 - w2) :
    interimPay w1 w0 w2 q γ ρ σ true true - interimPay w1 w0 w2 q γ ρ σ true false =
      ((w0 - w2) / sigProbMarg q γ true) *
        nH (phiConvexity w1 w0 w2 - 1) q γ (ρ * γ * (1 - γ)) σ.1 σ.2 := by
  have hw1 : w1 = phiConvexity w1 w0 w2 * (w0 - w2) + w0 := by
    unfold phiConvexity; field_simp; ring
  unfold interimPay
  rw [div_sub_div_same, div_mul_eq_mul_div]
  congr 1
  generalize phiConvexity w1 w0 w2 = φ at hw1 ⊢
  subst hw1
  simp [Fintype.sum_bool, prior, sigProb, sigMarg, fprob, rankPay, nH, AH, Bc]
  ring

lemma dL (w1 w0 w2 q γ ρ : ℝ) (σ : ℝ × ℝ) (hW2 : 0 < w0 - w2) :
    interimPay w1 w0 w2 q γ ρ σ false false - interimPay w1 w0 w2 q γ ρ σ false true =
      ((w0 - w2) / sigProbMarg q γ false) *
        nL (phiConvexity w1 w0 w2 - 1) q γ (ρ * γ * (1 - γ)) σ.1 σ.2 := by
  have hw1 : w1 = phiConvexity w1 w0 w2 * (w0 - w2) + w0 := by
    unfold phiConvexity; field_simp; ring
  unfold interimPay
  rw [div_sub_div_same, div_mul_eq_mul_div]
  congr 1
  generalize phiConvexity w1 w0 w2 = φ at hw1 ⊢
  subst hw1
  simp [Fintype.sum_bool, prior, sigProb, sigMarg, fprob, rankPay, nL, AL, Bc]
  ring

lemma bH (W q γ c : ℝ) (σ : ℝ × ℝ) :
    benchPay W q γ true true - benchPay W q γ true false =
      (W / sigProbMarg q γ true) * nH 0 q γ c σ.1 σ.2 := by
  unfold benchPay
  rw [div_sub_div_same, div_mul_eq_mul_div]
  congr 1
  simp [Fintype.sum_bool, prior, sigMarg, accPay, nH]
  ring

lemma bL (W q γ c : ℝ) (σ : ℝ × ℝ) :
    benchPay W q γ false false - benchPay W q γ false true =
      (W / sigProbMarg q γ false) * nL 0 q γ c σ.1 σ.2 := by
  unfold benchPay
  rw [div_sub_div_same, div_mul_eq_mul_div]
  congr 1
  simp [Fintype.sum_bool, prior, sigMarg, accPay, nL]
  ring

lemma comp_iff {w1 w0 w2 q γ ρ : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hW2 : 0 < w0 - w2) (σ : ℝ × ℝ) :
    IsCompEq w1 w0 w2 q γ ρ σ ↔ CE (phiConvexity w1 w0 w2 - 1) q γ (ρ * γ * (1 - γ)) σ := by
  have KH : 0 < (w0 - w2) / sigProbMarg q γ true := div_pos hW2 (spm_pos hq0 hq1 hγ0 hγ1 _)
  have KL : 0 < (w0 - w2) / sigProbMarg q γ false := div_pos hW2 (spm_pos hq0 hq1 hγ0 hγ1 _)
  unfold IsCompEq CE
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, hH, hL⟩
    have aH := (br_iff KH (dH w1 w0 w2 q γ ρ σ hW2) h1 h2).1 hH
    have aL := (br_iff KL (dL w1 w0 w2 q γ ρ σ hW2) h3 h4).1 hL
    exact ⟨h1, h2, h3, h4, h5, aH.1, aH.2, aL.1, aL.2⟩
  · rintro ⟨h1, h2, h3, h4, h5, a, b, c, d⟩
    exact ⟨h1, h2, h3, h4, h5, (br_iff KH (dH w1 w0 w2 q γ ρ σ hW2) h1 h2).2 ⟨a, b⟩,
      (br_iff KL (dL w1 w0 w2 q γ ρ σ hW2) h3 h4).2 ⟨c, d⟩⟩

lemma bench_iff {W q γ : ℝ} (c : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hW : 0 < W) (σ : ℝ × ℝ) :
    IsBenchEq W q γ σ ↔ CE 0 q γ c σ := by
  have KH : 0 < W / sigProbMarg q γ true := div_pos hW (spm_pos hq0 hq1 hγ0 hγ1 _)
  have KL : 0 < W / sigProbMarg q γ false := div_pos hW (spm_pos hq0 hq1 hγ0 hγ1 _)
  unfold IsBenchEq CE
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, hH, hL⟩
    have aH := (br_iff KH (bH W q γ c σ) h1 h2).1 hH
    have aL := (br_iff KL (bL W q γ c σ) h3 h4).1 hL
    exact ⟨h1, h2, h3, h4, h5, aH.1, aH.2, aL.1, aL.2⟩
  · rintro ⟨h1, h2, h3, h4, h5, x1, x2, x3, x4⟩
    exact ⟨h1, h2, h3, h4, h5, (br_iff KH (bH W q γ c σ) h1 h2).2 ⟨x1, x2⟩,
      (br_iff KL (bL W q γ c σ) h3 h4).2 ⟨x3, x4⟩⟩

/-! ### Symmetry `q ↦ 1 - q`, `(σʰ, σˡ) ↦ (σˡ, σʰ)` -/

lemma nL_swap (k q γ c h l : ℝ) : nL k q γ c h l = nH k (1 - q) γ c l h := by
  unfold nL nH AL AH; ring

lemma nH_swap (k q γ c h l : ℝ) : nH k q γ c h l = nL k (1 - q) γ c l h := by
  unfold nL nH AL AH; ring

lemma CE_swap {k q γ c : ℝ} (σ : ℝ × ℝ) : CE k q γ c σ ↔ CE k (1 - q) γ c (σ.2, σ.1) := by
  unfold CE
  simp only [← nL_swap, ← nH_swap]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, a, b, c, d⟩
    exact ⟨h3, h4, h1, h2, by linarith, c, d, a, b⟩
  · rintro ⟨h1, h2, h3, h4, h5, a, b, c, d⟩
    exact ⟨h3, h4, h1, h2, by linarith, c, d, a, b⟩

lemma J_swap (γ ρ : ℝ) (σ : ℝ × ℝ) (ω mi mj : Bool) :
    fcastJoint γ ρ σ ω mi mj = fcastJoint γ ρ (σ.2, σ.1) (!ω) (!mi) (!mj) := by
  cases ω <;> cases mi <;> cases mj <;>
    simp [fcastJoint, Fintype.sum_bool, sigProb, sigMarg, fprob] <;> ring

lemma E_swap (q γ ρ : ℝ) (σ : ℝ × ℝ) :
    expPostVar q γ ρ σ = expPostVar (1 - q) γ ρ (σ.2, σ.1) := by
  unfold expPostVar
  simp only [Fintype.sum_bool, J_swap γ ρ σ, Bool.not_true, Bool.not_false,
    sub_sub_cancel]
  ring

lemma Pi_swap (q γ ρ : ℝ) (σ : ℝ × ℝ) :
    informativeness q γ ρ σ = informativeness (1 - q) γ ρ (σ.2, σ.1) := by
  unfold informativeness
  rw [E_swap q γ ρ σ, sub_sub_cancel, mul_comm q]

/-! ### Expected posterior variance as a garbling sum -/

lemma sigProb_nonneg {γ ρ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (ω s t : Bool) : 0 ≤ sigProb γ ρ ω s t := by
  have h1 : 0 ≤ 1 - γ := by linarith
  have hc : 0 ≤ ρ * γ * (1 - γ) := mul_nonneg (mul_nonneg hρ0 hγ0) h1
  have hb : 0 ≤ (1 - ρ) * (γ * (1 - γ)) := mul_nonneg (by linarith) (mul_nonneg hγ0 h1)
  have g2 : 0 ≤ γ * γ := mul_nonneg hγ0 hγ0
  have g3 : 0 ≤ (1 - γ) * (1 - γ) := mul_nonneg h1 h1
  cases ω <;> cases s <;> cases t <;> simp only [sigProb, sigMarg] <;> norm_num <;> linarith

noncomputable def Kf (σ : ℝ × ℝ) (s m : Bool × Bool) : ℝ := fprob σ s.1 m.1 * fprob σ s.2 m.2

lemma fprob_nonneg {σ : ℝ × ℝ} (h0 : 0 ≤ σ.1) (h1 : σ.1 ≤ 1) (l0 : 0 ≤ σ.2) (l1 : σ.2 ≤ 1)
    (s m : Bool) : 0 ≤ fprob σ s m := by
  cases s <;> cases m <;> simp [fprob] <;> linarith

lemma Kf_nonneg {σ : ℝ × ℝ} (h0 : 0 ≤ σ.1) (h1 : σ.1 ≤ 1) (l0 : 0 ≤ σ.2) (l1 : σ.2 ≤ 1)
    (s m : Bool × Bool) : 0 ≤ Kf σ s m :=
  mul_nonneg (fprob_nonneg h0 h1 l0 l1 _ _) (fprob_nonneg h0 h1 l0 l1 _ _)

lemma Kf_sum (σ : ℝ × ℝ) (s : Bool × Bool) : ∑ m, Kf σ s m = 1 := by
  rcases s with ⟨a, b⟩
  cases a <;> cases b <;> simp [Kf, fprob, Fintype.sum_prod_type, Fintype.sum_bool] <;> ring

lemma XJ (γ ρ c : ℝ) (σ : ℝ × ℝ) (ω : Bool) (m : Bool × Bool) :
    ∑ s : Bool × Bool, Kf σ s m * (c * sigProb γ ρ ω s.1 s.2) = c * fcastJoint γ ρ σ ω m.1 m.2 := by
  simp only [fcastJoint, Kf, Fintype.sum_prod_type, Fintype.sum_bool]
  ring

lemma E_eq (q γ ρ : ℝ) (σ : ℝ × ℝ) :
    expPostVar q γ ρ σ = ∑ m : Bool × Bool,
      G (∑ s : Bool × Bool, Kf σ s m * (q * sigProb γ ρ true s.1 s.2))
        (∑ s : Bool × Bool, Kf σ s m * ((1 - q) * sigProb γ ρ false s.1 s.2)) := by
  simp only [XJ]
  rw [Fintype.sum_prod_type]
  rfl

/-- Garbling: if each analyst's forecast under `σ'` is a post-processing of his forecast under
`σ` by the stochastic kernel `K`, the expected posterior variance can only grow. -/
lemma E_mono_gen {q γ ρ : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {σ σ' : ℝ × ℝ} (h0 : 0 ≤ σ.1) (h1 : σ.1 ≤ 1) (l0 : 0 ≤ σ.2)
    (l1 : σ.2 ≤ 1) (K : Bool → Bool → ℝ) (hK : ∀ k m, 0 ≤ K k m)
    (hK1 : ∀ k, K k true + K k false = 1)
    (hc : ∀ s m, fprob σ' s m = fprob σ s true * K true m + fprob σ s false * K false m) :
    expPostVar q γ ρ σ ≤ expPostVar q γ ρ σ' := by
  set KK : Bool × Bool → Bool × Bool → ℝ := fun (k m : Bool × Bool) => K k.1 m.1 * K k.2 m.2 with hKK
  have hrw : ∀ (m : Bool × Bool) (Z : Bool × Bool → ℝ),
      ∑ s : Bool × Bool, Kf σ' s m * Z s = ∑ k : Bool × Bool, KK k m * ∑ s, Kf σ s k * Z s := by
    intro m Z
    simp only [hKK, Kf, hc, Fintype.sum_prod_type, Fintype.sum_bool]
    ring
  rw [E_eq, E_eq]
  simp only [hrw]
  apply garble KK
  · intro k m; exact mul_nonneg (hK _ _) (hK _ _)
  · intro k
    simp only [hKK, Fintype.sum_prod_type, Fintype.sum_bool]
    have a := hK1 k.1
    have b := hK1 k.2
    linear_combination (K k.2 true + K k.2 false) * a + b
  · intro k
    exact Finset.sum_nonneg fun s _ => mul_nonneg (Kf_nonneg h0 h1 l0 l1 _ _)
      (mul_nonneg hq0 (sigProb_nonneg hγ0 hγ1 hρ0 hρ1 _ _ _))
  · intro k
    exact Finset.sum_nonneg fun s _ => mul_nonneg (Kf_nonneg h0 h1 l0 l1 _ _)
      (mul_nonneg (by linarith) (sigProb_nonneg hγ0 hγ1 hρ0 hρ1 _ _ _))

lemma E_mono_gen_strict {q γ ρ : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {σ σ' : ℝ × ℝ} (h0 : 0 ≤ σ.1) (h1 : σ.1 ≤ 1) (l0 : 0 ≤ σ.2)
    (l1 : σ.2 ≤ 1) (K : Bool → Bool → ℝ) (hK : ∀ k m, 0 ≤ K k m)
    (hK1 : ∀ k, K k true + K k false = 1)
    (hc : ∀ s m, fprob σ' s m = fprob σ s true * K true m + fprob σ s false * K false m)
    (m0 k1 k2 : Bool × Bool) (h12 : k1 ≠ k2) (hk1 : 0 < K k1.1 m0.1 * K k1.2 m0.2)
    (hk2 : 0 < K k2.1 m0.1 * K k2.2 m0.2)
    (hp1 : 0 < fcastJoint γ ρ σ true k1.1 k1.2) (hp2 : 0 < fcastJoint γ ρ σ true k2.1 k2.2)
    (hdet : fcastJoint γ ρ σ true k1.1 k1.2 * fcastJoint γ ρ σ false k2.1 k2.2 ≠
      fcastJoint γ ρ σ true k2.1 k2.2 * fcastJoint γ ρ σ false k1.1 k1.2) :
    expPostVar q γ ρ σ < expPostVar q γ ρ σ' := by
  set KK : Bool × Bool → Bool × Bool → ℝ := fun (k m : Bool × Bool) => K k.1 m.1 * K k.2 m.2 with hKK
  have hrw : ∀ (m : Bool × Bool) (Z : Bool × Bool → ℝ),
      ∑ s : Bool × Bool, Kf σ' s m * Z s = ∑ k : Bool × Bool, KK k m * ∑ s, Kf σ s k * Z s := by
    intro m Z
    simp only [hKK, Kf, hc, Fintype.sum_prod_type, Fintype.sum_bool]
    ring
  have hJn : ∀ (ω : Bool) (k : Bool × Bool), 0 ≤ fcastJoint γ ρ σ ω k.1 k.2 := by
    intro ω k
    have := Finset.sum_nonneg fun (s : Bool × Bool) (_ : s ∈ Finset.univ) =>
      mul_nonneg (Kf_nonneg h0 h1 l0 l1 s k)
        (mul_nonneg zero_le_one (sigProb_nonneg hγ0 hγ1 hρ0 hρ1 ω s.1 s.2))
    rw [XJ, one_mul] at this
    exact this
  rw [E_eq, E_eq]
  simp only [hrw]
  refine garble_strict KK _ _ ?_ ?_ ?_ ?_ m0 k1 k2 h12 hk1 hk2 ?_ ?_ ?_
  · intro k m; exact mul_nonneg (hK _ _) (hK _ _)
  · intro k
    simp only [hKK, Fintype.sum_prod_type, Fintype.sum_bool]
    have a := hK1 k.1
    have b := hK1 k.2
    linear_combination (K k.2 true + K k.2 false) * a + b
  · intro k
    exact Finset.sum_nonneg fun s _ => mul_nonneg (Kf_nonneg h0 h1 l0 l1 _ _)
      (mul_nonneg hq0.le (sigProb_nonneg hγ0 hγ1 hρ0 hρ1 _ _ _))
  · intro k
    exact Finset.sum_nonneg fun s _ => mul_nonneg (Kf_nonneg h0 h1 l0 l1 _ _)
      (mul_nonneg (by linarith) (sigProb_nonneg hγ0 hγ1 hρ0 hρ1 _ _ _))
  · rw [XJ, XJ]
    have := mul_pos hq0 hp1
    have := mul_nonneg (sub_pos.2 hq1).le (hJn false k1)
    linarith
  · rw [XJ, XJ]
    have := mul_pos hq0 hp2
    have := mul_nonneg (sub_pos.2 hq1).le (hJn false k2)
    linarith
  · rw [XJ, XJ, XJ, XJ]
    intro h
    apply hdet
    have hq : q * (1 - q) ≠ 0 := (mul_pos hq0 (sub_pos.2 hq1)).ne'
    apply mul_left_cancel₀ hq
    linear_combination h

/-! ### One-coordinate garbling steps -/

/-- Lowering `σˡ` from `l` to `l'` (keeping `σʰ = h`, `h + l' ≥ 1`) is a garbling. -/
noncomputable def Kl (h l l' : ℝ) : Bool → Bool → ℝ
  | true, true => 1 - (1 - h) * (l - l') / (h + l - 1)
  | true, false => (1 - h) * (l - l') / (h + l - 1)
  | false, true => h * (l - l') / (h + l - 1)
  | false, false => 1 - h * (l - l') / (h + l - 1)

lemma lstep_K {h l l' : ℝ} (hD : 0 < h + l - 1) (s m : Bool) :
    fprob (h, l') s m = fprob (h, l) s true * Kl h l l' true m + fprob (h, l) s false * Kl h l l' false m := by
  have hD' := hD.ne'
  cases s <;> cases m <;> simp [fprob, Kl] <;> field_simp <;> ring

lemma lstep {q γ ρ : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {h l l' : ℝ} (h1 : h ≤ 1) (hl : l ≤ 1)
    (hll : l' ≤ l) (hsum : 1 ≤ h + l') (hl0 : 0 ≤ l') :
    expPostVar q γ ρ (h, l) ≤ expPostVar q γ ρ (h, l') := by
  rcases hll.eq_or_lt with e | hlt
  · rw [e]
  have h0 : 0 < h := by linarith
  have hD : 0 < h + l - 1 := by linarith
  have hy0 : 0 ≤ h * (l - l') / (h + l - 1) := div_nonneg (mul_nonneg h0.le (by linarith)) hD.le
  have hy1 : h * (l - l') / (h + l - 1) ≤ 1 := by
    rw [div_le_one hD]; linarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - h) (by linarith : (0:ℝ) ≤ l - l')]
  have ha0 : 0 ≤ (1 - h) * (l - l') / (h + l - 1) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) hD.le
  have ha1 : (1 - h) * (l - l') / (h + l - 1) ≤ 1 := by
    rw [div_le_one hD]; linarith [mul_nonneg h0.le (by linarith : (0:ℝ) ≤ l - l')]
  refine E_mono_gen hq0 hq1 hγ0 hγ1 hρ0 hρ1 (σ := (h, l)) h0.le h1 (by linarith) hl
    (Kl h l l')
    ?_ ?_ ?_
  · intro k m; cases k <;> cases m <;> simp only [Kl] <;> linarith
  · intro k; cases k <;> simp only [Kl] <;> ring
  · intro s m
    exact lstep_K hD s m

section Jvals
variable (γ ρ h l : ℝ)

lemma J_TTT : fcastJoint γ ρ (h, l) true true true =
    (γ ^ 2 + ρ * γ * (1 - γ)) * h ^ 2 + 2 * (γ * (1 - γ) - ρ * γ * (1 - γ)) * h * (1 - l)
      + ((1 - γ) ^ 2 + ρ * γ * (1 - γ)) * (1 - l) ^ 2 := by
  simp [fcastJoint, Fintype.sum_bool, sigProb, sigMarg, fprob]; ring

lemma J_FTT : fcastJoint γ ρ (h, l) false true true =
    ((1 - γ) ^ 2 + ρ * γ * (1 - γ)) * h ^ 2 + 2 * (γ * (1 - γ) - ρ * γ * (1 - γ)) * h * (1 - l)
      + (γ ^ 2 + ρ * γ * (1 - γ)) * (1 - l) ^ 2 := by
  simp [fcastJoint, Fintype.sum_bool, sigProb, sigMarg, fprob]; ring

lemma J_TFT : fcastJoint γ ρ (h, l) true false true =
    (γ ^ 2 + ρ * γ * (1 - γ)) * (1 - h) * h
      + (γ * (1 - γ) - ρ * γ * (1 - γ)) * ((1 - h) * (1 - l) + l * h)
      + ((1 - γ) ^ 2 + ρ * γ * (1 - γ)) * l * (1 - l) := by
  simp [fcastJoint, Fintype.sum_bool, sigProb, sigMarg, fprob]; ring

lemma J_FFT : fcastJoint γ ρ (h, l) false false true =
    ((1 - γ) ^ 2 + ρ * γ * (1 - γ)) * (1 - h) * h
      + (γ * (1 - γ) - ρ * γ * (1 - γ)) * ((1 - h) * (1 - l) + l * h)
      + (γ ^ 2 + ρ * γ * (1 - γ)) * l * (1 - l) := by
  simp [fcastJoint, Fintype.sum_bool, sigProb, sigMarg, fprob]; ring

lemma J_TFF : fcastJoint γ ρ (h, l) true false false =
    (γ ^ 2 + ρ * γ * (1 - γ)) * (1 - h) ^ 2 + 2 * (γ * (1 - γ) - ρ * γ * (1 - γ)) * (1 - h) * l
      + ((1 - γ) ^ 2 + ρ * γ * (1 - γ)) * l ^ 2 := by
  simp [fcastJoint, Fintype.sum_bool, sigProb, sigMarg, fprob]; ring

lemma J_FFF : fcastJoint γ ρ (h, l) false false false =
    ((1 - γ) ^ 2 + ρ * γ * (1 - γ)) * (1 - h) ^ 2 + 2 * (γ * (1 - γ) - ρ * γ * (1 - γ)) * (1 - h) * l
      + (γ ^ 2 + ρ * γ * (1 - γ)) * l ^ 2 := by
  simp [fcastJoint, Fintype.sum_bool, sigProb, sigMarg, fprob]; ring

end Jvals

lemma lstep_strict {q γ ρ : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hγh : 1 / 2 < γ) (hγ1 : γ < 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {h l l' : ℝ} (h1 : h ≤ 1) (hl : l ≤ 1)
    (hll : l' < l) (hsum : 1 ≤ h + l') (hl0 : 0 ≤ l') :
    expPostVar q γ ρ (h, l) < expPostVar q γ ρ (h, l') := by
  have hγ0 : 0 ≤ γ := by linarith
  have h0 : 0 < h := by linarith
  have hD : 0 < h + l - 1 := by linarith
  have hy0 : 0 < h * (l - l') / (h + l - 1) := div_pos (mul_pos h0 (by linarith)) hD
  have hy1 : h * (l - l') / (h + l - 1) ≤ 1 := by
    rw [div_le_one hD]; linarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - h) (by linarith : (0:ℝ) ≤ l - l')]
  have ha0 : 0 ≤ (1 - h) * (l - l') / (h + l - 1) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) hD.le
  have ha1 : (1 - h) * (l - l') / (h + l - 1) < 1 := by
    rw [div_lt_one hD]; linarith [mul_pos h0 (by linarith : (0:ℝ) < l - l')]
  set c := ρ * γ * (1 - γ) with hc
  have hcn : 0 ≤ c := mul_nonneg (mul_nonneg hρ0 hγ0) (by linarith)
  have hδ : 0 ≤ γ * (1 - γ) - c := by
    rw [hc]; nlinarith [mul_nonneg (sub_nonneg.2 hρ1) (mul_nonneg hγ0 (sub_nonneg.2 hγ1.le))]
  have hα : 0 < γ ^ 2 + c := by have := pow_pos (by linarith : (0:ℝ) < γ) 2; linarith
  have hβ : 0 < (1 - γ) ^ 2 + c := by have := pow_pos (by linarith : (0:ℝ) < 1 - γ) 2; linarith
  have hαβ : 0 < 2 * γ - 1 := by linarith
  have key := E_mono_gen_strict hq0 hq1 hγ0 hγ1.le hρ0 hρ1 (σ := (h, l)) (σ' := (h, l'))
    h0.le h1 (by linarith) hl
    (Kl h l l')
    (by intro k m; cases k <;> cases m <;> simp only [Kl] <;> linarith)
    (by intro k; cases k <;> simp only [Kl] <;> ring)
    (fun s m => lstep_K hD s m)
  rcases hl.lt_or_eq with hl1 | hl1
  · -- `σˡ < 1`: merge `(ĥ, ĥ)` and `(l̂, ĥ)`
    refine key (true, true) (true, true) (false, true) (by decide) ?_ ?_ ?_ ?_ ?_
    · dsimp only [Kl]; exact mul_pos (by linarith) (by linarith)
    · dsimp only [Kl]; exact mul_pos hy0 (by linarith)
    · rw [J_TTT]
      have : 0 < (γ ^ 2 + c) * h ^ 2 := mul_pos hα (pow_pos h0 2)
      have : 0 ≤ 2 * (γ * (1 - γ) - c) * h * (1 - l) :=
        mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hδ) h0.le) (by linarith)
      have : 0 ≤ ((1 - γ) ^ 2 + c) * (1 - l) ^ 2 := mul_nonneg hβ.le (sq_nonneg _)
      linarith
    · rw [J_TFT]
      have : 0 ≤ (γ ^ 2 + c) * (1 - h) * h := mul_nonneg (mul_nonneg hα.le (by linarith)) h0.le
      have : 0 ≤ (γ * (1 - γ) - c) * ((1 - h) * (1 - l) + l * h) :=
        mul_nonneg hδ (add_nonneg (mul_nonneg (by linarith) (by linarith))
          (mul_nonneg (by linarith) h0.le))
      have : 0 < ((1 - γ) ^ 2 + c) * l * (1 - l) ∨ 0 < (γ ^ 2 + c) * (1 - h) * h := by
        rcases h1.lt_or_eq with hh | hh
        · exact Or.inr (mul_pos (mul_pos hα (by linarith)) h0)
        · exact Or.inl (mul_pos (mul_pos hβ (by linarith)) (by linarith))
      have hβt : 0 ≤ ((1 - γ) ^ 2 + c) * l * (1 - l) :=
        mul_nonneg (mul_nonneg hβ.le (by linarith)) (by linarith)
      rcases this with this | this <;> linarith
    · rw [J_TTT, J_FFT, J_TFT, J_FTT]
      intro he
      have hpos : 0 < (h + l - 1) * (2 * γ - 1) * ((γ * (1 - γ) - c) * (h ^ 2 + (1 - l) ^ 2)
          + ((γ ^ 2 + c) + ((1 - γ) ^ 2 + c)) * h * (1 - l)) := by
        refine mul_pos (mul_pos hD hαβ) ?_
        have : 0 < ((γ ^ 2 + c) + ((1 - γ) ^ 2 + c)) * h * (1 - l) :=
          mul_pos (mul_pos (by linarith) h0) (by linarith)
        have : 0 ≤ (γ * (1 - γ) - c) * (h ^ 2 + (1 - l) ^ 2) := mul_nonneg hδ (by positivity)
        linarith
      have hid : ((γ ^ 2 + c) * h ^ 2 + 2 * (γ * (1 - γ) - c) * h * (1 - l)
            + ((1 - γ) ^ 2 + c) * (1 - l) ^ 2) *
          (((1 - γ) ^ 2 + c) * (1 - h) * h + (γ * (1 - γ) - c) * ((1 - h) * (1 - l) + l * h)
            + (γ ^ 2 + c) * l * (1 - l)) -
          ((γ ^ 2 + c) * (1 - h) * h + (γ * (1 - γ) - c) * ((1 - h) * (1 - l) + l * h)
            + ((1 - γ) ^ 2 + c) * l * (1 - l)) *
          (((1 - γ) ^ 2 + c) * h ^ 2 + 2 * (γ * (1 - γ) - c) * h * (1 - l)
            + (γ ^ 2 + c) * (1 - l) ^ 2)
          = (h + l - 1) * (2 * γ - 1) * ((γ * (1 - γ) - c) * (h ^ 2 + (1 - l) ^ 2)
            + ((γ ^ 2 + c) + ((1 - γ) ^ 2 + c)) * h * (1 - l)) := by ring
      linarith
  · subst hl1
    rcases h1.lt_or_eq with hh | hh
    · -- `σˡ = 1`, `σʰ < 1`: merge `(l̂, ĥ)` and `(l̂, l̂)`
      refine key (true, true) (false, true) (false, false) (by decide) ?_ ?_ ?_ ?_ ?_
      · dsimp only [Kl]; exact mul_pos hy0 (by linarith)
      · dsimp only [Kl]; exact mul_pos hy0 hy0
      · rw [J_TFT]
        have : 0 < (γ ^ 2 + c) * (1 - h) * h := mul_pos (mul_pos hα (by linarith)) h0
        have : 0 ≤ (γ * (1 - γ) - c) * ((1 - h) * (1 - 1) + 1 * h) :=
          mul_nonneg hδ (by nlinarith)
        nlinarith
      · rw [J_TFF]
        have : 0 ≤ (γ ^ 2 + c) * (1 - h) ^ 2 := mul_nonneg hα.le (sq_nonneg _)
        have : 0 ≤ 2 * (γ * (1 - γ) - c) * (1 - h) * 1 :=
          mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hδ) (by linarith)) zero_le_one
        nlinarith
      · rw [J_TFT, J_FFF, J_TFF, J_FFT]
        intro he
        have hpos : 0 < (h + 1 - 1) * (2 * γ - 1) * ((γ * (1 - γ) - c) * ((1 - h) ^ 2 + 1 ^ 2)
            + ((γ ^ 2 + c) + ((1 - γ) ^ 2 + c)) * (1 - h) * 1) := by
          refine mul_pos (mul_pos (by linarith) hαβ) ?_
          have : 0 < ((γ ^ 2 + c) + ((1 - γ) ^ 2 + c)) * (1 - h) * 1 :=
            mul_pos (mul_pos (by linarith) (by linarith)) one_pos
          have : 0 ≤ (γ * (1 - γ) - c) * ((1 - h) ^ 2 + 1 ^ 2) := mul_nonneg hδ (by positivity)
          linarith
        have hid : ((γ ^ 2 + c) * (1 - h) * h + (γ * (1 - γ) - c) * ((1 - h) * (1 - 1) + 1 * h)
              + ((1 - γ) ^ 2 + c) * 1 * (1 - 1)) *
            (((1 - γ) ^ 2 + c) * (1 - h) ^ 2 + 2 * (γ * (1 - γ) - c) * (1 - h) * 1
              + (γ ^ 2 + c) * 1 ^ 2) -
            ((γ ^ 2 + c) * (1 - h) ^ 2 + 2 * (γ * (1 - γ) - c) * (1 - h) * 1
              + ((1 - γ) ^ 2 + c) * 1 ^ 2) *
            (((1 - γ) ^ 2 + c) * (1 - h) * h + (γ * (1 - γ) - c) * ((1 - h) * (1 - 1) + 1 * h)
              + (γ ^ 2 + c) * 1 * (1 - 1))
            = (h + 1 - 1) * (2 * γ - 1) * ((γ * (1 - γ) - c) * ((1 - h) ^ 2 + 1 ^ 2)
              + ((γ ^ 2 + c) + ((1 - γ) ^ 2 + c)) * (1 - h) * 1) := by ring
        linarith
    · -- `σ = (1, 1)`: merge `(ĥ, ĥ)` and `(l̂, l̂)`
      subst hh
      refine key (true, true) (true, true) (false, false) (by decide) ?_ ?_ ?_ ?_ ?_
      · dsimp only [Kl]; exact mul_pos (by linarith) (by linarith)
      · dsimp only [Kl]; exact mul_pos hy0 hy0
      · rw [J_TTT]; nlinarith
      · rw [J_TFF]; nlinarith
      · rw [J_TTT, J_FFF, J_TFF, J_FTT]
        intro he
        have hid : ((γ ^ 2 + c) * 1 ^ 2 + 2 * (γ * (1 - γ) - c) * 1 * (1 - 1)
              + ((1 - γ) ^ 2 + c) * (1 - 1) ^ 2) *
            (((1 - γ) ^ 2 + c) * (1 - 1) ^ 2 + 2 * (γ * (1 - γ) - c) * (1 - 1) * 1
              + (γ ^ 2 + c) * 1 ^ 2) -
            ((γ ^ 2 + c) * (1 - 1) ^ 2 + 2 * (γ * (1 - γ) - c) * (1 - 1) * 1
              + ((1 - γ) ^ 2 + c) * 1 ^ 2) *
            (((1 - γ) ^ 2 + c) * 1 ^ 2 + 2 * (γ * (1 - γ) - c) * 1 * (1 - 1)
              + (γ ^ 2 + c) * (1 - 1) ^ 2)
            = (2 * γ - 1) * ((γ ^ 2 + c) + ((1 - γ) ^ 2 + c)) := by ring
        have : 0 < (2 * γ - 1) * ((γ ^ 2 + c) + ((1 - γ) ^ 2 + c)) := mul_pos hαβ (by linarith)
        linarith

lemma hstep {q γ ρ : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {h h' l : ℝ} (h1 : h ≤ 1) (hl : l ≤ 1)
    (hhh : h' ≤ h) (hsum : 1 ≤ h' + l) (hh0 : 0 ≤ h') :
    expPostVar q γ ρ (h, l) ≤ expPostVar q γ ρ (h', l) := by
  rw [E_swap q γ ρ (h, l), E_swap q γ ρ (h', l)]
  exact lstep (by linarith) (by linarith) hγ0 hγ1 hρ0 hρ1 hl h1 hhh (by linarith) hh0

lemma hstep_strict {q γ ρ : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hγh : 1 / 2 < γ) (hγ1 : γ < 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {h h' l : ℝ} (h1 : h ≤ 1) (hl : l ≤ 1)
    (hhh : h' < h) (hsum : 1 ≤ h' + l) (hh0 : 0 ≤ h') :
    expPostVar q γ ρ (h, l) < expPostVar q γ ρ (h', l) := by
  rw [E_swap q γ ρ (h, l), E_swap q γ ρ (h', l)]
  exact lstep_strict (by linarith) (by linarith) hγh hγ1 hρ0 hρ1 hl h1 hhh (by linarith) hh0

/-- Coordinatewise smaller strategies (in the region `σʰ + σˡ ≥ 1`) are garblings. -/
lemma E_mono2 {q γ ρ : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {σ σ' : ℝ × ℝ} (h1 : σ.1 ≤ 1) (l1 : σ.2 ≤ 1)
    (h0' : 0 ≤ σ'.1) (l0' : 0 ≤ σ'.2) (hsum : 1 ≤ σ'.1 + σ'.2)
    (hh : σ'.1 ≤ σ.1) (hl : σ'.2 ≤ σ.2) :
    expPostVar q γ ρ σ ≤ expPostVar q γ ρ σ' := by
  obtain ⟨h, l⟩ := σ
  obtain ⟨h', l'⟩ := σ'
  dsimp only at *
  calc expPostVar q γ ρ (h, l) ≤ expPostVar q γ ρ (h, l') :=
        lstep hq0 hq1 hγ0 hγ1 hρ0 hρ1 h1 l1 hl (by linarith) l0'
    _ ≤ expPostVar q γ ρ (h', l') :=
        hstep hq0 hq1 hγ0 hγ1 hρ0 hρ1 h1 (by linarith) hh hsum h0'

lemma E_mono2_strict {q γ ρ : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hγh : 1 / 2 < γ) (hγ1 : γ < 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {σ σ' : ℝ × ℝ} (h1 : σ.1 ≤ 1) (l1 : σ.2 ≤ 1)
    (h0' : 0 ≤ σ'.1) (l0' : 0 ≤ σ'.2) (hsum : 1 ≤ σ'.1 + σ'.2)
    (hh : σ'.1 ≤ σ.1) (hl : σ'.2 ≤ σ.2) (hne : σ' ≠ σ) :
    expPostVar q γ ρ σ < expPostVar q γ ρ σ' := by
  obtain ⟨h, l⟩ := σ
  obtain ⟨h', l'⟩ := σ'
  dsimp only at *
  have hγ0 : 0 ≤ γ := by linarith
  rcases hl.lt_or_eq with hl' | hl'
  · calc expPostVar q γ ρ (h, l) < expPostVar q γ ρ (h, l') :=
          lstep_strict hq0 hq1 hγh hγ1 hρ0 hρ1 h1 l1 hl' (by linarith) l0'
      _ ≤ expPostVar q γ ρ (h', l') :=
          hstep hq0.le hq1.le hγ0 hγ1.le hρ0 hρ1 h1 (by linarith) hh hsum h0'
  · subst hl'
    have hh' : h' < h := lt_of_le_of_ne hh (fun e => hne (by rw [e]))
    exact hstep_strict hq0 hq1 hγh hγ1 hρ0 hρ1 h1 l1 hh' hsum h0'

lemma J10 (γ ρ : ℝ) (ω mi mj : Bool) :
    fcastJoint γ ρ (1, 0) ω mi mj = if mi = true ∧ mj = true then 1 else 0 := by
  cases ω <;> cases mi <;> cases mj <;>
    simp [fcastJoint, Fintype.sum_bool, sigProb, sigMarg, fprob] <;> ring

lemma E_10 (q γ ρ : ℝ) : expPostVar q γ ρ (1, 0) = q * (1 - q) := by
  unfold expPostVar
  simp [J10, Fintype.sum_bool]

lemma sigProb_sum (γ ρ : ℝ) (ω : Bool) : ∑ s : Bool × Bool, sigProb γ ρ ω s.1 s.2 = 1 := by
  cases ω <;> simp [Fintype.sum_prod_type, Fintype.sum_bool, sigProb, sigMarg] <;> ring

lemma E_le {q γ ρ : ℝ} {σ : ℝ × ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (h0 : 0 ≤ σ.1) (h1 : σ.1 ≤ 1) (l0 : 0 ≤ σ.2) (l1 : σ.2 ≤ 1) :
    expPostVar q γ ρ σ ≤ q * (1 - q) := by
  rw [E_eq]
  have h := G_sum Finset.univ
    (fun m => ∑ s : Bool × Bool, Kf σ s m * (q * sigProb γ ρ true s.1 s.2))
    (fun m => ∑ s : Bool × Bool, Kf σ s m * ((1 - q) * sigProb γ ρ false s.1 s.2))
    (fun m => Finset.sum_nonneg fun s _ => mul_nonneg (Kf_nonneg h0 h1 l0 l1 s m)
      (mul_nonneg hq0 (sigProb_nonneg hγ0 hγ1 hρ0 hρ1 _ _ _)))
    (fun m => Finset.sum_nonneg fun s _ => mul_nonneg (Kf_nonneg h0 h1 l0 l1 s m)
      (mul_nonneg (sub_nonneg.2 hq1) (sigProb_nonneg hγ0 hγ1 hρ0 hρ1 _ _ _)))
  have hx : ∀ c : ℝ, ∀ ω : Bool,
      ∑ m : Bool × Bool, ∑ s : Bool × Bool, Kf σ s m * (c * sigProb γ ρ ω s.1 s.2) = c := by
    intro c ω
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, Kf_sum, one_mul]
    rw [← Finset.mul_sum, sigProb_sum, mul_one]
  rw [hx, hx] at h
  have hG : G q (1 - q) = q * (1 - q) := by
    unfold G; rw [show q + (1 - q) = 1 by ring, div_one]
  linarith

lemma E11_pos {q γ ρ : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) : 0 < expPostVar q γ ρ (1, 1) := by
  rw [E_eq]
  simp only [XJ]
  have hc : 0 ≤ ρ * γ * (1 - γ) := mul_nonneg (mul_nonneg hρ0 hγ0.le) (by linarith)
  have hα : 0 < γ ^ 2 + ρ * γ * (1 - γ) := by have := pow_pos hγ0 2; linarith
  have hβ : 0 < (1 - γ) ^ 2 + ρ * γ * (1 - γ) := by
    have := pow_pos (by linarith : (0:ℝ) < 1 - γ) 2; linarith
  have hJn : ∀ ω (m : Bool × Bool), 0 ≤ fcastJoint γ ρ (1, 1) ω m.1 m.2 := by
    intro ω m
    have := Finset.sum_nonneg fun (s : Bool × Bool) (_ : s ∈ Finset.univ) =>
      mul_nonneg (Kf_nonneg (σ := (1, 1)) zero_le_one le_rfl zero_le_one le_rfl s m)
        (mul_nonneg zero_le_one (sigProb_nonneg hγ0.le hγ1.le hρ0 hρ1 ω s.1 s.2))
    rw [XJ, one_mul] at this
    exact this
  have hnn : ∀ m : Bool × Bool,
      0 ≤ G (q * fcastJoint γ ρ (1, 1) true m.1 m.2) ((1 - q) * fcastJoint γ ρ (1, 1) false m.1 m.2) :=
    fun m => G_nonneg (mul_nonneg hq0.le (hJn _ _)) (mul_nonneg (by linarith) (hJn _ _))
  have hsingle := Finset.single_le_sum (fun m _ => hnn m) (Finset.mem_univ (true, true))
  have hpos : 0 < G (q * fcastJoint γ ρ (1, 1) true true true)
      ((1 - q) * fcastJoint γ ρ (1, 1) false true true) := by
    rw [J_TTT, J_FTT]
    have a1 : 0 < q * ((γ ^ 2 + ρ * γ * (1 - γ)) * 1 ^ 2
        + 2 * (γ * (1 - γ) - ρ * γ * (1 - γ)) * 1 * (1 - 1)
        + ((1 - γ) ^ 2 + ρ * γ * (1 - γ)) * (1 - 1) ^ 2) := mul_pos hq0 (by nlinarith)
    have a2 : 0 < (1 - q) * (((1 - γ) ^ 2 + ρ * γ * (1 - γ)) * 1 ^ 2
        + 2 * (γ * (1 - γ) - ρ * γ * (1 - γ)) * 1 * (1 - 1)
        + (γ ^ 2 + ρ * γ * (1 - γ)) * (1 - 1) ^ 2) := mul_pos (by linarith) (by nlinarith)
    exact div_pos (mul_pos a1 a2) (add_pos a1 a2)
  exact lt_of_lt_of_le hpos hsingle

/-! ### The pure-algebra core of the rank game (from 61ae79da) -/

lemma core_exists {cl al be ch ah : ℝ} (hal : 0 < al) (hah : 0 < ah) (hbe : 0 ≤ be)
    (hcl : 0 < cl) (hch : 0 < ch) (h11 : cl + be < al) (hdet : be ^ 2 < al * ah)
    (hS : al * ah - be ^ 2 ≤ (al + be) * ch + (ah + be) * cl) :
    ∃ hs ls : ℝ, 0 < hs ∧ hs ≤ 1 ∧ 0 < ls ∧ ls < 1 ∧ 1 ≤ hs + ls ∧ cl - al * ls + be * hs = 0 ∧
      ((hs = 1 ∧ 0 ≤ ch - ah * hs + be * ls) ∨ (hs < 1 ∧ ch - ah * hs + be * ls = 0)) := by
  have hal' : al ≠ 0 := hal.ne'
  by_cases hA : 0 ≤ ch - ah * 1 + be * ((cl + be) / al)
  · have hx0 : 0 < (cl + be) / al := div_pos (by linarith) hal
    refine ⟨1, (cl + be) / al, one_pos, le_refl _, hx0, (div_lt_one hal).2 h11, by linarith,
      ?_, Or.inl ⟨rfl, hA⟩⟩
    field_simp
    ring
  · push_neg at hA
    have hd : 0 < al * ah - be ^ 2 := by linarith
    have hdne : al * ah - be ^ 2 ≠ 0 := hd.ne'
    have hdne' : ah * al - be ^ 2 ≠ 0 := by
      have : ah * al - be ^ 2 = al * ah - be ^ 2 := by ring
      rw [this]; exact hdne
    have e : al * (ch - ah * 1 + be * ((cl + be) / al))
        = al * ch - al * ah + be * cl + be ^ 2 := by
      field_simp
      ring
    have hA' := mul_neg_of_pos_of_neg hal hA
    rw [e] at hA'
    have hs0 : 0 < (al * ch + be * cl) / (al * ah - be ^ 2) :=
      div_pos (by nlinarith [mul_pos hal hch, mul_nonneg hbe hcl.le]) hd
    have ls0 : 0 < (ah * cl + be * ch) / (al * ah - be ^ 2) :=
      div_pos (by nlinarith [mul_pos hah hcl, mul_nonneg hbe hch.le]) hd
    have hs1 : (al * ch + be * cl) / (al * ah - be ^ 2) < 1 := by
      rw [div_lt_one hd]; linarith
    have eqL : cl - al * ((ah * cl + be * ch) / (al * ah - be ^ 2))
        + be * ((al * ch + be * cl) / (al * ah - be ^ 2)) = 0 := by
      field_simp
      ring
    have eqH : ch - ah * ((al * ch + be * cl) / (al * ah - be ^ 2))
        + be * ((ah * cl + be * ch) / (al * ah - be ^ 2)) = 0 := by
      field_simp
      ring
    have ls1 : (ah * cl + be * ch) / (al * ah - be ^ 2) < 1 := by
      have := mul_le_mul_of_nonneg_left hs1.le hbe
      nlinarith
    have hsum : 1 ≤ (al * ch + be * cl) / (al * ah - be ^ 2)
        + (ah * cl + be * ch) / (al * ah - be ^ 2) := by
      rw [← add_div, le_div_iff₀ hd]
      linarith
    exact ⟨_, _, hs0, hs1.le, ls0, ls1, hsum, eqL, Or.inr ⟨hs1, eqH⟩⟩

lemma core_dom {cl al be ch ah hs ls : ℝ} (hal : 0 < al) (hah : 0 < ah) (hbe : 0 ≤ be)
    (hdet : be ^ 2 < al * ah) (hL0 : cl - al * ls + be * hs = 0)
    (hcase : (hs = 1 ∧ 0 ≤ ch - ah * hs + be * ls) ∨ (hs < 1 ∧ ch - ah * hs + be * ls = 0))
    (hs0 : 0 < hs) (ls0 : 0 < ls) {h l : ℝ} (hh1 : h ≤ 1)
    (hL : 0 < l → 0 ≤ cl - al * l + be * h) (hH : 0 < h → 0 ≤ ch - ah * h + be * l) :
    h ≤ hs ∧ l ≤ ls := by
  have key : ¬ ls < l := by
    intro hl
    have h1 := hL (by linarith)
    have hX : al * (l - ls) ≤ be * (h - hs) := by linarith
    have hXpos : 0 < al * (l - ls) := mul_pos hal (by linarith)
    have hhgt : hs < h := by
      by_contra hc
      push_neg at hc
      have : be * (h - hs) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hbe (by linarith)
      linarith
    rcases hcase with ⟨h1', _⟩ | ⟨_, hH0⟩
    · linarith
    · have h2 := hH (by linarith)
      have hY : ah * (h - hs) ≤ be * (l - ls) := by linarith
      have e1 := mul_le_mul_of_nonneg_left hX hah.le
      have e2 := mul_le_mul_of_nonneg_left hY hbe
      nlinarith [mul_pos (sub_pos.2 hdet) (sub_pos.2 hl)]
  refine ⟨?_, not_lt.1 key⟩
  by_contra hc
  push_neg at hc
  rcases hcase with ⟨h1', _⟩ | ⟨_, hH0⟩
  · linarith
  · have h2 := hH (by linarith)
    have hY : ah * (h - hs) ≤ be * (l - ls) := by linarith
    have hYpos : 0 < ah * (h - hs) := mul_pos hah (by linarith)
    apply key
    by_contra hc2
    push_neg at hc2
    have : be * (l - ls) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hbe (by linarith)
    linarith

/-! ### Most informative equilibria of the normalized games -/

lemma MI_unique {E : ℝ × ℝ → Prop} {σ τ : ℝ × ℝ} (hσ : IsMostInformative E σ)
    (hτ : IsMostInformative E τ) : σ = τ :=
  Prod.ext (le_antisymm (hτ.2 σ hσ.1).1 (hσ.2 τ hτ.1).1)
    (le_antisymm (hτ.2 σ hσ.1).2 (hσ.2 τ hτ.1).2)

lemma MI_swap (k q γ c : ℝ) (e : ℝ × ℝ) :
    IsMostInformative (CE k q γ c) e ↔ IsMostInformative (CE k (1 - q) γ c) (e.2, e.1) := by
  unfold IsMostInformative
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(CE_swap e).1 h1, fun e' he' => ?_⟩
    have := h2 (e'.2, e'.1) ((CE_swap (e'.2, e'.1)).2 he')
    exact ⟨this.2, this.1⟩
  · rintro ⟨h1, h2⟩
    refine ⟨(CE_swap e).2 h1, fun e' he' => ?_⟩
    have := h2 (e'.2, e'.1) ((CE_swap e').1 he')
    exact ⟨this.2, this.1⟩

lemma nL11 (φ q γ ρ : ℝ) (hD : 0 < (1 - γ) * φ + γ) :
    nL (φ - 1) q γ (ρ * γ * (1 - γ)) 1 1 = ((1 - γ) * φ + γ) * (qminCheck γ ρ φ - q) := by
  have hq : qminCheck γ ρ φ * ((1 - γ) * φ + γ)
      = φ * (γ * (1 - γ) - ρ * γ * (1 - γ)) + γ ^ 2 + ρ * γ * (1 - γ) := by
    unfold qminCheck
    rw [sub_mul, mul_assoc, div_mul_cancel₀ _ hD.ne']
    ring
  unfold nL AL Bc
  linear_combination (-1 : ℝ) * hq

lemma nH11 (φ q γ ρ : ℝ) (hD : 0 < (1 - γ) * φ + γ) :
    nH (φ - 1) q γ (ρ * γ * (1 - γ)) 1 1 = ((1 - γ) * φ + γ) * (qminCheck γ ρ φ - (1 - q)) := by
  rw [nH_swap, nL11 φ (1 - q) γ ρ hD]

lemma nL_mono {k k' q γ c h l : ℝ} (hk : 0 < k) (hkk : k ≤ k') (hq : q ≤ γ)
    (h' : 0 ≤ nL k' q γ c h l) : 0 ≤ nL k q γ c h l := by
  unfold nL at *
  set F := γ * (γ - q) + c - AL q γ c * l + Bc γ c * h
  rcases le_or_gt 0 F with hF | hF
  · linarith [mul_nonneg hk.le hF]
  · linarith [mul_le_mul_of_nonpos_right hkk hF.le]

lemma nH_mono {k k' q γ c h l : ℝ} (hk : 0 < k) (hkk : k ≤ k') (hq : 1 - q ≤ γ)
    (h' : 0 ≤ nH k' q γ c h l) : 0 ≤ nH k q γ c h l := by
  rw [nH_swap] at *
  exact nL_mono hk hkk (by linarith) h'

/-- The rank game's most informative equilibrium for `k = φ - 1 > 0`, `1/2 ≤ q ≤ γ`: it dominates
every strategy satisfying the "no profitable deviation to the truthful forecast" half of the
conditions. -/
lemma comp_MI {k q γ ρ : ℝ} (hk : 0 < k) (hq : 1 / 2 ≤ q) (hqγ : q ≤ γ) (hγh : 1 / 2 < γ)
    (hγ1 : γ < 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ∃ e : ℝ × ℝ, CE k q γ (ρ * γ * (1 - γ)) e ∧
      (∀ σ : ℝ × ℝ, σ.1 ≤ 1 → σ.2 ≤ 1 → (0 < σ.2 → 0 ≤ nL k q γ (ρ * γ * (1 - γ)) σ.1 σ.2) →
        (0 < σ.1 → 0 ≤ nH k q γ (ρ * γ * (1 - γ)) σ.1 σ.2) → σ.1 ≤ e.1 ∧ σ.2 ≤ e.2) ∧
      (nL k q γ (ρ * γ * (1 - γ)) 1 1 < 0 →
        0 < e.1 ∧ 0 < e.2 ∧ e.2 < 1 ∧ nL k q γ (ρ * γ * (1 - γ)) e.1 e.2 = 0) := by
  set c := ρ * γ * (1 - γ) with hc
  have hγ0 : 0 < γ := by linarith
  have h1γ : 0 < 1 - γ := by linarith
  have hq1 : q < 1 := by linarith
  have h1q : 0 < 1 - q := by linarith
  have hq0 : 0 < q := by linarith
  have hcn : 0 ≤ c := mul_nonneg (mul_nonneg hρ0 hγ0.le) h1γ.le
  have hB : 0 ≤ Bc γ c := by
    unfold Bc; rw [hc]
    linarith [mul_nonneg (sub_nonneg.2 hρ1) (mul_nonneg hγ0.le h1γ.le)]
  have hP : 0 < γ ^ 2 + c := by have := pow_pos hγ0 2; linarith
  have hQ : 0 < (1 - γ) ^ 2 + c := by have := pow_pos h1γ 2; linarith
  have hAL : 0 < AL q γ c := by unfold AL; linarith [mul_pos h1q hP, mul_pos hq0 hQ]
  have hAH : 0 < AH q γ c := by unfold AH; linarith [mul_pos hq0 hP, mul_pos h1q hQ]
  have eL : ∀ h l, nL k q γ c h l =
      (k * (γ * (γ - q) + c) + (γ - q)) - k * AL q γ c * l + k * Bc γ c * h := by
    intro h l; unfold nL; ring
  have eH : ∀ h l, nH k q γ c h l =
      (k * (γ * (γ - (1 - q)) + c) + (γ - (1 - q))) - k * AH q γ c * h + k * Bc γ c * l := by
    intro h l; unfold nH; ring
  have hHL : nL k q γ c 1 1 ≤ nH k q γ c 1 1 := by
    rw [eL, eH]; unfold AL AH
    linarith [mul_nonneg hk.le (mul_nonneg (by linarith : (0:ℝ) ≤ 2 * q - 1) h1γ.le)]
  by_cases h11 : 0 ≤ nL k q γ c 1 1
  · refine ⟨(1, 1), ⟨zero_le_one, le_rfl, zero_le_one, le_rfl, by norm_num,
      fun h => absurd h (lt_irrefl _), fun _ => le_trans h11 hHL,
      fun h => absurd h (lt_irrefl _), fun _ => h11⟩, fun σ h1 h2 _ _ => ⟨h1, h2⟩,
      fun h => absurd h (not_lt.2 h11)⟩
  push_neg at h11
  have hal : 0 < k * AL q γ c := mul_pos hk hAL
  have hah : 0 < k * AH q γ c := mul_pos hk hAH
  have hbe : 0 ≤ k * Bc γ c := mul_nonneg hk.le hB
  have hcl : 0 < k * (γ * (γ - q) + c) + (γ - q) := by
    rcases hqγ.lt_or_eq with hlt | heq
    · have : 0 ≤ k * (γ * (γ - q) + c) :=
        mul_nonneg hk.le (add_nonneg (mul_nonneg hγ0.le (by linarith)) hcn)
      linarith
    · rw [eL] at h11
      have e : (k * (γ * (γ - q) + c) + (γ - q)) - k * AL q γ c * 1 + k * Bc γ c * 1
          = (γ - q) * (k * (1 - γ) + 1) - k * c := by unfold AL Bc; ring
      rw [e, heq, sub_self, zero_mul, zero_sub] at h11
      have : 0 < k * c := by linarith
      rw [heq, sub_self, mul_zero, zero_add, add_zero]
      exact this
  have hch : 0 < k * (γ * (γ - (1 - q)) + c) + (γ - (1 - q)) := by
    have : 0 ≤ k * (γ * (γ - (1 - q)) + c) :=
      mul_nonneg hk.le (add_nonneg (mul_nonneg hγ0.le (by linarith)) hcn)
    linarith
  have h11' : (k * (γ * (γ - q) + c) + (γ - q)) + k * Bc γ c < k * AL q γ c := by
    rw [eL] at h11; linarith
  have hdet : (k * Bc γ c) ^ 2 < k * AL q γ c * (k * AH q γ c) := by
    have e : k * AL q γ c * (k * AH q γ c) - (k * Bc γ c) ^ 2
        = k ^ 2 * (c + q * (1 - q) * (2 * γ - 1) ^ 2) := by unfold AL AH Bc; ring
    have : 0 < k ^ 2 * (c + q * (1 - q) * (2 * γ - 1) ^ 2) :=
      mul_pos (pow_pos hk 2) (add_pos_of_nonneg_of_pos hcn
        (mul_pos (mul_pos hq0 h1q) (pow_pos (by linarith) 2)))
    linarith
  have hS : k * AL q γ c * (k * AH q γ c) - (k * Bc γ c) ^ 2 ≤
      (k * AL q γ c + k * Bc γ c) * (k * (γ * (γ - (1 - q)) + c) + (γ - (1 - q))) +
      (k * AH q γ c + k * Bc γ c) * (k * (γ * (γ - q) + c) + (γ - q)) := by
    have e : (k * AL q γ c + k * Bc γ c) * (k * (γ * (γ - (1 - q)) + c) + (γ - (1 - q))) +
        (k * AH q γ c + k * Bc γ c) * (k * (γ * (γ - q) + c) + (γ - q)) -
        (k * AL q γ c * (k * AH q γ c) - (k * Bc γ c) ^ 2)
        = k * (k + 2) * q * (1 - q) * (2 * γ - 1) := by unfold AL AH Bc; ring
    have : 0 ≤ k * (k + 2) * q * (1 - q) * (2 * γ - 1) := by
      have : 0 ≤ 2 * γ - 1 := by linarith
      have : 0 ≤ k + 2 := by linarith
      positivity
    linarith
  obtain ⟨hs, ls, hs0, hs1, ls0, ls1, hsum, hLeq, hcase⟩ :=
    core_exists hal hah hbe hcl hch h11' hdet hS
  have nLs : nL k q γ c hs ls = 0 := by rw [eL]; linarith
  refine ⟨(hs, ls), ⟨hs0.le, hs1, ls0.le, ls1.le, by dsimp only; linarith, ?_, ?_,
    fun _ => nLs.le, fun _ => nLs.ge⟩, ?_, fun _ => ⟨hs0, ls0, ls1, nLs⟩⟩
  · intro h
    rcases hcase with ⟨e1, _⟩ | ⟨_, e2⟩
    · exact absurd e1 (ne_of_lt h)
    · dsimp only; rw [eH]; linarith
  · intro _
    rcases hcase with ⟨_, e2⟩ | ⟨_, e2⟩ <;> (dsimp only; rw [eH]; linarith)
  · intro σ h1 _ hL hH
    exact core_dom hal hah hbe hdet hLeq hcase hs0 ls0 h1
      (fun hl => by have := hL hl; rw [eL] at this; linarith)
      (fun hh => by have := hH hh; rw [eH] at this; linarith)

/-! ### The conclusion in normalized form, its symmetry, and the case `q ≥ 1/2` -/

def Concl (γ ρ φ q : ℝ) : Prop :=
  ∃ eB : ℝ × ℝ, IsMostInformative (CE 0 q γ (ρ * γ * (1 - γ))) eB ∧
    ((∃ e : ℝ × ℝ, IsMostInformative (CE (φ - 1) q γ (ρ * γ * (1 - γ))) e ∧
        informativeness q γ ρ e < informativeness q γ ρ eB) ↔
      (1 < φ ∧ 0 < ρ ∧ 1 - γ ≤ q ∧ q ≤ γ ∧ qminCheck γ ρ φ < max q (1 - q))) ∧
    (∀ φ' : ℝ, 1 < φ → φ < φ' → 1 - γ ≤ q → q ≤ γ →
      ∃ e e' : ℝ × ℝ, IsMostInformative (CE (φ - 1) q γ (ρ * γ * (1 - γ))) e ∧
        IsMostInformative (CE (φ' - 1) q γ (ρ * γ * (1 - γ))) e' ∧
        informativeness q γ ρ eB - informativeness q γ ρ e ≤
          informativeness q γ ρ eB - informativeness q γ ρ e' ∧
        (qminCheck γ ρ φ' < max q (1 - q) → max q (1 - q) < γ →
          informativeness q γ ρ eB - informativeness q γ ρ e <
            informativeness q γ ρ eB - informativeness q γ ρ e'))

lemma Concl_swap (γ ρ φ q : ℝ) (h : Concl γ ρ φ (1 - q)) : Concl γ ρ φ q := by
  obtain ⟨eB, hB, hiff, h2⟩ := h
  have hmax : max (1 - q) (1 - (1 - q)) = max q (1 - q) := by rw [sub_sub_cancel, max_comm]
  refine ⟨(eB.2, eB.1), (MI_swap _ _ _ _ _).2 hB, ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨e, he, hlt⟩
    rw [Pi_swap q γ ρ e, Pi_swap q γ ρ (eB.2, eB.1)] at hlt
    have := hiff.1 ⟨(e.2, e.1), (MI_swap _ _ _ _ e).1 he, hlt⟩
    obtain ⟨a, b, c1, c2, d⟩ := this
    rw [hmax] at d
    exact ⟨a, b, by linarith, by linarith, d⟩
  · rintro ⟨a, b, c1, c2, d⟩
    rw [← hmax] at d
    obtain ⟨e, he, hlt⟩ := hiff.2 ⟨a, b, by linarith, by linarith, d⟩
    refine ⟨(e.2, e.1), (MI_swap _ _ _ _ _).2 he, ?_⟩
    rw [Pi_swap q γ ρ (e.2, e.1), Pi_swap q γ ρ (eB.2, eB.1)]
    exact hlt
  · intro φ' h1 h2' h3 h4
    obtain ⟨e, e', he, he', hle, hlt⟩ := h2 φ' h1 h2' (by linarith) (by linarith)
    refine ⟨(e.2, e.1), (e'.2, e'.1), (MI_swap _ _ _ _ _).2 he, (MI_swap _ _ _ _ _).2 he', ?_, ?_⟩
    · rw [Pi_swap q γ ρ (e.2, e.1), Pi_swap q γ ρ (e'.2, e'.1), Pi_swap q γ ρ (eB.2, eB.1)]
      exact hle
    · intro a b
      rw [Pi_swap q γ ρ (e.2, e.1), Pi_swap q γ ρ (e'.2, e'.1), Pi_swap q γ ρ (eB.2, eB.1)]
      rw [← hmax] at a b
      exact hlt a b

lemma core (γ ρ φ q : ℝ) (hγ1 : 1 / 2 < γ) (hγ2 : γ < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hq : 1 / 2 ≤ q) (hq1 : q < 1) (hφ0 : 0 < φ) (hφ : φ ≠ 1) : Concl γ ρ φ q := by
  set c := ρ * γ * (1 - γ) with hc
  have hq0 : 0 < q := by linarith
  have hγ0 : 0 < γ := by linarith
  have hcn : 0 ≤ c := mul_nonneg (mul_nonneg hρ0 hγ0.le) (by linarith)
  have hmax : max q (1 - q) = q := max_eq_left (by linarith)
  have hDf : ∀ ψ : ℝ, 0 < ψ → 0 < (1 - γ) * ψ + γ := fun ψ hψ => by
    have : 0 ≤ (1 - γ) * ψ := mul_nonneg (by linarith) hψ.le
    linarith
  have hD := hDf φ hφ0
  have hqq : 0 < q * (1 - q) := mul_pos hq0 (by linarith)
  have Epos : ∀ σ : ℝ × ℝ, 0 ≤ σ.1 → σ.1 ≤ 1 → 0 ≤ σ.2 → σ.2 ≤ 1 → 1 - σ.2 ≤ σ.1 →
      0 < expPostVar q γ ρ σ := fun σ a b d e f =>
    lt_of_lt_of_le (E11_pos hq0 hq1 hγ0 hγ2 hρ0 hρ1)
      (E_mono2 hq0.le hq1.le hγ0.le hγ2.le hρ0 hρ1 (σ := (1, 1)) le_rfl le_rfl a d
        (by linarith) b e)
  have Pi_le : ∀ σ σ' : ℝ × ℝ, expPostVar q γ ρ σ ≤ expPostVar q γ ρ σ' →
      0 < expPostVar q γ ρ σ → informativeness q γ ρ σ' ≤ informativeness q γ ρ σ := by
    intro σ σ' h h0
    unfold informativeness
    have := div_le_div_of_nonneg_left hqq.le h0 h
    linarith
  have Pi_lt : ∀ σ σ' : ℝ × ℝ, expPostVar q γ ρ σ < expPostVar q γ ρ σ' →
      0 < expPostVar q γ ρ σ → informativeness q γ ρ σ' < informativeness q γ ρ σ := by
    intro σ σ' h h0
    unfold informativeness
    have := div_lt_div_of_pos_left hqq h0 h
    linarith
  have toMI : ∀ k : ℝ, ∀ e : ℝ × ℝ, CE k q γ c e →
      (∀ σ : ℝ × ℝ, σ.1 ≤ 1 → σ.2 ≤ 1 → (0 < σ.2 → 0 ≤ nL k q γ c σ.1 σ.2) →
        (0 < σ.1 → 0 ≤ nH k q γ c σ.1 σ.2) → σ.1 ≤ e.1 ∧ σ.2 ≤ e.2) →
      IsMostInformative (CE k q γ c) e := fun k e he hdom =>
    ⟨he, fun σ hσ => hdom σ hσ.2.1 hσ.2.2.2.1 hσ.2.2.2.2.2.2.2.2 hσ.2.2.2.2.2.2.1⟩
  by_cases hqγ : q ≤ γ
  · have hB : IsMostInformative (CE 0 q γ c) (1, 1) := by
      refine ⟨⟨zero_le_one, le_rfl, zero_le_one, le_rfl, by norm_num,
        fun h => absurd h (lt_irrefl _), fun _ => ?_, fun h => absurd h (lt_irrefl _),
        fun _ => ?_⟩, fun e he => ⟨he.2.1, he.2.2.2.1⟩⟩
      · unfold nH; linarith
      · unfold nL; linarith
    refine ⟨(1, 1), hB, ⟨?_, ?_⟩, ?_⟩
    · rintro ⟨e, he, hlt⟩
      have hn : nL (φ - 1) q γ c 1 1 < 0 := by
        by_contra hn
        push_neg at hn
        have hH : 0 ≤ nH (φ - 1) q γ c 1 1 := by
          rw [hc, nH11 φ q γ ρ hD]
          rw [hc, nL11 φ q γ ρ hD] at hn
          linarith [mul_nonneg hD.le (by linarith : (0:ℝ) ≤ 2 * q - 1)]
        have h11 : IsMostInformative (CE (φ - 1) q γ c) (1, 1) :=
          ⟨⟨zero_le_one, le_rfl, zero_le_one, le_rfl, by norm_num,
            fun h => absurd h (lt_irrefl _), fun _ => hH, fun h => absurd h (lt_irrefl _),
            fun _ => hn⟩, fun e he => ⟨he.2.1, he.2.2.2.1⟩⟩
        rw [MI_unique he h11] at hlt
        exact lt_irrefl _ hlt
      rw [hc, nL11 φ q γ ρ hD] at hn
      have hqm : qminCheck γ ρ φ < q := by
        by_contra h
        push_neg at h
        have : 0 ≤ ((1 - γ) * φ + γ) * (qminCheck γ ρ φ - q) :=
          mul_nonneg hD.le (by linarith)
        linarith
      refine ⟨?_, ?_, by linarith, hqγ, by rw [hmax]; exact hqm⟩
      · by_contra hφ1
        push_neg at hφ1
        have hlt1 : φ < 1 := lt_of_le_of_ne hφ1 hφ
        have : γ ≤ qminCheck γ ρ φ := by
          unfold qminCheck
          have h1 : (φ - 1) / ((1 - γ) * φ + γ) < 0 := div_neg_of_neg_of_pos (by linarith) hD
          have h2 : ρ * γ * (1 - γ) * ((φ - 1) / ((1 - γ) * φ + γ)) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos hcn h1.le
          linarith
        linarith
      · by_contra hρ'
        push_neg at hρ'
        have h0 : ρ = 0 := le_antisymm hρ' hρ0
        have : qminCheck γ ρ φ = γ := by unfold qminCheck; rw [h0]; ring
        linarith
    · rintro ⟨hφ1, hρp, -, -, hqm⟩
      rw [hmax] at hqm
      have hn : nL (φ - 1) q γ c 1 1 < 0 := by
        rw [hc, nL11 φ q γ ρ hD]; exact mul_neg_of_pos_of_neg hD (by linarith)
      obtain ⟨e, he, hdom, hint⟩ := comp_MI (k := φ - 1) (by linarith) hq hqγ hγ1 hγ2 hρ0 hρ1
      obtain ⟨e1, e2, e3, -⟩ := hint hn
      refine ⟨e, toMI _ e he hdom, ?_⟩
      apply Pi_lt (1, 1) e _ (E11_pos hq0 hq1 hγ0 hγ2 hρ0 hρ1)
      refine E_mono2_strict hq0 hq1 hγ1 hγ2 hρ0 hρ1 (σ := (1, 1)) le_rfl le_rfl he.1 he.2.2.1
        (by linarith [he.2.2.2.2.1]) he.2.1 he.2.2.2.1 ?_
      intro h
      rw [h] at e3
      exact lt_irrefl _ e3
    · intro φ' hφ1 hφφ' _ _
      obtain ⟨e, he, hdom, hint⟩ := comp_MI (k := φ - 1) (by linarith) hq hqγ hγ1 hγ2 hρ0 hρ1
      obtain ⟨e', he', hdom', hint'⟩ := comp_MI (k := φ' - 1) (by linarith) hq hqγ hγ1 hγ2 hρ0 hρ1
      have hle : e'.1 ≤ e.1 ∧ e'.2 ≤ e.2 := hdom e' he'.2.1 he'.2.2.2.1
        (fun h => nL_mono (by linarith) (by linarith) hqγ (he'.2.2.2.2.2.2.2.2 h))
        (fun h => nH_mono (by linarith) (by linarith) (by linarith) (he'.2.2.2.2.2.2.1 h))
      have hEle : expPostVar q γ ρ e ≤ expPostVar q γ ρ e' :=
        E_mono2 hq0.le hq1.le hγ0.le hγ2.le hρ0 hρ1 he.2.1 he.2.2.2.1 he'.1 he'.2.2.1
          (by linarith [he'.2.2.2.2.1]) hle.1 hle.2
      have hEpos := Epos e he.1 he.2.1 he.2.2.1 he.2.2.2.1 he.2.2.2.2.1
      refine ⟨e, e', toMI _ e he hdom, toMI _ e' he' hdom', by linarith [Pi_le e e' hEle hEpos], ?_⟩
      intro hqm' hlt
      rw [hmax] at hqm' hlt
      have hn' : nL (φ' - 1) q γ c 1 1 < 0 := by
        rw [hc, nL11 φ' q γ ρ (hDf φ' (by linarith))]
        exact mul_neg_of_pos_of_neg (hDf φ' (by linarith)) (by linarith)
      obtain ⟨f1, f2, f3, f4⟩ := hint' hn'
      have hne : e' ≠ e := by
        intro heq
        rw [heq] at f2 f3 f4
        have hL0 : nL (φ - 1) q γ c e.1 e.2 = 0 :=
          le_antisymm (he.2.2.2.2.2.2.2.1 f3) (he.2.2.2.2.2.2.2.2 f2)
        have hdiff : nL (φ - 1) q γ c e.1 e.2 - nL (φ' - 1) q γ c e.1 e.2 =
            (φ - φ') * (γ * (γ - q) + c - AL q γ c * e.2 + Bc γ c * e.1) := by
          unfold nL; ring
        rw [hL0, f4, sub_zero] at hdiff
        have hF : γ * (γ - q) + c - AL q γ c * e.2 + Bc γ c * e.1 = 0 :=
          (mul_eq_zero.1 hdiff.symm).resolve_left (by linarith)
        unfold nL at hL0
        rw [hF] at hL0
        linarith
      have hElt : expPostVar q γ ρ e < expPostVar q γ ρ e' :=
        E_mono2_strict hq0 hq1 hγ1 hγ2 hρ0 hρ1 he.2.1 he.2.2.2.1 he'.1 he'.2.2.1
          (by linarith [he'.2.2.2.2.1]) hle.1 hle.2 hne
      linarith [Pi_lt e e' hElt hEpos]
  · push_neg at hqγ
    have hB : IsMostInformative (CE 0 q γ c) (1, 0) := by
      refine ⟨⟨zero_le_one, le_rfl, le_rfl, zero_le_one, by norm_num,
        fun h => absurd h (lt_irrefl _), fun _ => ?_, fun _ => ?_,
        fun h => absurd h (lt_irrefl _)⟩, fun e he => ⟨he.2.1, ?_⟩⟩
      · unfold nH; linarith
      · unfold nL; linarith
      · by_contra h
        push_neg at h
        have := he.2.2.2.2.2.2.2.2 h
        unfold nL at this
        linarith
    have hPiB : informativeness q γ ρ (1, 0) = 0 := by
      unfold informativeness; rw [E_10, div_self hqq.ne']; ring
    refine ⟨(1, 0), hB, ⟨?_, fun h => absurd h.2.2.2.1 (not_le.2 hqγ)⟩,
      fun φ' _ _ _ h => absurd h (not_le.2 hqγ)⟩
    rintro ⟨e, he, hlt⟩
    exfalso
    have hE := E_le hq0.le hq1.le hγ0.le hγ2.le hρ0 hρ1 he.1.1 he.1.2.1 he.1.2.2.1 he.1.2.2.2.1
    have hEp := Epos e he.1.1 he.1.2.1 he.1.2.2.1 he.1.2.2.2.1 he.1.2.2.2.2.1
    have : 0 ≤ informativeness q γ ρ e := by
      unfold informativeness
      have : 1 ≤ q * (1 - q) / expPostVar q γ ρ e := by rw [le_div_iff₀ hEp]; linarith
      linarith
    linarith

end P5R

open AnalystRanking.Revelation in
theorem solution
    (γ ρ q W w1 w0 w2 : ℝ) (hγ1 : 1 / 2 < γ) (hγ2 : γ < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hq0 : 0 < q) (hq1 : q < 1)
    (hW : 0 < W) (hw20 : w2 < w0) (hw01 : w0 < w1) (hφ : phiConvexity w1 w0 w2 ≠ 1) :
    ∃ eB : ℝ × ℝ, IsMostInformative (IsBenchEq W q γ) eB ∧
      ((∃ e : ℝ × ℝ, IsMostInformative (IsCompEq w1 w0 w2 q γ ρ) e ∧
          informativeness q γ ρ e < informativeness q γ ρ eB) ↔
        (1 < phiConvexity w1 w0 w2 ∧ 0 < ρ ∧ 1 - γ ≤ q ∧ q ≤ γ ∧
          qminCheck γ ρ (phiConvexity w1 w0 w2) < max q (1 - q))) ∧
      (∀ w1' w0' w2' : ℝ, w2' < w0' → w0' < w1' →
        1 < phiConvexity w1 w0 w2 → phiConvexity w1 w0 w2 < phiConvexity w1' w0' w2' →
        1 - γ ≤ q → q ≤ γ →
        ∃ e e' : ℝ × ℝ, IsMostInformative (IsCompEq w1 w0 w2 q γ ρ) e ∧
          IsMostInformative (IsCompEq w1' w0' w2' q γ ρ) e' ∧
          informativeness q γ ρ eB - informativeness q γ ρ e ≤
            informativeness q γ ρ eB - informativeness q γ ρ e' ∧
          (qminCheck γ ρ (phiConvexity w1' w0' w2') < max q (1 - q) → max q (1 - q) < γ →
            informativeness q γ ρ eB - informativeness q γ ρ e <
              informativeness q γ ρ eB - informativeness q γ ρ e')) := by
  have hγ0 : 0 < γ := by linarith
  have hφ0 : 0 < phiConvexity w1 w0 w2 := div_pos (by linarith) (by linarith)
  have hcomp : ∀ a b d : ℝ, d < b → IsCompEq a b d q γ ρ =
      P5R.CE (phiConvexity a b d - 1) q γ (ρ * γ * (1 - γ)) := fun a b d h =>
    funext fun σ => propext (P5R.comp_iff hq0 hq1 hγ0 hγ2 (by linarith) σ)
  have hbench : IsBenchEq W q γ = P5R.CE 0 q γ (ρ * γ * (1 - γ)) :=
    funext fun σ => propext (P5R.bench_iff _ hq0 hq1 hγ0 hγ2 hW σ)
  have hC : P5R.Concl γ ρ (phiConvexity w1 w0 w2) q := by
    rcases le_or_gt (1 / 2) q with hq | hq
    · exact P5R.core γ ρ _ q hγ1 hγ2 hρ0 hρ1 hq hq1 hφ0 hφ
    · apply P5R.Concl_swap
      exact P5R.core γ ρ _ (1 - q) hγ1 hγ2 hρ0 hρ1 (by linarith) (by linarith) hφ0 hφ
  obtain ⟨eB, hB, hiff, h2⟩ := hC
  rw [hbench, hcomp w1 w0 w2 hw20]
  refine ⟨eB, hB, hiff, ?_⟩
  intro w1' w0' w2' h20 h01 hφ1 hφφ' h1γ hqγ
  rw [hcomp w1' w0' w2' h20]
  exact h2 _ hφ1 hφφ' h1γ hqγ
