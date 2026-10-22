-- Prove2me | solution 1 for AnalystRank.Informativeness.proposition_5_B1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T22:56:52.860469+00:00
-- url     : https://prove2.me/submissions/3bc472ff-8448-411e-b3c2-7e5efa168743

import Mathlib
import Definitions.Def_AnalystRank_Informativeness_Model

set_option autoImplicit false

namespace P5B1

open AnalystRank.Informativeness Set

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

/-! ### Expected posterior variance as a sum of `G` terms -/

def Kf (σ : ℝ × ℝ) (s m : Bool × Bool) : ℝ := fcast σ s.1 m.1 * fcast σ s.2 m.2

lemma term (q γ ρ : ℝ) (σ : ℝ × ℝ) (mi mj : Bool) :
    fcastPairProb q γ ρ σ mi mj * postVar q γ ρ σ mi mj
      = G (q * fcastPairLaw γ ρ σ true mi mj) ((1 - q) * fcastPairLaw γ ρ σ false mi mj) := by
  have hP : fcastPairProb q γ ρ σ mi mj
      = q * fcastPairLaw γ ρ σ true mi mj + (1 - q) * fcastPairLaw γ ρ σ false mi mj := by
    simp [fcastPairProb, Fintype.sum_bool, prior]
  have hpt : prior q true = q := by simp [prior]
  unfold postVar postHigh G
  rw [hP, hpt]
  set A := q * fcastPairLaw γ ρ σ true mi mj
  set B := (1 - q) * fcastPairLaw γ ρ σ false mi mj
  rcases eq_or_ne (A + B) 0 with h | h
  · rw [h]; simp
  · field_simp; ring

lemma E_eq (q γ ρ : ℝ) (σ : ℝ × ℝ) :
    expPostVar q γ ρ σ = ∑ m : Bool × Bool,
      G (∑ s : Bool × Bool, Kf σ s m * (q * sigLaw γ ρ true s.1 s.2))
        (∑ s : Bool × Bool, Kf σ s m * ((1 - q) * sigLaw γ ρ false s.1 s.2)) := by
  have hL : ∀ (c : ℝ) (ω mi mj : Bool), c * fcastPairLaw γ ρ σ ω mi mj
      = ∑ s : Bool × Bool, Kf σ s (mi, mj) * (c * sigLaw γ ρ ω s.1 s.2) := by
    intro c ω mi mj
    simp only [fcastPairLaw, Kf, Fintype.sum_prod_type, Fintype.sum_bool]
    ring
  unfold expPostVar
  simp only [term, hL]
  rw [Fintype.sum_prod_type (f := fun m : Bool × Bool =>
    G (∑ s : Bool × Bool, Kf σ s m * (q * sigLaw γ ρ true s.1 s.2))
      (∑ s : Bool × Bool, Kf σ s m * ((1 - q) * sigLaw γ ρ false s.1 s.2)))]

lemma E_11 (q γ ρ : ℝ) : expPostVar q γ ρ (1, 1) =
    ∑ s : Bool × Bool, G (q * sigLaw γ ρ true s.1 s.2) ((1 - q) * sigLaw γ ρ false s.1 s.2) := by
  rw [E_eq]
  simp [Kf, fcast, Fintype.sum_prod_type, Fintype.sum_bool]

lemma chi_nonneg {γ ρ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hρ0 : 0 ≤ ρ) : 0 ≤ chi γ ρ := by
  unfold chi; exact mul_nonneg (mul_nonneg hρ0 hγ0) (sub_nonneg.2 hγ1)

lemma a_nonneg {γ ρ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hρ1 : ρ ≤ 1) :
    0 ≤ γ * (1 - γ) - chi γ ρ := by
  unfold chi
  nlinarith [mul_nonneg (sub_nonneg.2 hρ1) (mul_nonneg hγ0 (sub_nonneg.2 hγ1))]

lemma sigLaw_nonneg {γ ρ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (ω a b : Bool) : 0 ≤ sigLaw γ ρ ω a b := by
  have hc := chi_nonneg hγ0 hγ1 hρ0
  have ha := a_nonneg (ρ := ρ) hγ0 hγ1 hρ1
  unfold sigLaw
  split_ifs <;> nlinarith [sq_nonneg γ, sq_nonneg (1 - γ)]

lemma sigLaw_sum (γ ρ : ℝ) (ω : Bool) : ∑ s : Bool × Bool, sigLaw γ ρ ω s.1 s.2 = 1 := by
  cases ω <;> simp [Fintype.sum_prod_type, Fintype.sum_bool, sigLaw] <;> ring

lemma fcast_nonneg {σ : ℝ × ℝ} (h1 : σ.1 ∈ Icc (0 : ℝ) 1) (h2 : σ.2 ∈ Icc (0 : ℝ) 1)
    (s m : Bool) : 0 ≤ fcast σ s m := by
  cases s <;> cases m <;> simp [fcast] <;> linarith [h1.1, h1.2, h2.1, h2.2]

lemma Kf_nonneg {σ : ℝ × ℝ} (h1 : σ.1 ∈ Icc (0 : ℝ) 1) (h2 : σ.2 ∈ Icc (0 : ℝ) 1)
    (s m : Bool × Bool) : 0 ≤ Kf σ s m :=
  mul_nonneg (fcast_nonneg h1 h2 _ _) (fcast_nonneg h1 h2 _ _)

lemma Kf_sum (σ : ℝ × ℝ) (s : Bool × Bool) : ∑ m, Kf σ s m = 1 := by
  rcases s with ⟨a, b⟩
  cases a <;> cases b <;> simp [Kf, fcast, Fintype.sum_prod_type, Fintype.sum_bool] <;> ring

lemma E_ge {q γ ρ : ℝ} {σ : ℝ × ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (h1 : σ.1 ∈ Icc (0 : ℝ) 1) (h2 : σ.2 ∈ Icc (0 : ℝ) 1) :
    expPostVar q γ ρ (1, 1) ≤ expPostVar q γ ρ σ := by
  rw [E_11, E_eq]
  exact garble (Kf σ) _ _ (Kf_nonneg h1 h2) (Kf_sum σ)
    (fun s => mul_nonneg hq0 (sigLaw_nonneg hγ0 hγ1 hρ0 hρ1 _ _ _))
    (fun s => mul_nonneg (sub_nonneg.2 hq1) (sigLaw_nonneg hγ0 hγ1 hρ0 hρ1 _ _ _))

lemma E_gt {q γ ρ : ℝ} {σ : ℝ × ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hγh : 1 / 2 < γ)
    (hγ1 : γ < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (h1 : σ.1 ∈ Icc (0 : ℝ) 1)
    (h2 : σ.2 ∈ Icc (0 : ℝ) 1) (hh : 0 < σ.1) (hl : σ.2 < 1) :
    expPostVar q γ ρ (1, 1) < expPostVar q γ ρ σ := by
  have hγ0 : (0 : ℝ) ≤ γ := by linarith
  have hc := chi_nonneg hγ0 hγ1.le hρ0
  rw [E_11, E_eq]
  have hγp : 0 < γ := by linarith
  have hP : 0 < γ ^ 2 + chi γ ρ := by have := pow_pos hγp 2; linarith
  have h1γ : 0 < 1 - γ := by linarith
  have hQ : 0 < (1 - γ) ^ 2 + chi γ ρ := by have := pow_pos h1γ 2; linarith
  have h1q : 0 < 1 - q := by linarith
  apply garble_strict (Kf σ) _ _ (Kf_nonneg h1 h2) (Kf_sum σ)
    (fun s => mul_nonneg hq0.le (sigLaw_nonneg hγ0 hγ1.le hρ0 hρ1 _ _ _))
    (fun s => mul_nonneg (sub_nonneg.2 hq1.le) (sigLaw_nonneg hγ0 hγ1.le hρ0 hρ1 _ _ _))
    (true, true) (true, true) (false, false) (by decide)
  · show 0 < σ.1 * σ.1
    exact mul_pos hh hh
  · show 0 < (1 - σ.2) * (1 - σ.2)
    have : 0 < 1 - σ.2 := by linarith
    exact mul_pos this this
  · show 0 < q * (γ ^ 2 + chi γ ρ) + (1 - q) * ((1 - γ) ^ 2 + chi γ ρ)
    nlinarith [mul_pos hq0 hP, mul_pos h1q hQ]
  · show 0 < q * ((1 - γ) ^ 2 + chi γ ρ) + (1 - q) * (γ ^ 2 + chi γ ρ)
    nlinarith [mul_pos hq0 hQ, mul_pos h1q hP]
  · show q * (γ ^ 2 + chi γ ρ) * ((1 - q) * (γ ^ 2 + chi γ ρ))
      ≠ q * ((1 - γ) ^ 2 + chi γ ρ) * ((1 - q) * ((1 - γ) ^ 2 + chi γ ρ))
    intro h
    have h' : q * (1 - q) * ((γ ^ 2 + chi γ ρ) ^ 2 - ((1 - γ) ^ 2 + chi γ ρ) ^ 2) = 0 := by
      linear_combination h
    have hd : 0 < (γ ^ 2 + chi γ ρ) ^ 2 - ((1 - γ) ^ 2 + chi γ ρ) ^ 2 := by nlinarith
    have : 0 < q * (1 - q) * ((γ ^ 2 + chi γ ρ) ^ 2 - ((1 - γ) ^ 2 + chi γ ρ) ^ 2) :=
      mul_pos (mul_pos hq0 h1q) hd
    linarith

lemma E_le {q γ ρ : ℝ} {σ : ℝ × ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (h1 : σ.1 ∈ Icc (0 : ℝ) 1) (h2 : σ.2 ∈ Icc (0 : ℝ) 1) :
    expPostVar q γ ρ σ ≤ q * (1 - q) := by
  rw [E_eq]
  have h := G_sum Finset.univ (fun m => ∑ s : Bool × Bool, Kf σ s m * (q * sigLaw γ ρ true s.1 s.2))
    (fun m => ∑ s : Bool × Bool, Kf σ s m * ((1 - q) * sigLaw γ ρ false s.1 s.2))
    (fun m => Finset.sum_nonneg fun s _ => mul_nonneg (Kf_nonneg h1 h2 s m)
      (mul_nonneg hq0 (sigLaw_nonneg hγ0 hγ1 hρ0 hρ1 _ _ _)))
    (fun m => Finset.sum_nonneg fun s _ => mul_nonneg (Kf_nonneg h1 h2 s m)
      (mul_nonneg (sub_nonneg.2 hq1) (sigLaw_nonneg hγ0 hγ1 hρ0 hρ1 _ _ _)))
  have hx : ∀ c : ℝ, ∀ ω : Bool,
      ∑ m : Bool × Bool, ∑ s : Bool × Bool, Kf σ s m * (c * sigLaw γ ρ ω s.1 s.2) = c := by
    intro c ω
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, Kf_sum, one_mul]
    rw [← Finset.mul_sum, sigLaw_sum, mul_one]
  rw [hx, hx] at h
  have hG : G q (1 - q) = q * (1 - q) := by
    unfold G; rw [show q + (1 - q) = 1 by ring, div_one]
  linarith

lemma E_10 {q γ ρ : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    expPostVar q γ ρ (1, 0) = q * (1 - q) := by
  rw [E_eq]
  have hk : ∀ s m, Kf (1, 0) s m = (if m.1 then (1 : ℝ) else 0) * (if m.2 then 1 else 0) := by
    intro s m; rcases s with ⟨a, b⟩; rcases m with ⟨c, d⟩
    cases a <;> cases b <;> cases c <;> cases d <;> simp [Kf, fcast]
  simp only [hk, ← Finset.mul_sum, sigLaw_sum, mul_one]
  simp [Fintype.sum_prod_type, Fintype.sum_bool, G]

/-! ### Best responses -/

lemma mix_diff (pay : Bool → Bool → Bool → ℝ) (q γ ρ : ℝ) (σ : ℝ × ℝ) (s : Bool) (x y : ℝ) :
    mixPay pay q γ ρ σ s x - mixPay pay q γ ρ σ s y = (x - y) * dU pay q γ ρ σ s := by
  unfold mixPay dU; ring

lemma br_one {pay : Bool → Bool → Bool → ℝ} {q γ ρ : ℝ} {σ : ℝ × ℝ} {s : Bool}
    (hd : 0 ≤ dU pay q γ ρ σ s) :
    ∀ x ∈ Icc (0 : ℝ) 1, mixPay pay q γ ρ σ s x ≤ mixPay pay q γ ρ σ s 1 := by
  intro x hx
  have h := mix_diff pay q γ ρ σ s x 1
  have : (x - 1) * dU pay q γ ρ σ s ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith [hx.2]) hd
  linarith

lemma br_zero {pay : Bool → Bool → Bool → ℝ} {q γ ρ : ℝ} {σ : ℝ × ℝ} {s : Bool}
    (hd : dU pay q γ ρ σ s = 0) (y : ℝ) :
    ∀ x ∈ Icc (0 : ℝ) 1, mixPay pay q γ ρ σ s x ≤ mixPay pay q γ ρ σ s y := by
  intro x _
  have h := mix_diff pay q γ ρ σ s x y
  rw [hd, mul_zero] at h
  linarith

lemma dU_nonneg_of_pos {pay : Bool → Bool → Bool → ℝ} {q γ ρ : ℝ} {σ : ℝ × ℝ} {s : Bool}
    {y : ℝ} (hy : 0 < y)
    (hbr : ∀ x ∈ Icc (0 : ℝ) 1, mixPay pay q γ ρ σ s x ≤ mixPay pay q γ ρ σ s y) :
    0 ≤ dU pay q γ ρ σ s := by
  have h1 := hbr 0 ⟨le_refl _, zero_le_one⟩
  have h2 := mix_diff pay q γ ρ σ s 0 y
  by_contra hneg
  push_neg at hneg
  have : 0 < (0 - y) * dU pay q γ ρ σ s := mul_pos_of_neg_of_neg (by linarith) hneg
  linarith

lemma nonneg_of_div {N p : ℝ} (hp : 0 < p) (h : 0 ≤ N / p) : 0 ≤ N := by
  by_contra hn
  push_neg at hn
  have := div_neg_of_neg_of_pos hn hp
  linarith

/-! ### Payoff differences in closed form -/

lemma sigProb_T (q γ ρ : ℝ) : sigProb q γ ρ true = q * γ + (1 - q) * (1 - γ) := by
  simp [sigProb, Fintype.sum_bool, prior, sigLaw]; ring

lemma sigProb_F (q γ ρ : ℝ) : sigProb q γ ρ false = (1 - q) * γ + q * (1 - γ) := by
  simp [sigProb, Fintype.sum_bool, prior, sigLaw]; ring

def NL (W1 W2 q γ c h l : ℝ) : ℝ :=
  W1 * (γ * (γ - q) + c) + W2 * ((1 - γ) * (γ - q) - c)
    - (W1 - W2) * ((1 - q) * (γ ^ 2 + c) + q * ((1 - γ) ^ 2 + c)) * l
    + (W1 - W2) * (γ * (1 - γ) - c) * h

def NH (W1 W2 q γ c h l : ℝ) : ℝ :=
  W1 * (γ * (γ - (1 - q)) + c) + W2 * ((1 - γ) * (γ - (1 - q)) - c)
    - (W1 - W2) * (q * (γ ^ 2 + c) + (1 - q) * ((1 - γ) ^ 2 + c)) * h
    + (W1 - W2) * (γ * (1 - γ) - c) * l

lemma rank_dUF (w1 w0 w2 q γ ρ : ℝ) (σ : ℝ × ℝ) :
    dU (rankPay w1 w0 w2) q γ ρ σ false
      = NL (w1 - w0) (w0 - w2) q γ (chi γ ρ) σ.1 σ.2 / sigProb q γ ρ false := by
  unfold dU condPay
  rw [div_sub_div_same]
  congr 1
  simp [Fintype.sum_bool, prior, sigLaw, fcast, rankPay, NL]
  ring

lemma rank_dUT (w1 w0 w2 q γ ρ : ℝ) (σ : ℝ × ℝ) :
    dU (rankPay w1 w0 w2) q γ ρ σ true
      = NH (w1 - w0) (w0 - w2) q γ (chi γ ρ) σ.1 σ.2 / sigProb q γ ρ true := by
  unfold dU condPay
  rw [div_sub_div_same]
  congr 1
  simp [Fintype.sum_bool, prior, sigLaw, fcast, rankPay, NH]
  ring

lemma bench_dUF (q γ ρ : ℝ) (σ : ℝ × ℝ) :
    dU benchPay q γ ρ σ false = (γ - q) / sigProb q γ ρ false := by
  unfold dU condPay
  rw [div_sub_div_same]
  congr 1
  simp [Fintype.sum_bool, prior, sigLaw, fcast, benchPay]
  ring

lemma bench_dUT (q γ ρ : ℝ) (σ : ℝ × ℝ) :
    dU benchPay q γ ρ σ true = (q + γ - 1) / sigProb q γ ρ true := by
  unfold dU condPay
  rw [div_sub_div_same]
  congr 1
  simp [Fintype.sum_bool, prior, sigLaw, fcast, benchPay]
  ring

/-! ### The rank game's most informative equilibrium: pure algebra -/

lemma core_exists {cl al be ch ah : ℝ} (hal : 0 < al) (hah : 0 < ah) (hbe : 0 ≤ be)
    (hcl : 0 < cl) (hch : 0 < ch) (h11 : cl + be < al) (hdet : be ^ 2 < al * ah)
    (hS : al * ah - be ^ 2 ≤ (al + be) * ch + (ah + be) * cl) :
    ∃ hs ls : ℝ, 0 < hs ∧ hs ≤ 1 ∧ 0 < ls ∧ ls < 1 ∧ 1 ≤ hs + ls ∧ cl - al * ls + be * hs = 0 ∧
      ((hs = 1 ∧ 0 ≤ ch - ah * hs + be * ls) ∨ (hs < 1 ∧ ch - ah * hs + be * ls = 0)) := by
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

/-! ### Most informative equilibria -/

lemma MI_unique {E : Set (ℝ × ℝ)} {σ τ : ℝ × ℝ} (hσ : IsMostInformative E σ)
    (hτ : IsMostInformative E τ) : σ = τ :=
  Prod.ext (le_antisymm (hτ.2 σ hσ.1).1 (hσ.2 τ hτ.1).1)
    (le_antisymm (hτ.2 σ hσ.1).2 (hσ.2 τ hτ.1).2)

lemma top_MI {pay : Bool → Bool → Bool → ℝ} {q γ ρ : ℝ}
    (h11 : IsSymEq pay q γ ρ (1, 1)) :
    IsMostInformative {σ | IsSymEq pay q γ ρ σ} (1, 1) :=
  ⟨h11, fun e he => ⟨he.1.2, he.2.1.2⟩⟩

lemma qmin_relL (w1 w0 w2 q γ ρ : ℝ) (hW2 : 0 < w0 - w2)
    (hD : (1 - γ) * phi w1 w0 w2 + γ ≠ 0) :
    NL (w1 - w0) (w0 - w2) q γ (chi γ ρ) 1 1
      = (w0 - w2) * ((1 - γ) * phi w1 w0 w2 + γ) * (qmin γ ρ (phi w1 w0 w2) - q) := by
  have hq : qmin γ ρ (phi w1 w0 w2) * ((1 - γ) * phi w1 w0 w2 + γ)
      = phi w1 w0 w2 * (γ * (1 - γ) - chi γ ρ) + γ ^ 2 + chi γ ρ := by
    unfold qmin
    rw [sub_mul, mul_assoc, div_mul_cancel₀ _ hD]
    ring
  have hφ : (w0 - w2) * phi w1 w0 w2 = w1 - w0 := by
    unfold phi
    field_simp
  unfold NL
  linear_combination (-(w0 - w2)) * hq + (-(γ * (1 - γ) - chi γ ρ - q * (1 - γ))) * hφ

lemma qmin_relH (w1 w0 w2 q γ ρ : ℝ) (hW2 : 0 < w0 - w2)
    (hD : (1 - γ) * phi w1 w0 w2 + γ ≠ 0) :
    NH (w1 - w0) (w0 - w2) q γ (chi γ ρ) 1 1
      = (w0 - w2) * ((1 - γ) * phi w1 w0 w2 + γ) * (qmin γ ρ (phi w1 w0 w2) - (1 - q)) := by
  have hq : qmin γ ρ (phi w1 w0 w2) * ((1 - γ) * phi w1 w0 w2 + γ)
      = phi w1 w0 w2 * (γ * (1 - γ) - chi γ ρ) + γ ^ 2 + chi γ ρ := by
    unfold qmin
    rw [sub_mul, mul_assoc, div_mul_cancel₀ _ hD]
    ring
  have hφ : (w0 - w2) * phi w1 w0 w2 = w1 - w0 := by
    unfold phi
    field_simp
  unfold NH
  linear_combination (-(w0 - w2)) * hq + (-(γ * (1 - γ) - chi γ ρ - (1 - q) * (1 - γ))) * hφ

lemma Pi_lt {q E1 E2 : ℝ} (hq : 0 < q * (1 - q)) (h1 : 0 < E1) (h12 : E1 < E2) :
    q * (1 - q) / E2 - 1 < q * (1 - q) / E1 - 1 := by
  have := div_lt_div_of_pos_left hq h1 h12
  linarith

lemma E11_pos {q γ ρ : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) : 0 < expPostVar q γ ρ (1, 1) := by
  rw [E_11]
  have hc := chi_nonneg hγ0.le hγ1.le hρ0
  have hP : 0 < γ ^ 2 + chi γ ρ := by have := pow_pos hγ0 2; linarith
  have h1γ : 0 < 1 - γ := by linarith
  have hQ : 0 < (1 - γ) ^ 2 + chi γ ρ := by have := pow_pos h1γ 2; linarith
  have h1q : 0 < 1 - q := by linarith
  have hnn : ∀ s : Bool × Bool,
      0 ≤ G (q * sigLaw γ ρ true s.1 s.2) ((1 - q) * sigLaw γ ρ false s.1 s.2) :=
    fun s => G_nonneg (mul_nonneg hq0.le (sigLaw_nonneg hγ0.le hγ1.le hρ0 hρ1 _ _ _))
      (mul_nonneg h1q.le (sigLaw_nonneg hγ0.le hγ1.le hρ0 hρ1 _ _ _))
  have hsingle := Finset.single_le_sum (fun s _ => hnn s) (Finset.mem_univ (true, true))
  have hpos : 0 < G (q * sigLaw γ ρ true (true, true).1 (true, true).2)
      ((1 - q) * sigLaw γ ρ false (true, true).1 (true, true).2) := by
    show 0 < q * (γ ^ 2 + chi γ ρ) * ((1 - q) * ((1 - γ) ^ 2 + chi γ ρ))
      / (q * (γ ^ 2 + chi γ ρ) + (1 - q) * ((1 - γ) ^ 2 + chi γ ρ))
    have a1 := mul_pos hq0 hP
    have a2 := mul_pos h1q hQ
    exact div_pos (mul_pos a1 a2) (add_pos a1 a2)
  linarith

end P5B1

open AnalystRank.Informativeness Set in
theorem solution (γ ρ w1 w0 w2 : ℝ) (hγ0 : 1 / 2 < γ) (hγ1 : γ < 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hw1 : w0 < w1) (hw2 : w2 < w0) (hφ : phi w1 w0 w2 ≠ 1) :
    (∀ (q : ℝ) (σ σB : ℝ × ℝ), 1 / 2 ≤ q → q < 1 →
        IsMostInformative (rankEqSet w1 w0 w2 q γ ρ) σ →
        IsMostInformative (benchEqSet q γ ρ) σB →
        informativeness q γ ρ σ < informativeness q γ ρ σB →
        1 < phi w1 w0 w2 ∧ 0 < ρ ∧ qmin γ ρ (phi w1 w0 w2) < q ∧ q ≤ γ) ∧
    (1 < phi w1 w0 w2 → 0 < ρ → ∀ q : ℝ, 1 / 2 ≤ q → qmin γ ρ (phi w1 w0 w2) < q → q ≤ γ →
        (∃ σ : ℝ × ℝ, IsMostInformative (rankEqSet w1 w0 w2 q γ ρ) σ) ∧
        (∃ σB : ℝ × ℝ, IsMostInformative (benchEqSet q γ ρ) σB) ∧
        ∀ σ σB : ℝ × ℝ, IsMostInformative (rankEqSet w1 w0 w2 q γ ρ) σ →
          IsMostInformative (benchEqSet q γ ρ) σB →
          informativeness q γ ρ σ < informativeness q γ ρ σB) := by
  have hW1 : 0 < w1 - w0 := by linarith
  have hW2 : 0 < w0 - w2 := by linarith
  have hφpos : 0 < phi w1 w0 w2 := by unfold phi; exact div_pos hW1 hW2
  have hDpos : 0 < (1 - γ) * phi w1 w0 w2 + γ := by
    have : 0 < 1 - γ := by linarith
    positivity
  have hγ0' : (0 : ℝ) ≤ γ := by linarith
  have hc := P5B1.chi_nonneg hγ0' hγ1.le hρ0
  -- the bench game's most informative equilibrium for q ≤ γ
  have bench11 : ∀ q : ℝ, 1 / 2 ≤ q → q ≤ γ →
      IsMostInformative (benchEqSet q γ ρ) (1, 1) := by
    intro q hq hqγ
    have hspT : 0 < sigProb q γ ρ true := by
      rw [P5B1.sigProb_T]
      have : 0 < 1 - γ := by linarith
      have : 0 ≤ 1 - q := by linarith
      nlinarith
    have hspF : 0 < sigProb q γ ρ false := by
      rw [P5B1.sigProb_F]
      have : 0 < 1 - γ := by linarith
      have : 0 ≤ 1 - q := by linarith
      nlinarith
    refine P5B1.top_MI ⟨⟨zero_le_one, le_refl _⟩, ⟨zero_le_one, le_refl _⟩, by norm_num, ?_, ?_⟩
    · apply P5B1.br_one
      rw [P5B1.bench_dUT]
      exact div_nonneg (by linarith) hspT.le
    · apply P5B1.br_one
      rw [P5B1.bench_dUF]
      exact div_nonneg (by linarith) hspF.le
  constructor
  · intro q σ σB hq0 hq1 hMI hMIB hlt
    have hσ : IsSymEq (rankPay w1 w0 w2) q γ ρ σ := hMI.1
    have hspT : 0 < sigProb q γ ρ true := by
      rw [P5B1.sigProb_T]
      have : 0 < 1 - γ := by linarith
      have : 0 < 1 - q := by linarith
      nlinarith
    have hspF : 0 < sigProb q γ ρ false := by
      rw [P5B1.sigProb_F]
      have : 0 < 1 - γ := by linarith
      have : 0 < 1 - q := by linarith
      nlinarith
    by_cases hqγ : q ≤ γ
    · have hB : σB = (1, 1) := P5B1.MI_unique hMIB (bench11 q hq0 hqγ)
      have hqm : qmin γ ρ (phi w1 w0 w2) < q := by
        by_contra hcq
        push_neg at hcq
        have h11 : IsSymEq (rankPay w1 w0 w2) q γ ρ (1, 1) := by
          refine ⟨⟨zero_le_one, le_refl _⟩, ⟨zero_le_one, le_refl _⟩, by norm_num, ?_, ?_⟩
          · apply P5B1.br_one
            rw [P5B1.rank_dUT]
            refine div_nonneg ?_ hspT.le
            rw [P5B1.qmin_relH w1 w0 w2 q γ ρ hW2 hDpos.ne']
            have : 0 ≤ qmin γ ρ (phi w1 w0 w2) - (1 - q) := by linarith
            positivity
          · apply P5B1.br_one
            rw [P5B1.rank_dUF]
            refine div_nonneg ?_ hspF.le
            rw [P5B1.qmin_relL w1 w0 w2 q γ ρ hW2 hDpos.ne']
            have : 0 ≤ qmin γ ρ (phi w1 w0 w2) - q := by linarith
            positivity
        have hA : σ = (1, 1) := P5B1.MI_unique hMI (P5B1.top_MI h11)
        rw [hA, hB] at hlt
        exact lt_irrefl _ hlt
      refine ⟨?_, ?_, hqm, hqγ⟩
      · by_contra hcφ
        push_neg at hcφ
        have hlt1 : phi w1 w0 w2 < 1 := lt_of_le_of_ne hcφ hφ
        have : γ ≤ qmin γ ρ (phi w1 w0 w2) := by
          unfold qmin
          have : (phi w1 w0 w2 - 1) / ((1 - γ) * phi w1 w0 w2 + γ) < 0 :=
            div_neg_of_neg_of_pos (by linarith) hDpos
          nlinarith
        linarith
      · by_contra hcρ
        push_neg at hcρ
        have h0 : ρ = 0 := le_antisymm hcρ hρ0
        have : qmin γ ρ (phi w1 w0 w2) = γ := by
          unfold qmin chi; rw [h0]; ring
        linarith
    · push_neg at hqγ
      exfalso
      have hB' : IsSymEq benchPay q γ ρ σB := hMIB.1
      have h2 : σB.2 = 0 := by
        by_contra hne
        have hpos : 0 < σB.2 := lt_of_le_of_ne hB'.2.1.1 (Ne.symm hne)
        have := P5B1.dU_nonneg_of_pos hpos hB'.2.2.2.2
        rw [P5B1.bench_dUF] at this
        have := P5B1.nonneg_of_div hspF this
        linarith
      have h1 : σB.1 = 1 := by linarith [hB'.1.2, hB'.2.2.1]
      have hσB : σB = (1, 0) := Prod.ext h1 h2
      have hq01 : 0 < q * (1 - q) := by
        have : 0 < 1 - q := by linarith
        have : 0 < q := by linarith
        positivity
      have hPiB : informativeness q γ ρ σB = 0 := by
        rw [hσB]; unfold informativeness
        rw [P5B1.E_10 (by linarith) hq1.le, div_self hq01.ne']; ring
      have hE1 := P5B1.E11_pos (by linarith) hq1 (by linarith) hγ1 hρ0 hρ1
      have hE := P5B1.E_ge (by linarith) hq1.le hγ0' hγ1.le hρ0 hρ1 hσ.1 hσ.2.1
      have hEle := P5B1.E_le (by linarith) hq1.le hγ0' hγ1.le hρ0 hρ1 hσ.1 hσ.2.1
      have hPi : 0 ≤ informativeness q γ ρ σ := by
        unfold informativeness
        have hEp : 0 < expPostVar q γ ρ σ := by linarith
        have : 1 ≤ q * (1 - q) / expPostVar q γ ρ σ := by
          rw [le_div_iff₀ hEp]; linarith
        linarith
      linarith
  · intro hφ1 hρpos q hq hqm hqγ
    have hq1 : q < 1 := by linarith
    have hq0 : 0 < q := by linarith
    have h1q : 0 < 1 - q := by linarith
    have hW12 : w0 - w2 < w1 - w0 := by
      have h' : 1 < (w1 - w0) / (w0 - w2) := hφ1
      rwa [one_lt_div hW2] at h'
    have hγp : 0 < γ := by linarith
    have h1γ : 0 < 1 - γ := by linarith
    have hcpos : 0 < chi γ ρ := by
      unfold chi
      positivity
    have ha := P5B1.a_nonneg (ρ := ρ) hγ0' hγ1.le hρ1
    have hP : 0 < γ ^ 2 + chi γ ρ := by have := pow_pos hγp 2; linarith
    have hQ : 0 < (1 - γ) ^ 2 + chi γ ρ := by have := pow_pos h1γ 2; linarith
    have hspT : 0 < sigProb q γ ρ true := by
      rw [P5B1.sigProb_T]; nlinarith [mul_pos hq0 hγp, mul_pos h1q h1γ]
    have hspF : 0 < sigProb q γ ρ false := by
      rw [P5B1.sigProb_F]; nlinarith [mul_pos h1q hγp, mul_pos hq0 h1γ]
    have hk : 0 < w1 - w0 - (w0 - w2) := by linarith
    have hal : 0 < ((w1 - w0 - (w0 - w2)) * ((1 - q) * (γ ^ 2 + chi γ ρ) + q * ((1 - γ) ^ 2 + chi γ ρ))) := mul_pos hk (by nlinarith [mul_pos h1q hP, mul_pos hq0 hQ])
    have hah : 0 < ((w1 - w0 - (w0 - w2)) * (q * (γ ^ 2 + chi γ ρ) + (1 - q) * ((1 - γ) ^ 2 + chi γ ρ))) := mul_pos hk (by nlinarith [mul_pos hq0 hP, mul_pos h1q hQ])
    have hbe : 0 ≤ ((w1 - w0 - (w0 - w2)) * (γ * (1 - γ) - chi γ ρ)) := mul_nonneg hk.le ha
    have hcl : 0 < ((w1 - w0) * (γ * (γ - q) + chi γ ρ) + (w0 - w2) * ((1 - γ) * (γ - q) - chi γ ρ)) := by
      have e : ((w1 - w0) * (γ * (γ - q) + chi γ ρ) + (w0 - w2) * ((1 - γ) * (γ - q) - chi γ ρ)) = (γ - q) * ((w1 - w0) * γ + (w0 - w2) * (1 - γ))
          + chi γ ρ * (w1 - w0 - (w0 - w2)) := by ring
      rw [e]
      have h1 : 0 ≤ (γ - q) * ((w1 - w0) * γ + (w0 - w2) * (1 - γ)) :=
        mul_nonneg (by linarith) (by nlinarith [mul_pos hW1 hγp, mul_pos hW2 h1γ])
      have h2 : 0 < chi γ ρ * (w1 - w0 - (w0 - w2)) := mul_pos hcpos hk
      linarith
    have hch : 0 < ((w1 - w0) * (γ * (γ - (1 - q)) + chi γ ρ) + (w0 - w2) * ((1 - γ) * (γ - (1 - q)) - chi γ ρ)) := by
      have e : ((w1 - w0) * (γ * (γ - (1 - q)) + chi γ ρ) + (w0 - w2) * ((1 - γ) * (γ - (1 - q)) - chi γ ρ)) = (γ - (1 - q)) * ((w1 - w0) * γ + (w0 - w2) * (1 - γ))
          + chi γ ρ * (w1 - w0 - (w0 - w2)) := by ring
      rw [e]
      have h1 : 0 ≤ (γ - (1 - q)) * ((w1 - w0) * γ + (w0 - w2) * (1 - γ)) :=
        mul_nonneg (by linarith) (by nlinarith [mul_pos hW1 hγp, mul_pos hW2 h1γ])
      have h2 : 0 < chi γ ρ * (w1 - w0 - (w0 - w2)) := mul_pos hcpos hk
      linarith
    have h11 : ((w1 - w0) * (γ * (γ - q) + chi γ ρ) + (w0 - w2) * ((1 - γ) * (γ - q) - chi γ ρ)) + ((w1 - w0 - (w0 - w2)) * (γ * (1 - γ) - chi γ ρ)) < ((w1 - w0 - (w0 - w2)) * ((1 - q) * (γ ^ 2 + chi γ ρ) + q * ((1 - γ) ^ 2 + chi γ ρ))) := by
      have hN := P5B1.qmin_relL w1 w0 w2 q γ ρ hW2 hDpos.ne'
      have hneg : (w0 - w2) * ((1 - γ) * phi w1 w0 w2 + γ) * (qmin γ ρ (phi w1 w0 w2) - q) < 0 :=
        mul_neg_of_pos_of_neg (mul_pos hW2 hDpos) (by linarith)
      unfold P5B1.NL at hN
      linarith
    have hdet : ((w1 - w0 - (w0 - w2)) * (γ * (1 - γ) - chi γ ρ)) ^ 2 < ((w1 - w0 - (w0 - w2)) * ((1 - q) * (γ ^ 2 + chi γ ρ) + q * ((1 - γ) ^ 2 + chi γ ρ))) * ((w1 - w0 - (w0 - w2)) * (q * (γ ^ 2 + chi γ ρ) + (1 - q) * ((1 - γ) ^ 2 + chi γ ρ))) := by
      have e : ((w1 - w0 - (w0 - w2)) * ((1 - q) * (γ ^ 2 + chi γ ρ) + q * ((1 - γ) ^ 2 + chi γ ρ))) * ((w1 - w0 - (w0 - w2)) * (q * (γ ^ 2 + chi γ ρ) + (1 - q) * ((1 - γ) ^ 2 + chi γ ρ))) - ((w1 - w0 - (w0 - w2)) * (γ * (1 - γ) - chi γ ρ)) ^ 2 = (w1 - w0 - (w0 - w2)) ^ 2
          * (chi γ ρ + q * (1 - q) * (2 * γ - 1) ^ 2) := by ring
      have : 0 < (w1 - w0 - (w0 - w2)) ^ 2 * (chi γ ρ + q * (1 - q) * (2 * γ - 1) ^ 2) :=
        mul_pos (pow_pos hk 2) (add_pos_of_pos_of_nonneg hcpos
          (mul_nonneg (mul_nonneg hq0.le h1q.le) (sq_nonneg _)))
      linarith
    have hS : ((w1 - w0 - (w0 - w2)) * ((1 - q) * (γ ^ 2 + chi γ ρ) + q * ((1 - γ) ^ 2 + chi γ ρ))) * ((w1 - w0 - (w0 - w2)) * (q * (γ ^ 2 + chi γ ρ) + (1 - q) * ((1 - γ) ^ 2 + chi γ ρ))) - ((w1 - w0 - (w0 - w2)) * (γ * (1 - γ) - chi γ ρ)) ^ 2 ≤ (((w1 - w0 - (w0 - w2)) * ((1 - q) * (γ ^ 2 + chi γ ρ) + q * ((1 - γ) ^ 2 + chi γ ρ))) + ((w1 - w0 - (w0 - w2)) * (γ * (1 - γ) - chi γ ρ))) * ((w1 - w0) * (γ * (γ - (1 - q)) + chi γ ρ) + (w0 - w2) * ((1 - γ) * (γ - (1 - q)) - chi γ ρ)) + (((w1 - w0 - (w0 - w2)) * (q * (γ ^ 2 + chi γ ρ) + (1 - q) * ((1 - γ) ^ 2 + chi γ ρ))) + ((w1 - w0 - (w0 - w2)) * (γ * (1 - γ) - chi γ ρ))) * ((w1 - w0) * (γ * (γ - q) + chi γ ρ) + (w0 - w2) * ((1 - γ) * (γ - q) - chi γ ρ)) := by
      have e : (((w1 - w0 - (w0 - w2)) * ((1 - q) * (γ ^ 2 + chi γ ρ) + q * ((1 - γ) ^ 2 + chi γ ρ))) + ((w1 - w0 - (w0 - w2)) * (γ * (1 - γ) - chi γ ρ))) * ((w1 - w0) * (γ * (γ - (1 - q)) + chi γ ρ) + (w0 - w2) * ((1 - γ) * (γ - (1 - q)) - chi γ ρ)) + (((w1 - w0 - (w0 - w2)) * (q * (γ ^ 2 + chi γ ρ) + (1 - q) * ((1 - γ) ^ 2 + chi γ ρ))) + ((w1 - w0 - (w0 - w2)) * (γ * (1 - γ) - chi γ ρ))) * ((w1 - w0) * (γ * (γ - q) + chi γ ρ) + (w0 - w2) * ((1 - γ) * (γ - q) - chi γ ρ)) - (((w1 - w0 - (w0 - w2)) * ((1 - q) * (γ ^ 2 + chi γ ρ) + q * ((1 - γ) ^ 2 + chi γ ρ))) * ((w1 - w0 - (w0 - w2)) * (q * (γ ^ 2 + chi γ ρ) + (1 - q) * ((1 - γ) ^ 2 + chi γ ρ))) - ((w1 - w0 - (w0 - w2)) * (γ * (1 - γ) - chi γ ρ)) ^ 2)
          = (w1 - w0 - (w0 - w2)) * ((w1 - w0) + (w0 - w2)) * q * (1 - q) * (2 * γ - 1) := by ring
      have : 0 ≤ (w1 - w0 - (w0 - w2)) * ((w1 - w0) + (w0 - w2)) * q * (1 - q) * (2 * γ - 1) := by
        have : 0 ≤ 2 * γ - 1 := by linarith
        have : 0 ≤ (w1 - w0) + (w0 - w2) := by linarith
        positivity
      linarith
    obtain ⟨hs, ls, hs0, hs1, ls0, ls1, hsum, hLeq, hcase⟩ :=
      P5B1.core_exists hal hah hbe hcl hch h11 hdet hS
    have hstarEq : IsSymEq (rankPay w1 w0 w2) q γ ρ (hs, ls) := by
      refine ⟨⟨hs0.le, hs1⟩, ⟨ls0.le, ls1.le⟩, ?_, ?_, ?_⟩
      · show 1 - ls ≤ hs
        linarith
      · rcases hcase with ⟨hh, hN⟩ | ⟨_, hN⟩
        · subst hh
          refine P5B1.br_one ?_
          rw [P5B1.rank_dUT]
          refine div_nonneg ?_ hspT.le
          unfold P5B1.NH
          dsimp only
          linarith
        · refine P5B1.br_zero ?_ _
          rw [P5B1.rank_dUT]
          have : P5B1.NH (w1 - w0) (w0 - w2) q γ (chi γ ρ) (hs, ls).1 (hs, ls).2 = 0 := by
            unfold P5B1.NH
            dsimp only
            linarith
          rw [this, zero_div]
      · refine P5B1.br_zero ?_ _
        rw [P5B1.rank_dUF]
        have : P5B1.NL (w1 - w0) (w0 - w2) q γ (chi γ ρ) (hs, ls).1 (hs, ls).2 = 0 := by
          unfold P5B1.NL
          dsimp only
          linarith
        rw [this, zero_div]
    have hMIstar : IsMostInformative (rankEqSet w1 w0 w2 q γ ρ) (hs, ls) := by
      refine ⟨hstarEq, fun e he => ?_⟩
      have he' : IsSymEq (rankPay w1 w0 w2) q γ ρ e := he
      refine P5B1.core_dom hal hah hbe hdet hLeq hcase hs0 ls0 he'.1.2 ?_ ?_
      · intro hl
        have h1 := P5B1.dU_nonneg_of_pos hl he'.2.2.2.2
        rw [P5B1.rank_dUF] at h1
        have h2 := P5B1.nonneg_of_div hspF h1
        unfold P5B1.NL at h2
        linarith
      · intro hh
        have h1 := P5B1.dU_nonneg_of_pos hh he'.2.2.2.1
        rw [P5B1.rank_dUT] at h1
        have h2 := P5B1.nonneg_of_div hspT h1
        unfold P5B1.NH at h2
        linarith
    have hB := bench11 q hq hqγ
    refine ⟨⟨_, hMIstar⟩, ⟨_, hB⟩, ?_⟩
    intro σ σB h1 h2
    rw [P5B1.MI_unique h1 hMIstar, P5B1.MI_unique h2 hB]
    have hq01 : 0 < q * (1 - q) := mul_pos hq0 h1q
    unfold informativeness
    exact P5B1.Pi_lt hq01 (P5B1.E11_pos hq0 hq1 hγp hγ1 hρ0 hρ1)
      (P5B1.E_gt hq0 hq1 hγ0 hγ1 hρ0 hρ1 ⟨hs0.le, hs1⟩ ⟨ls0.le, ls1.le⟩ hs0 ls1)
