-- Prove2me | Definitions.Def_RPLib_S3_HypParP
-- name    : RPLib_S3_HypParP
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T21:41:54.832194+00:00
-- url     : https://prove2.me/theorems/ad8ff738-69ce-485b-b4c4-9a7d9e94d7f8
-- title:
--   The Eichler-Selberg trace formula, hyperbolic part P: the per-pair conversion
-- statement:
--   Bookkeeping for periodic sums and the evaluation of the weighted top-edge constants for each pair $(a, d)$ with $ad = n$ (split hyperbolic $a \ne d$ and parabolic $a = d$) in terms of level counts.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer: the Eichler-Selberg trace formula on $S_k(\Gamma_1(M))$ for $k \ge 3$, proved by Zagier's kernel method). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976 (with the Correction in later printings)

import Mathlib
import Definitions.Def_RPLib_S3_HypParM

/-!
# S3-HypParTerms, part P (O8, the per-pair conversion)

* `sum_range_mul_periodic`, `sum_Ico_nat`, `sum_zmod_val`: bookkeeping for periodic sums.
* `wt_ut_hyp`: for `a ≠ d`, `a d = n`, `wt (ut a r d) = levelCount / 2`.
* `sum_Ico_wt` (P1): `Σ_{r ∈ Ico 0 |a-d|} wt (ut a r d) = |a - d| · (Σ_b levelCount (ut a b d)) / (2M)`.
* `sum_wt_par` (P2): `Σ_x wt (ut s (x.val + M) s) = (Σ_b levelCount (ut s b s)) / 2`.
* `hypC_eq`, `parC_eq`, `core_const`, `pairQ`, **`pair_hyp`**, **`pair_par`** (P3):
  `n^{k-1} B_k⁻¹ · (-(top-edge limit of the pair (a, d))) = pairQ a d`
  with `pairQ a d = (1/2) A(a,d) a^{k-1} (sign(a-d) - sign(a+d))`, `A(a,d) = (Σ_b levelCount)/(2M)`.
* `sum_pairQ_eq`: `Σ_{e ∣ n} Σ_{σ = ±1} pairQ (σe) (σ n/e) = hypG1` (H6 restated).
-/

open Complex Finset
open scoped Real

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.HypPar

section PerPair

lemma sum_range_mul_periodic (F : ℕ → ℂ) (K : ℕ) (hF : ∀ r, F (r + K) = F r) (q : ℕ) :
    ∑ r ∈ range (q * K), F r = (q : ℂ) * ∑ r ∈ range K, F r := by
  have hF' : ∀ q r : ℕ, F (q * K + r) = F r := by
    intro q
    induction q with
    | zero => intro r; simp
    | succ q ih =>
      intro r
      rw [show (q + 1) * K + r = (q * K + r) + K by ring, hF, ih]
  induction q with
  | zero => simp
  | succ q ih =>
    rw [add_mul, one_mul, Finset.sum_range_add, ih]
    simp only [hF']
    push_cast
    ring

lemma sum_Ico_nat (G : ℤ → ℂ) (P : ℕ) :
    ∑ r ∈ Finset.Ico (0 : ℤ) P, G r = ∑ r ∈ range P, G r := by
  refine Finset.sum_nbij' (fun r : ℤ => r.toNat) (fun r : ℕ => (r : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro r hr
    simp only [Finset.mem_Ico] at hr
    simp only [Finset.mem_range]
    omega
  · intro r hr
    simp only [Finset.mem_range] at hr
    simp only [Finset.mem_Ico]
    omega
  · intro r hr
    simp only [Finset.mem_Ico] at hr
    simp only [Int.toNat_of_nonneg hr.1]
  · intro r _
    simp
  · intro r hr
    simp only [Finset.mem_Ico] at hr
    simp only [Int.toNat_of_nonneg hr.1]

lemma sum_zmod_val {M : ℕ} [NeZero M] (F : ℕ → ℂ) :
    ∑ x : ZMod M, F x.val = ∑ r ∈ range M, F r := by
  refine Finset.sum_nbij' (fun x : ZMod M => x.val) (fun r : ℕ => (r : ZMod M)) ?_ ?_ ?_ ?_ ?_
  · intro x _
    simp only [Finset.mem_range]
    exact ZMod.val_lt x
  · intro r _
    exact Finset.mem_univ _
  · intro x _
    exact ZMod.natCast_zmod_val x
  · intro r hr
    simp only [Finset.mem_range] at hr
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hr]
  · intro x _
    rfl

variable {M : ℕ} [NeZero M]

/-- For `a ≠ d` and `a d = n`, every `ut a r d` is a rest element of determinant `n`. -/
lemma wt_ut_hyp (n : ℤ) (δ' : ZMod M) {a d : ℤ} (had : a * d = n) (hγ : a ≠ d) (r : ℤ) :
    wt M n δ' (ut a r d) = (S3.levelCount M δ' (ut a r d) : ℂ) / 2 := by
  have hR : IsRest (ut a r d) := by
    intro h
    rcases h with h | h
    · apply hγ
      have h3 := h.2.2
      simpa using h3
    · rw [det_ut] at h
      simp only [ut_00, ut_11] at h
      nlinarith [sq_nonneg (a - d)]
  unfold wt
  rw [if_pos ⟨by rw [det_ut, had], hR⟩]

/-- (P1) The hyperbolic period sum in terms of the level average. -/
theorem sum_Ico_wt (n : ℤ) (δ' : ZMod M) {a d : ℤ} (had : a * d = n) (hγ : a ≠ d) :
    ∑ r ∈ Finset.Ico 0 |a - d|, wt M n δ' (ut a r d) =
      ((a - d).natAbs : ℂ) *
        (((∑ b : ZMod M, S3.levelCount M δ' (ut a (b.val : ℤ) d) : ℕ) : ℂ) / (2 * (M : ℂ))) := by
  set P : ℕ := (a - d).natAbs with hPdef
  have hPz : ((P : ℕ) : ℤ) = |a - d| := Int.natCast_natAbs (a - d)
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  rw [← hPz, sum_Ico_nat (fun r => wt M n δ' (ut a r d)) P]
  have hperP : ∀ r : ℕ, wt M n δ' (ut a ((r + P : ℕ) : ℤ) d) = wt M n δ' (ut a (r : ℤ) d) := by
    intro r
    rcases Int.natAbs_eq (a - d) with h | h
    · rw [← hPdef] at h
      have e : ((r + P : ℕ) : ℤ) = (r : ℤ) - (a - d) * (-1) := by
        push_cast
        linarith
      rw [e, wt_ut_sub_mul]
    · rw [← hPdef] at h
      have e : ((r + P : ℕ) : ℤ) = (r : ℤ) - (a - d) * 1 := by
        push_cast
        linarith
      rw [e, wt_ut_sub_mul]
  have hperM : ∀ r : ℕ, wt M n δ' (ut a ((r + M : ℕ) : ℤ) d) = wt M n δ' (ut a (r : ℤ) d) := by
    intro r
    rw [wt_ut_hyp n δ' had hγ, wt_ut_hyp n δ' had hγ,
      levelCount_ut_mod δ' a d (b := ((r + M : ℕ) : ℤ)) (b' := (r : ℤ)) (by simp)]
  have h1 := sum_range_mul_periodic (fun r : ℕ => wt M n δ' (ut a (r : ℤ) d)) P hperP M
  have h2 := sum_range_mul_periodic (fun r : ℕ => wt M n δ' (ut a (r : ℤ) d)) M hperM P
  rw [show M * P = P * M from Nat.mul_comm M P] at h1
  have hMP := h1.symm.trans h2
  have hY : ∑ r ∈ range M, wt M n δ' (ut a (r : ℤ) d) =
      ((∑ b : ZMod M, S3.levelCount M δ' (ut a (b.val : ℤ) d) : ℕ) : ℂ) / 2 := by
    rw [← sum_zmod_val (fun r : ℕ => wt M n δ' (ut a (r : ℤ) d))]
    simp only [wt_ut_hyp n δ' had hγ]
    rw [← Finset.sum_div, Nat.cast_sum]
  have hX : ∑ r ∈ range P, wt M n δ' (ut a (r : ℤ) d) =
      (P : ℂ) * (∑ r ∈ range M, wt M n δ' (ut a (r : ℤ) d)) / M := by
    rw [eq_div_iff hM0]
    linear_combination hMP
  rw [hX, hY]
  ring

/-- (P2) The parabolic class sum in terms of the level count. -/
theorem sum_wt_par (n : ℤ) (δ' : ZMod M) {s : ℤ} (hss : s * s = n) :
    ∑ x : ZMod M, wt M n δ' (ut s ((x.val : ℤ) + M) s) =
      ((∑ b : ZMod M, S3.levelCount M δ' (ut s (b.val : ℤ) s) : ℕ) : ℂ) / 2 := by
  rw [Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hb : (x.val : ℤ) + M ≠ 0 := by omega
  unfold wt
  rw [if_pos ⟨by rw [det_ut, hss], (isRest_ut_par s _).2 hb⟩,
    levelCount_ut_mod δ' s s (b := (x.val : ℤ) + M) (b' := (x.val : ℤ))
      (by rw [cast_rep, Int.cast_natCast, ZMod.natCast_zmod_val])]

lemma negI_pow (m : ℕ) : (-I) ^ m = (I ^ m)⁻¹ := by
  rw [← Complex.inv_I, inv_pow]

/-- `|a - d| · hypC a d m` in closed form. -/
lemma hypC_eq {a d : ℤ} (hγ : a ≠ d) (m : ℕ) :
    ((a - d).natAbs : ℂ) * hypC a d m =
      -((1 / (m : ℂ)) * (((2 * (d : ℂ)) ^ m * (I ^ m)⁻¹)⁻¹ *
        ((π : ℂ) * (((a - d).sign : ℂ) - ((a + d).sign : ℂ)) * I))) := by
  have hne : (a : ℝ) - d ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hγ)
  have hr : (((a - d).natAbs : ℕ) : ℝ) = |(a : ℝ) - d| := by
    rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub]
  have habs : (((a - d).natAbs : ℕ) : ℂ) * ((|((a : ℝ) - d)⁻¹| : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, hr, abs_inv,
      mul_inv_cancel₀ (abs_ne_zero.2 hne), Complex.ofReal_one]
  have hs1 : Real.sign ((a : ℝ) - d) = (((a - d).sign : ℤ) : ℝ) := by
    rw [← Real.sign_intCast, Int.cast_sub]
  have hs2 : Real.sign ((a : ℝ) + d) = (((a + d).sign : ℤ) : ℝ) := by
    rw [← Real.sign_intCast, Int.cast_add]
  have hpow : ((((-2 * d : ℤ)) : ℂ) * I) ^ m = (2 * (d : ℂ)) ^ m * (I ^ m)⁻¹ := by
    rw [show (((-2 * d : ℤ)) : ℂ) * I = (2 * (d : ℂ)) * (-I) by push_cast; ring, mul_pow, negI_pow]
  unfold hypC
  simp only [hs1, hs2, hpow, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_intCast]
  linear_combination (-(1 / (m : ℂ)) * ((2 * (d : ℂ)) ^ m * (I ^ m)⁻¹)⁻¹ *
    ((π : ℂ) * (((a - d).sign : ℂ) - ((a + d).sign : ℂ)) * I)) * habs

/-- `parC M s m` in closed form. -/
lemma parC_eq (M : ℕ) (s : ℤ) (m : ℕ) :
    parC M s m = (1 / (2 * (m : ℂ) * M)) * (((2 * (s : ℂ)) ^ m * (I ^ m)⁻¹)⁻¹ *
      ((π : ℂ) * (2 * ((s + s).sign : ℂ)) * I)) := by
  have h1 : Real.sign (2 * (s : ℝ)) = (((s + s).sign : ℤ) : ℝ) := by
    rw [← Real.sign_intCast, show ((s + s : ℤ) : ℝ) = 2 * (s : ℝ) by push_cast; ring]
  have h2 : Real.sign (-(2 * (s : ℝ))) = -(((s + s).sign : ℤ) : ℝ) := by
    rw [Real.sign_neg, h1]
  have hc : (cP (2 * (s : ℝ))) ^ m = (2 * (s : ℂ)) ^ m * (I ^ m)⁻¹ := by
    unfold cP
    rw [show -(((2 * (s : ℝ) : ℝ) : ℂ) * I) = (2 * (s : ℂ)) * (-I) by push_cast; ring, mul_pow,
      negI_pow]
  unfold parC
  rw [hc, h1, h2]
  push_cast
  ring

/-- The constant bookkeeping: `n^m B_{m+1}⁻¹ (1/m) ((-2d) i)^{-m} π S i = (1/2) a^m S` for `n = a d`. -/
lemma core_const {m : ℕ} (hm : 1 ≤ m) (a d : ℤ) (hd : d ≠ 0) (A S : ℂ) :
    ((a * d : ℤ) : ℂ) ^ m * (Bergman.bergmanConst (m + 1))⁻¹ *
      (A * ((1 / (m : ℂ)) * (((2 * (d : ℂ)) ^ m * (I ^ m)⁻¹)⁻¹ * ((π : ℂ) * S * I)))) =
    1 / 2 * A * (a : ℂ) ^ m * S := by
  unfold Bergman.bergmanConst
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hI : I ≠ 0 := Complex.I_ne_zero
  have hk : (((m + 1 : ℕ) : ℂ) - 1) = m := by push_cast; ring
  rw [hk]
  push_cast
  field_simp
  ring

/-- The per-pair main term `(1/2) A(a,d) a^{k-1} (sign(a-d) - sign(a+d))` (exactly the summand of
`hyp_pairs_eq` at `(a, d) = (σ e, σ n/e)`). -/
def pairQ (M : ℕ) [NeZero M] (δ' : ZMod M) (k : ℕ) (a d : ℤ) : ℚ :=
  (1 / 2 : ℚ) * (((∑ b : ZMod M, S3.levelCount M δ' (ut a (b.val : ℤ) d) : ℕ) : ℚ) / (2 * (M : ℚ))) *
    ((a : ℤ) : ℚ) ^ (k - 1) * (((a - d).sign : ℚ) - ((a + d).sign : ℚ))

lemma pairQ_cast (δ' : ZMod M) (m : ℕ) (a d : ℤ) :
    ((pairQ M δ' (m + 1) a d : ℚ) : ℂ) =
      1 / 2 * (((∑ b : ZMod M, S3.levelCount M δ' (ut a (b.val : ℤ) d) : ℕ) : ℂ) / (2 * (M : ℂ))) *
        (a : ℂ) ^ m * (((a - d).sign : ℂ) - ((a + d).sign : ℂ)) := by
  unfold pairQ
  simp only [Nat.add_sub_cancel]
  push_cast
  ring

lemma hyp_final {m : ℕ} (hm : 1 ≤ m) {a d : ℤ} (hd : d ≠ 0) (hγ : a ≠ d) (A : ℂ) :
    ((a * d : ℤ) : ℂ) ^ m * (Bergman.bergmanConst (m + 1))⁻¹ *
      (-(((a - d).natAbs : ℂ) * A * hypC a d m)) =
    1 / 2 * A * (a : ℂ) ^ m * (((a - d).sign : ℂ) - ((a + d).sign : ℂ)) := by
  rw [← core_const hm a d hd A]
  rw [show (((a - d).natAbs : ℂ)) * A * hypC a d m = A * ((((a - d).natAbs : ℂ)) * hypC a d m) by ring,
    hypC_eq hγ m]
  ring

/-- (P3, hyperbolic) The top-edge limit of a pair `a ≠ d` contributes `pairQ a d`. -/
theorem pair_hyp {k : ℕ} (hk : 2 ≤ k) (n : ℤ) (δ' : ZMod M) {a d : ℤ} (had : a * d = n)
    (hn : 0 < n) (hγ : a ≠ d) :
    (n : ℂ) ^ (k - 1) * (Bergman.bergmanConst k)⁻¹ *
      (-((∑ r ∈ Finset.Ico 0 |a - d|, wt M n δ' (ut a r d)) * hypC a d (k - 1))) =
    ((pairQ M δ' k a d : ℚ) : ℂ) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  have hd : d ≠ 0 := by
    rintro rfl
    simp at had
    omega
  simp only [Nat.add_sub_cancel]
  rw [sum_Ico_wt n δ' had hγ, ← had, pairQ_cast]
  exact hyp_final hm hd hγ _

/-- (P3, parabolic) The top-edge limit of the pair `a = d = s` contributes `pairQ s s`. -/
theorem pair_par {k : ℕ} (hk : 2 ≤ k) (n : ℤ) (δ' : ZMod M) {s : ℤ} (hss : s * s = n)
    (hn : 0 < n) :
    (n : ℂ) ^ (k - 1) * (Bergman.bergmanConst k)⁻¹ *
      (-((∑ x : ZMod M, wt M n δ' (ut s ((x.val : ℤ) + M) s)) * parC M s (k - 1))) =
    ((pairQ M δ' k s s : ℚ) : ℂ) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  have hs : s ≠ 0 := by
    rintro rfl
    simp at hss
    omega
  simp only [Nat.add_sub_cancel]
  have hshape : ∀ L : ℂ, -(L / 2 * ((1 / (2 * (m : ℂ) * M)) * (((2 * (s : ℂ)) ^ m * (I ^ m)⁻¹)⁻¹ *
      ((π : ℂ) * (2 * ((s + s).sign : ℂ)) * I)))) =
      L / (2 * (M : ℂ)) * ((1 / (m : ℂ)) * (((2 * (s : ℂ)) ^ m * (I ^ m)⁻¹)⁻¹ *
        ((π : ℂ) * (((s - s).sign : ℂ) - ((s + s).sign : ℂ)) * I))) := by
    intro L
    simp only [sub_self, Int.sign_zero, Int.cast_zero, zero_sub]
    ring
  rw [sum_wt_par n δ' hss, parC_eq, hshape, ← hss, pairQ_cast]
  exact core_const hm s s hs _ _

/-- H6 restated with `pairQ`. -/
theorem sum_pairQ_eq {k n : ℕ} (hk : 1 ≤ k) (hn : 0 < n) (hnM : Nat.Coprime n M)
    (δ : ZMod M) (U : ℤ) (hU : (M : ℤ) ∣ (δ.val : ℤ) * U - 1) (D : ℤ)
    (hD : (M : ℤ) ∣ D - n * (δ.val : ℤ)) :
    ∑ e ∈ n.divisors, ∑ σ ∈ ({1, -1} : Finset ℤ),
      pairQ M (D : ZMod M) k (σ * e) (σ * ((n / e : ℕ) : ℤ)) = S3.hypG1 M k n δ :=
  hyp_pairs_eq hk hn hnM δ U hU D hD

end PerPair

end RamanujanPetersson.HypPar


