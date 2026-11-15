-- Prove2me | Definitions.Def_RPLib_S3_EllW2W
-- name    : RPLib_S3_EllW2W
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T13:34:06.84059+00:00
-- url     : https://prove2.me/theorems/5ab8c643-b3f5-4c01-9432-2de48d6ddef3
-- title:
--   The Eichler-Selberg trace formula in weight two: the weighted counts `W_c(t)`
-- statement:
--   The weighted counts `W_c(t)`.
--
--   * `WcF M n δ' c t = Σ_{a ∈ fib n c t} levelCount(mkT n (c,t) a)/2` (all traces) and
--     `Wc M n δ' c t = Σ_{a ∈ fib n c t} wtN (mkT n (c,t) a)` (the factor in `zero_mode_ct` for `w = wtN`).
--   * `Wc_eq_ite`: `Wc = 0` on exceptional traces (`t² < 4n` or `t² - 4n` a square), `= WcF` otherwise;
--     exceptional traces satisfy `|t| ≤ 2n` (`abs_le_of_excT`), `tsum_Wc_mul` splits off the finite exceptional part.
--   * `WcF_periodic`: period `|c|·M` in `t`; `norm_WcF_le`; `sum_card_fib_le`: `Σ_{t < |c|K} #fib ≤ |c| K n`;
--     `trivial_disc` (generic): partial sums of `f - mean` are bounded by `2 Σ_{period} ‖f‖`.
--   * `wtN_tconj`, `wtN_c0`, `wtN_det`: the hypotheses of `zero_mode_ct` for `w = wtN`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2U2

/-!
# S3-ES-Wt2 (O6, file W): the weighted counts `W_c(t)`

* `WcF M n δ' c t = Σ_{a ∈ fib n c t} levelCount(mkT n (c,t) a)/2` (all traces) and
  `Wc M n δ' c t = Σ_{a ∈ fib n c t} wtN (mkT n (c,t) a)` (the factor in `zero_mode_ct` for `w = wtN`).
* `Wc_eq_ite`: `Wc = 0` on exceptional traces (`t² < 4n` or `t² - 4n` a square), `= WcF` otherwise;
  exceptional traces satisfy `|t| ≤ 2n` (`abs_le_of_excT`), `tsum_Wc_mul` splits off the finite exceptional part.
* `WcF_periodic`: period `|c|·M` in `t`; `norm_WcF_le`; `sum_card_fib_le`: `Σ_{t < |c|K} #fib ≤ |c| K n`;
  `trivial_disc` (generic): partial sums of `f - mean` are bounded by `2 Σ_{period} ‖f‖`.
* `wtN_tconj`, `wtN_c0`, `wtN_det`: the hypotheses of `zero_mode_ct` for `w = wtN`.
-/

open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Kernel RamanujanPetersson.EllTerm

variable {M : ℕ} [NeZero M]

/-! ## `wtN` as a zero-mode weight -/

lemma wtN_tconj (n : ℤ) (δ' : ZMod M) (g : S3.Conj.Mat) : wtN M n δ' (tconj 1 g) = wtN M n δ' g := by
  rw [tconj_one]; exact wtN_conj n δ' _ g

lemma wtN_c0 (n : ℤ) (δ' : ZMod M) (g : S3.Conj.Mat) (h : g 1 0 = 0) : wtN M n δ' g = 0 := by
  have hs : IsSP g := ⟨g 0 0 - g 1 1, by rw [Matrix.det_fin_two, h]; ring⟩
  unfold wtN; rw [if_pos hs]

lemma wtN_det (n : ℤ) (δ' : ZMod M) (g : S3.Conj.Mat) (h : g.det ≠ n) : wtN M n δ' g = 0 :=
  wtN_of_not fun h' => h h'.1

/-! ## Exceptional traces -/

/-- Elliptic (`t² < 4n`) or split (`t² - 4n` a square) traces. -/
def ExcT (n t : ℤ) : Prop := t ^ 2 < 4 * n ∨ ∃ r : ℤ, t ^ 2 - 4 * n = r ^ 2

noncomputable instance decExcT (n t : ℤ) : Decidable (ExcT n t) := Classical.propDecidable _

lemma wtN_mkT (n : ℤ) (δ' : ZMod M) {c t a : ℤ} (hc : c ≠ 0) (ha : c ∣ a * (t - a) - n) :
    wtN M n δ' (mkT n (c, t) a) =
      if ExcT n t then 0 else (S3.levelCount M δ' (mkT n (c, t) a) : ℂ) / 2 := by
  obtain ⟨e0, -, e2, e3⟩ := mkT_entries n (c, t) a
  simp only at e2 e3
  have hd : (mkT n (c, t) a).det = n := (det_mkT_iff n c t a).2 ha
  have htr : (mkT n (c, t) a) 0 0 + (mkT n (c, t) a) 1 1 = t := by rw [e0, e3]; ring
  have hSP : IsSP (mkT n (c, t) a) ↔ ∃ r : ℤ, t ^ 2 - 4 * n = r ^ 2 := by
    unfold IsSP; rw [htr, hd]
  have hR : HypPar.IsRest (mkT n (c, t) a) ↔ ¬ t ^ 2 < 4 * n := by
    unfold HypPar.IsRest; rw [htr, hd, e2]; simp [hc]
  unfold wtN HypPar.wt
  by_cases h1 : ∃ r : ℤ, t ^ 2 - 4 * n = r ^ 2
  · rw [if_pos (hSP.2 h1), if_pos (show ExcT n t from Or.inr h1)]
  · rw [if_neg (fun h => h1 (hSP.1 h))]
    by_cases h2 : t ^ 2 < 4 * n
    · rw [if_neg (fun h => (hR.1 h.2) h2), if_pos (show ExcT n t from Or.inl h2)]
    · rw [if_pos ⟨hd, hR.2 h2⟩, if_neg (show ¬ ExcT n t by unfold ExcT; tauto)]

lemma abs_le_of_excT {n t : ℤ} (hn : 0 < n) (h : ExcT n t) : |t| ≤ 2 * n := by
  by_contra hlt
  push Not at hlt
  have h5 : 2 * n + 1 ≤ |t| := by omega
  have h6 : (2 * n + 1) ^ 2 ≤ |t| ^ 2 := pow_le_pow_left₀ (by omega) h5 2
  rw [sq_abs] at h6
  rcases h with h | ⟨r, hr⟩
  · nlinarith
  · have h1 : r ^ 2 < t ^ 2 := by linarith
    have e : (|t| - 1) ^ 2 = t ^ 2 - 2 * |t| + 1 := by rw [← sq_abs t]; ring
    have h2 : (|t| - 1) ^ 2 < r ^ 2 := by rw [e]; linarith
    have h3 : |r| < |t| := sq_lt_sq.1 h1
    have h4 : |(|t| - 1)| < |r| := sq_lt_sq.1 h2
    rw [abs_of_nonneg (by linarith : (0 : ℤ) ≤ |t| - 1)] at h4
    omega

/-- The (finite) set of exceptional traces. -/
def excF (n : ℤ) : Finset ℤ := (Finset.Icc (-(2 * n)) (2 * n)).filter (ExcT n)

lemma mem_excF {n t : ℤ} (hn : 0 < n) : t ∈ excF n ↔ ExcT n t := by
  unfold excF
  rw [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    have := abs_le_of_excT hn h
    exact ⟨⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩, h⟩

/-! ## The counts -/

/-- All traces: `Σ_{a ∈ fib} levelCount(mkT)/2`. -/
def WcF (M : ℕ) [NeZero M] (n : ℤ) (δ' : ZMod M) (c t : ℤ) : ℂ :=
  ∑ a ∈ fib n c t, (S3.levelCount M δ' (mkT n (c, t) a) : ℂ) / 2

/-- The zero-mode factor of `zero_mode_ct` for `w = wtN`. -/
def Wc (M : ℕ) [NeZero M] (n : ℤ) (δ' : ZMod M) (c t : ℤ) : ℂ :=
  ∑ a ∈ fib n c t, wtN M n δ' (mkT n (c, t) a)

lemma Wc_eq_ite (n : ℤ) (δ' : ZMod M) (c t : ℤ) :
    Wc M n δ' c t = if ExcT n t then 0 else WcF M n δ' c t := by
  by_cases hc : c = 0
  · subst hc; simp [Wc, WcF, fib]
  unfold Wc WcF
  split_ifs with h
  · refine Finset.sum_eq_zero fun a ha => ?_
    rw [wtN_mkT n δ' hc (Finset.mem_filter.1 ha).2, if_pos h]
  · refine Finset.sum_congr rfl fun a ha => ?_
    rw [wtN_mkT n δ' hc (Finset.mem_filter.1 ha).2, if_neg h]

/-- Splitting off the exceptional traces. -/
lemma tsum_Wc_mul {n : ℤ} (hn : 0 < n) (δ' : ZMod M) (c : ℤ) (Φ : ℤ → ℂ)
    (hs : Summable fun t => WcF M n δ' c t * Φ t) :
    ∑' t, Wc M n δ' c t * Φ t =
      ∑' t, WcF M n δ' c t * Φ t - ∑ t ∈ excF n, WcF M n δ' c t * Φ t := by
  classical
  have e : ∀ t, Wc M n δ' c t * Φ t =
      WcF M n δ' c t * Φ t - (if t ∈ excF n then WcF M n δ' c t * Φ t else 0) := by
    intro t
    rw [Wc_eq_ite]
    by_cases h : ExcT n t
    · rw [if_pos h, if_pos ((mem_excF hn).2 h)]; ring
    · rw [if_neg h, if_neg (fun h' => h ((mem_excF hn).1 h'))]; ring
  have hE : ∀ t ∉ excF n, (if t ∈ excF n then WcF M n δ' c t * Φ t else 0) = 0 :=
    fun t ht => if_neg ht
  rw [tsum_congr e, hs.tsum_sub (summable_of_ne_finset_zero hE), tsum_eq_sum hE]
  congr 1
  exact Finset.sum_congr rfl fun t ht => if_pos ht

/-! ## Periodicity -/

lemma fib_add (n c t k : ℤ) : fib n c (t + c * k) = fib n c t := by
  unfold fib
  refine Finset.filter_congr fun a _ => ?_
  rw [show a * (t + c * k - a) - n = a * (t - a) - n + c * (a * k) by ring]
  exact dvd_add_left (dvd_mul_right c _)

omit [NeZero M] in
lemma mkT_add_map (n : ℤ) {c : ℤ} (hc : c ≠ 0) (t a k : ℤ) :
    (mkT n (c, t + c * (M * k)) a).map (Int.castRingHom (ZMod M)) =
      (mkT n (c, t) a).map (Int.castRingHom (ZMod M)) := by
  have hb : (a * (t + c * (M * k) - a) - n) / c = (a * (t - a) - n) / c + a * (M * k) := by
    rw [show a * (t + c * (M * k) - a) - n = a * (t - a) - n + c * (a * (M * k)) by ring]
    exact Int.add_mul_ediv_left _ _ hc
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mkT, hb]

lemma WcF_add (n : ℤ) (δ' : ZMod M) (c t k : ℤ) :
    WcF M n δ' c (t + c * (M * k)) = WcF M n δ' c t := by
  by_cases hc : c = 0
  · subst hc; simp [WcF, fib]
  unfold WcF
  rw [fib_add]
  refine Finset.sum_congr rfl fun a _ => ?_
  unfold S3.levelCount; rw [mkT_add_map n hc]

lemma WcF_periodic (n : ℤ) (δ' : ZMod M) (c t : ℤ) :
    WcF M n δ' c (t + ((c.natAbs * M : ℕ) : ℤ)) = WcF M n δ' c t := by
  rw [Nat.cast_mul, Int.natCast_natAbs]
  rcases le_or_gt 0 c with h | h
  · rw [abs_of_nonneg h, show c * (M : ℤ) = c * (M * 1) by ring, WcF_add]
  · rw [abs_of_neg h, show -c * (M : ℤ) = c * (M * (-1)) by ring, WcF_add]

/-! ## Trivial bounds -/

lemma card_fib_le (n c t : ℤ) : (fib n c t).card ≤ c.natAbs := by
  unfold fib
  refine (Finset.card_filter_le _ _).trans ?_
  rw [Int.card_Ico, sub_zero, ← Int.natCast_natAbs, Int.toNat_natCast]

lemma levelCount_le (δ' : ZMod M) (g : S3.Conj.Mat) :
    (S3.levelCount M δ' g : ℝ) ≤ Fintype.card (Fin 2 → ZMod M) := by
  have h1 : S3.levelCount M δ' g ≤ Fintype.card (Fin 2 → ZMod M) := by
    unfold S3.levelCount; exact (Finset.card_filter_le _ _).trans_eq Finset.card_univ
  exact_mod_cast h1

lemma norm_WcF_le' (n : ℤ) (δ' : ZMod M) (c t : ℤ) :
    ‖WcF M n δ' c t‖ ≤ (fib n c t).card * (Fintype.card (Fin 2 → ZMod M) : ℝ) / 2 := by
  unfold WcF
  refine (norm_sum_le _ _).trans ?_
  rw [mul_div_assoc, ← nsmul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun a _ => ?_
  rw [norm_div, Complex.norm_natCast, Complex.norm_two]
  exact div_le_div_of_nonneg_right (levelCount_le δ' _) (by norm_num)

lemma norm_WcF_le (n : ℤ) (δ' : ZMod M) (c t : ℤ) :
    ‖WcF M n δ' c t‖ ≤ c.natAbs * (Fintype.card (Fin 2 → ZMod M) : ℝ) / 2 := by
  refine (norm_WcF_le' n δ' c t).trans ?_
  have : ((fib n c t).card : ℝ) ≤ c.natAbs := by exact_mod_cast card_fib_le n c t
  gcongr

lemma norm_Wc_le (n : ℤ) (δ' : ZMod M) (c t : ℤ) : ‖Wc M n δ' c t‖ ≤ ‖WcF M n δ' c t‖ := by
  classical
  rw [Wc_eq_ite]; split_ifs
  · rw [norm_zero]; exact norm_nonneg _
  · exact le_rfl

/-- Solutions of `a u ≡ m (mod c)` in `[0, |c| K)`: at most `K · gcd(a, c)`. -/
lemma card_sol_le {c : ℤ} (hc : c ≠ 0) (a m : ℤ) (K : ℕ) :
    ((Finset.range (c.natAbs * K)).filter fun u : ℕ => c ∣ a * u - m).card ≤ K * Int.gcd a c := by
  have hG0 : 0 < Int.gcd a c := Int.gcd_pos_of_ne_zero_right a hc
  obtain ⟨a', c', hg1, ha, hcc⟩ := Int.exists_gcd_one (show 0 < Int.gcd a c from hG0)
  set G := Int.gcd a c with hG
  set q : ℕ := c'.natAbs with hq
  have hcq : c.natAbs = G * q := by
    rw [hcc, Int.natAbs_mul, Int.natAbs_natCast, mul_comm]
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · rw [h, mul_zero, Int.natAbs_eq_zero] at hcq; exact absurd hcq hc
    · exact h
  have key : ∀ u1 u2 : ℕ, c ∣ a * u1 - m → c ∣ a * u2 - m → u1 % q = u2 % q := by
    intro u1 u2 h1 h2
    have h3 : c ∣ a * ((u1 : ℤ) - u2) := by
      have := dvd_sub h1 h2
      rwa [show a * (u1 : ℤ) - m - (a * u2 - m) = a * ((u1 : ℤ) - u2) by ring] at this
    rw [hcc, ha, show a' * (G : ℤ) * ((u1 : ℤ) - u2) = a' * ((u1 : ℤ) - u2) * G by ring] at h3
    have h4 : c' ∣ a' * ((u1 : ℤ) - u2) :=
      (mul_dvd_mul_iff_right (by exact_mod_cast hG0.ne')).1 h3
    have h5 : c' ∣ (u1 : ℤ) - u2 :=
      Int.dvd_of_dvd_mul_right_of_gcd_one h4 (by rw [Int.gcd_comm]; exact hg1)
    have h6 : (q : ℤ) ∣ (u2 : ℤ) - u1 := by
      rw [hq, Int.natAbs_dvd]
      exact (dvd_neg.2 h5).trans (by rw [neg_sub])
    exact (Nat.modEq_iff_dvd.2 h6)
  have hmap : ∀ u ∈ (Finset.range (c.natAbs * K)).filter (fun u : ℕ => c ∣ a * u - m),
      u / q ∈ Finset.range (K * G) := by
    intro u hu
    have hu' := Finset.mem_range.1 (Finset.mem_filter.1 hu).1
    rw [Finset.mem_range, Nat.div_lt_iff_lt_mul hq0]
    rw [hcq] at hu'
    calc u < G * q * K := hu'
      _ = K * G * q := by ring
  have hinj : Set.InjOn (fun u : ℕ => u / q)
      ((Finset.range (c.natAbs * K)).filter (fun u : ℕ => c ∣ a * u - m) : Set ℕ) := by
    intro u1 hu1 u2 hu2 he
    have h1 := (Finset.mem_filter.1 hu1).2
    have h2 := (Finset.mem_filter.1 hu2).2
    have hm := key u1 u2 h1 h2
    simp only at he
    rw [← Nat.div_add_mod u1 q, ← Nat.div_add_mod u2 q, he, hm]
  have := Finset.card_le_card_of_injOn (fun u : ℕ => u / q) hmap hinj
  rwa [Finset.card_range] at this

/-- `Σ_{t ∈ [0, |c| K)} #fib n c t ≤ |c| · K · n`. -/
lemma sum_card_fib_le {n : ℤ} (hn : 0 < n) {c : ℤ} (hc : c ≠ 0) (K : ℕ) :
    ∑ u ∈ Finset.range (c.natAbs * K), (fib n c u).card ≤ c.natAbs * (K * n.toNat) := by
  classical
  have e : ∀ u : ℕ, (fib n c u).card =
      ∑ a ∈ Finset.Ico 0 |c|, if c ∣ a * ((u : ℤ) - a) - n then 1 else 0 := by
    intro u; unfold fib; rw [Finset.card_filter]
  simp_rw [e]
  rw [Finset.sum_comm]
  have hcard : (Finset.Ico 0 |c|).card = c.natAbs := by
    rw [Int.card_Ico, sub_zero, ← Int.natCast_natAbs, Int.toNat_natCast]
  refine (Finset.sum_le_card_nsmul (Finset.Ico 0 |c|) _ (K * n.toNat) fun a _ => ?_).trans
    (by rw [hcard, smul_eq_mul])
  rw [← Finset.card_filter]
  have hf : (Finset.range (c.natAbs * K)).filter (fun u : ℕ => c ∣ a * ((u : ℤ) - a) - n) =
      (Finset.range (c.natAbs * K)).filter (fun u : ℕ => c ∣ a * u - (a * a + n)) :=
    Finset.filter_congr fun u _ => by rw [show a * ((u : ℤ) - a) - n = a * u - (a * a + n) by ring]
  rw [hf]
  rcases Finset.eq_empty_or_nonempty
    ((Finset.range (c.natAbs * K)).filter (fun u : ℕ => c ∣ a * u - (a * a + n))) with h | ⟨u0, hu0⟩
  · rw [h, Finset.card_empty]; exact Nat.zero_le _
  · refine (card_sol_le hc a (a * a + n) K).trans (Nat.mul_le_mul_left K ?_)
    have h1 : c ∣ a * u0 - (a * a + n) := (Finset.mem_filter.1 hu0).2
    have hgn : (Int.gcd a c : ℤ) ∣ n := by
      have ha : (Int.gcd a c : ℤ) ∣ a := Int.gcd_dvd_left a c
      have h2 := dvd_sub (dvd_mul_of_dvd_left ha (u0 : ℤ)) ((Int.gcd_dvd_right a c).trans h1)
      have h3 := dvd_sub h2 (dvd_mul_of_dvd_left ha a)
      rwa [show a * (u0 : ℤ) - (a * u0 - (a * a + n)) - a * a = n by ring] at h3
    have := Int.le_of_dvd hn hgn
    omega

/-! ## Means and the trivial discrepancy -/

/-- Generic trivial discrepancy: partial sums of `f - μ` over a period are at most `2 Σ_{period} ‖f‖`. -/
lemma trivial_disc {f : ℤ → ℂ} {μ : ℂ} {q : ℕ} (hμ : ∑ u ∈ Finset.range q, f u = q * μ)
    (m : ℕ) (hm : m ≤ q) :
    ‖∑ u ∈ Finset.range m, (f u - μ)‖ ≤ 2 * ∑ u ∈ Finset.range q, ‖f u‖ := by
  have h1 : ‖∑ u ∈ Finset.range m, (f u - μ)‖ ≤ ∑ u ∈ Finset.range q, ‖f u‖ + q * ‖μ‖ := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · refine (norm_sum_le _ _).trans ?_
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hm)
        fun _ _ _ => norm_nonneg _
    · rw [norm_mul, Complex.norm_natCast]
      gcongr
  have h2 : (q : ℝ) * ‖μ‖ ≤ ∑ u ∈ Finset.range q, ‖f u‖ := by
    have : ‖(q : ℂ) * μ‖ = q * ‖μ‖ := by rw [norm_mul, Complex.norm_natCast]
    rw [← this, ← hμ]; exact norm_sum_le _ _
  linarith

/-- The mean of `WcF M n δ' c` over its period `|c| M`. -/
def muc (M : ℕ) [NeZero M] (n : ℤ) (δ' : ZMod M) (c : ℤ) : ℂ :=
  (∑ u ∈ Finset.range (c.natAbs * M), WcF M n δ' c u) / ((c.natAbs * M : ℕ) : ℂ)

lemma sum_WcF_eq (n : ℤ) (δ' : ZMod M) {c : ℤ} (hc : c ≠ 0) :
    ∑ u ∈ Finset.range (c.natAbs * M), WcF M n δ' c u = ((c.natAbs * M : ℕ) : ℂ) * muc M n δ' c := by
  have h : ((c.natAbs * M : ℕ) : ℂ) ≠ 0 := by
    have : 0 < c.natAbs * M := Nat.mul_pos (Int.natAbs_pos.2 hc) (NeZero.pos M)
    exact_mod_cast this.ne'
  unfold muc; field_simp

/-- `Σ_{period} ‖WcF‖ ≤ |c| M n · #(Fin 2 → ZMod M) / 2`. -/
lemma sum_norm_WcF_le {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {c : ℤ} (hc : c ≠ 0) :
    ∑ u ∈ Finset.range (c.natAbs * M), ‖WcF M n δ' c u‖ ≤
      (c.natAbs * (M * n.toNat) : ℕ) * (Fintype.card (Fin 2 → ZMod M) : ℝ) / 2 := by
  have h1 := sum_card_fib_le hn hc M
  have h2 : (∑ u ∈ Finset.range (c.natAbs * M), ((fib n c u).card : ℝ)) ≤
      (c.natAbs * (M * n.toNat) : ℕ) := by exact_mod_cast h1
  calc ∑ u ∈ Finset.range (c.natAbs * M), ‖WcF M n δ' c u‖
      ≤ ∑ u ∈ Finset.range (c.natAbs * M),
          ((fib n c u).card : ℝ) * (Fintype.card (Fin 2 → ZMod M) : ℝ) / 2 :=
        Finset.sum_le_sum fun u _ => norm_WcF_le' n δ' c u
    _ = (∑ u ∈ Finset.range (c.natAbs * M), ((fib n c u).card : ℝ)) *
          (Fintype.card (Fin 2 → ZMod M) : ℝ) / 2 := by
        rw [Finset.sum_mul, Finset.sum_div]
    _ ≤ _ := by gcongr

end RamanujanPetersson.EllW2


