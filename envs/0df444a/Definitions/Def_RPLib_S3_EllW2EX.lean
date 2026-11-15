-- Prove2me | Definitions.Def_RPLib_S3_EllW2EX
-- name    : RPLib_S3_EllW2EX
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T13:47:55.201145+00:00
-- url     : https://prove2.me/theorems/0aaf2a61-abef-4a1f-9507-58affb65a95d
-- title:
--   The Eichler-Selberg trace formula in weight two: the exceptional traces
-- statement:
--   The exceptional traces.
--
--   * `card_divisors_le_two_sqrt`: `τ(N) ≤ 2 ⌊√N⌋`; `card_divisors_le_sqrt`: `τ(N) ≤ 2 √N` (reals).
--   * `sum_gcd_le`: `Σ_{d < N} gcd(d, N) ≤ N τ(N)`.
--   * `card_fib_sq_le`: `#fib(c,t)² ≤ Σ_{d < |c|} gcd(-2d, c)` (pair count with `card_sol_le`).
--   * `card_fib_le_rpow`: `#fib(c,t) ≤ 2 |c|^(3/4)`; `norm_WcF_le_rpow`: `‖WcF c t‖ ≤ |c|^(3/4) #(Fin 2 → ZMod M)`.
--   * `integral_VS_u_le`: `∫_u VS s c n u y t ≤ (c²)^(-s-1) (y²)^(-s) π / y` for a fixed trace `t`.
--   * `exc_term_le`, `exc_sum_le`: `Σ_{t ∈ excF n} ‖WcF c t‖ ∫_u VS ≤ #excF · L (π/y) (y²)^(-s) |c|^(-5/4)`;
--     `summable_abs_int_rpow54`, `tsum_abs_int_rpow54_le` (`Σ'_c |c|^(-5/4) ≤ 10`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2Z3

/-!
# S3-ES-Wt2 (O6, file EX): the exceptional traces

* `card_divisors_le_two_sqrt`: `τ(N) ≤ 2 ⌊√N⌋`; `card_divisors_le_sqrt`: `τ(N) ≤ 2 √N` (reals).
* `sum_gcd_le`: `Σ_{d < N} gcd(d, N) ≤ N τ(N)`.
* `card_fib_sq_le`: `#fib(c,t)² ≤ Σ_{d < |c|} gcd(-2d, c)` (pair count with `card_sol_le`).
* `card_fib_le_rpow`: `#fib(c,t) ≤ 2 |c|^(3/4)`; `norm_WcF_le_rpow`: `‖WcF c t‖ ≤ |c|^(3/4) #(Fin 2 → ZMod M)`.
* `integral_VS_u_le`: `∫_u VS s c n u y t ≤ (c²)^(-s-1) (y²)^(-s) π / y` for a fixed trace `t`.
* `exc_term_le`, `exc_sum_le`: `Σ_{t ∈ excF n} ‖WcF c t‖ ∫_u VS ≤ #excF · L (π/y) (y²)^(-s) |c|^(-5/4)`;
  `summable_abs_int_rpow54`, `tsum_abs_int_rpow54_le` (`Σ'_c |c|^(-5/4) ≤ 10`).
-/

open MeasureTheory Set Filter Real

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Kernel RamanujanPetersson.EllTerm

variable {M : ℕ} [NeZero M]

/-! ## Divisor counting -/

/-- `τ(N) ≤ 2 ⌊√N⌋`. -/
lemma card_divisors_le_two_sqrt (N : ℕ) : N.divisors.card ≤ 2 * Nat.sqrt N := by
  rw [← Finset.card_filter_add_card_filter_not (s := N.divisors) (fun d => d ≤ Nat.sqrt N),
    two_mul]
  refine add_le_add ?_ ?_
  · calc (N.divisors.filter fun d => d ≤ Nat.sqrt N).card ≤ (Finset.Icc 1 (Nat.sqrt N)).card := by
          refine Finset.card_le_card fun d hd => ?_
          have hd' := Finset.mem_filter.1 hd
          have hdN := Nat.mem_divisors.1 hd'.1
          exact Finset.mem_Icc.2 ⟨Nat.pos_of_dvd_of_pos hdN.1 (Nat.pos_of_ne_zero hdN.2), hd'.2⟩
      _ = Nat.sqrt N := by simp
  · calc (N.divisors.filter fun d => ¬ d ≤ Nat.sqrt N).card ≤ (Finset.Icc 1 (Nat.sqrt N)).card := by
          refine Finset.card_le_card_of_injOn (fun d => N / d) (fun d hd => ?_) (fun d1 hd1 d2 hd2 he => ?_)
          · have hd' := Finset.mem_filter.1 hd
            have hdN := Nat.mem_divisors.1 hd'.1
            have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdN.1 (Nat.pos_of_ne_zero hdN.2)
            have hlt : N < d * d := Nat.sqrt_lt.1 (Nat.lt_of_not_le hd'.2)
            have hq : N / d < d := (Nat.div_lt_iff_lt_mul hd0).2 hlt
            have hqd : N / d * d = N := Nat.div_mul_cancel hdN.1
            refine Finset.mem_Icc.2 ⟨Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hdN.2) hdN.1) hd0, ?_⟩
            refine Nat.le_sqrt.2 ?_
            calc N / d * (N / d) ≤ N / d * d := Nat.mul_le_mul_left _ hq.le
              _ = N := hqd
          · have h1 := Nat.mem_divisors.1 (Finset.mem_filter.1 hd1).1
            have h2 := Nat.mem_divisors.1 (Finset.mem_filter.1 hd2).1
            have he' : N / d1 = N / d2 := he
            calc d1 = N / (N / d1) := (Nat.div_div_self h1.1 h1.2).symm
              _ = N / (N / d2) := by rw [he']
              _ = d2 := Nat.div_div_self h2.1 h2.2
      _ = Nat.sqrt N := by simp

/-- `τ(N) ≤ 2 √N`. -/
lemma card_divisors_le_sqrt (N : ℕ) : (N.divisors.card : ℝ) ≤ 2 * √(N : ℝ) := by
  have h1 : (N.divisors.card : ℝ) ≤ 2 * (Nat.sqrt N : ℝ) := by
    exact_mod_cast card_divisors_le_two_sqrt N
  exact h1.trans (by gcongr; exact Real.nat_sqrt_le_real_sqrt)

/-- `#{d < N : e ∣ d} ≤ N / e` for `e ∣ N`. -/
lemma card_filter_dvd_le (N e : ℕ) (he : e ∣ N) (he0 : 0 < e) :
    ((Finset.range N).filter fun d => e ∣ d).card ≤ N / e := by
  calc ((Finset.range N).filter fun d => e ∣ d).card ≤ (Finset.range (N / e)).card := by
        refine Finset.card_le_card_of_injOn (fun d => d / e) (fun d hd => ?_)
          (fun d1 hd1 d2 hd2 h => ?_)
        · have hd' := Finset.mem_filter.1 hd
          have hdN : d < N := Finset.mem_range.1 hd'.1
          obtain ⟨k, rfl⟩ := hd'.2
          obtain ⟨m, rfl⟩ := he
          refine Finset.mem_range.2 ?_
          show e * k / e < e * m / e
          rw [Nat.mul_div_cancel_left k he0, Nat.mul_div_cancel_left m he0]
          exact Nat.lt_of_mul_lt_mul_left hdN
        · have h1 : e ∣ d1 := (Finset.mem_filter.1 hd1).2
          have h2 : e ∣ d2 := (Finset.mem_filter.1 hd2).2
          have h' : d1 / e = d2 / e := h
          calc d1 = e * (d1 / e) := (Nat.mul_div_cancel' h1).symm
            _ = e * (d2 / e) := by rw [h']
            _ = d2 := Nat.mul_div_cancel' h2
    _ = N / e := Finset.card_range _

/-- `Σ_{d < N} gcd(d, N) ≤ N τ(N)`. -/
lemma sum_gcd_le (N : ℕ) : ∑ d ∈ Finset.range N, Nat.gcd d N ≤ N * N.divisors.card := by
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · subst h0; simp
  have h1 : ∀ d ∈ Finset.range N,
      Nat.gcd d N ≤ ∑ e ∈ N.divisors, if e ∣ d then e else 0 := by
    intro d _
    have hmem : Nat.gcd d N ∈ N.divisors := Nat.mem_divisors.2 ⟨Nat.gcd_dvd_right d N, hN.ne'⟩
    calc Nat.gcd d N = (fun e => if e ∣ d then e else 0) (Nat.gcd d N) := by
          simp only [if_pos (Nat.gcd_dvd_left d N)]
      _ ≤ ∑ e ∈ N.divisors, (fun e => if e ∣ d then e else 0) e :=
          Finset.single_le_sum (f := fun e => if e ∣ d then e else 0) (fun e _ => Nat.zero_le _) hmem
  calc ∑ d ∈ Finset.range N, Nat.gcd d N
      ≤ ∑ d ∈ Finset.range N, ∑ e ∈ N.divisors, if e ∣ d then e else 0 := Finset.sum_le_sum h1
    _ = ∑ e ∈ N.divisors, ∑ d ∈ Finset.range N, if e ∣ d then e else 0 := Finset.sum_comm
    _ ≤ ∑ e ∈ N.divisors, N := by
        refine Finset.sum_le_sum fun e he => ?_
        have he' := Nat.mem_divisors.1 he
        have he0 : 0 < e := Nat.pos_of_dvd_of_pos he'.1 hN
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
        calc ((Finset.range N).filter fun d => e ∣ d).card * e ≤ N / e * e :=
              Nat.mul_le_mul_right _ (card_filter_dvd_le N e he'.1 he0)
          _ = N := Nat.div_mul_cancel he'.1
    _ = N * N.divisors.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-! ## The pair count -/

/-- `gcd(-2d, c) ≤ 2 gcd(d, |c|)`. -/
lemma gcd_neg_two_mul_le {c : ℤ} (hc : c ≠ 0) (d : ℕ) :
    Int.gcd (-2 * (d : ℤ)) c ≤ 2 * Nat.gcd d c.natAbs := by
  have hN : 0 < c.natAbs := Int.natAbs_pos.2 hc
  have e1 : Int.natAbs (-2 * (d : ℤ)) = 2 * d := by
    omega
  have e : Int.gcd (-2 * (d : ℤ)) c = Nat.gcd (2 * d) c.natAbs := by
    rw [Int.gcd_eq_natAbs_gcd_natAbs, e1]
  rw [e]
  refine Nat.le_of_dvd (Nat.mul_pos two_pos (Nat.gcd_pos_of_pos_right d hN)) ?_
  rw [← Nat.gcd_mul_left]
  exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _) (dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) 2)

/-- **Pair count**: `#fib(c,t)² ≤ Σ_{d < |c|} gcd(-2d, c)`. Pairs `(a, a')` of roots map injectively to
`(d, a') = ((a - a') mod c, a')`, and `c ∣ (a - a')(t - a - a')` makes `a'` a root of `-2d·a' + d(t-d) ≡ 0`. -/
lemma card_fib_sq_le (n : ℤ) {c : ℤ} (hc : c ≠ 0) (t : ℤ) :
    (fib n c t).card ^ 2 ≤ ∑ d ∈ Finset.range c.natAbs, Int.gcd (-2 * (d : ℤ)) c := by
  set N := c.natAbs with hNdef
  have hNc : ((N : ℕ) : ℤ) = |c| := Int.natCast_natAbs c
  set T : Finset (ℕ × ℕ) := (Finset.range N ×ˢ Finset.range N).filter
    fun p => c ∣ (-2 * ((p.1 : ℕ) : ℤ)) * ((p.2 : ℕ) : ℤ) - -(((p.1 : ℕ) : ℤ) * (t - ((p.1 : ℕ) : ℤ)))
    with hTdef
  have hT : T.card = ∑ d ∈ Finset.range N,
      ((Finset.range (N * 1)).filter fun u : ℕ =>
        c ∣ (-2 * (d : ℤ)) * (u : ℤ) - -((d : ℤ) * (t - (d : ℤ)))).card := by
    rw [mul_one, hTdef, Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.card_filter]
  have hTle : T.card ≤ ∑ d ∈ Finset.range N, Int.gcd (-2 * (d : ℤ)) c := by
    rw [hT]
    refine Finset.sum_le_sum fun d _ => ?_
    have := card_sol_le hc (-2 * (d : ℤ)) (-((d : ℤ) * (t - (d : ℤ)))) 1
    rw [one_mul] at this
    exact this
  have hmaps : ∀ p ∈ fib n c t ×ˢ fib n c t,
      (((p.1 - p.2) % c).toNat, p.2.toNat) ∈ T := by
    rintro ⟨a, a'⟩ hp
    have ha : a ∈ fib n c t := (Finset.mem_product.1 hp).1
    have ha' : a' ∈ fib n c t := (Finset.mem_product.1 hp).2
    obtain ⟨haI, h1⟩ := Finset.mem_filter.1 ha
    obtain ⟨haI', h2⟩ := Finset.mem_filter.1 ha'
    obtain ⟨ha0, haN⟩ := Finset.mem_Ico.1 haI
    obtain ⟨ha0', haN'⟩ := Finset.mem_Ico.1 haI'
    have hd0 : 0 ≤ (a - a') % c := Int.emod_nonneg _ hc
    have hdN : (a - a') % c < |c| := Int.emod_lt_abs _ hc
    have ed : ((((a - a') % c).toNat : ℕ) : ℤ) = (a - a') % c := Int.toNat_of_nonneg hd0
    have ea : ((a'.toNat : ℕ) : ℤ) = a' := Int.toNat_of_nonneg ha0'
    refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨Finset.mem_range.2 ?_, Finset.mem_range.2 ?_⟩, ?_⟩
    · have : ((((a - a') % c).toNat : ℕ) : ℤ) < ((N : ℕ) : ℤ) := by rw [ed, hNc]; exact hdN
      exact_mod_cast this
    · have : ((a'.toNat : ℕ) : ℤ) < ((N : ℕ) : ℤ) := by rw [ea, hNc]; exact haN'
      exact_mod_cast this
    · show c ∣ (-2 * ((((a - a') % c).toNat : ℕ) : ℤ)) * ((a'.toNat : ℕ) : ℤ) -
          -(((((a - a') % c).toNat : ℕ) : ℤ) * (t - ((((a - a') % c).toNat : ℕ) : ℤ)))
      rw [ed, ea]
      set d := (a - a') % c with hd
      have hk : c ∣ a - a' - d := ⟨(a - a') / c, by rw [hd, Int.emod_def]; ring⟩
      have key : (-2 * d) * a' - -(d * (t - d)) =
          (a * (t - a) - n) - (a' * (t - a') - n) - (a - a' - d) * (t - a - a' - d) := by ring
      rw [key]
      exact dvd_sub (dvd_sub h1 h2) (dvd_mul_of_dvd_left hk _)
  have hinj : Set.InjOn (fun p : ℤ × ℤ => (((p.1 - p.2) % c).toNat, p.2.toNat))
      ((fib n c t ×ˢ fib n c t : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) := by
    rintro ⟨a, a'⟩ hp ⟨b, b'⟩ hq he
    have ha : a ∈ fib n c t := (Finset.mem_product.1 hp).1
    have ha' : a' ∈ fib n c t := (Finset.mem_product.1 hp).2
    have hb : b ∈ fib n c t := (Finset.mem_product.1 hq).1
    have hb' : b' ∈ fib n c t := (Finset.mem_product.1 hq).2
    obtain ⟨ha0, haN⟩ := Finset.mem_Ico.1 (Finset.mem_filter.1 ha).1
    obtain ⟨ha0', _⟩ := Finset.mem_Ico.1 (Finset.mem_filter.1 ha').1
    obtain ⟨hb0, hbN⟩ := Finset.mem_Ico.1 (Finset.mem_filter.1 hb).1
    obtain ⟨hb0', _⟩ := Finset.mem_Ico.1 (Finset.mem_filter.1 hb').1
    have he' : (((a - a') % c).toNat, a'.toNat) = (((b - b') % c).toNat, b'.toNat) := he
    obtain ⟨e1, e2⟩ := Prod.mk.inj he'
    have e2' : a' = b' := by
      have := congrArg (fun k : ℕ => (k : ℤ)) e2
      simp only [Int.toNat_of_nonneg ha0', Int.toNat_of_nonneg hb0'] at this
      exact this
    have e1' : (a - a') % c = (b - b') % c := by
      have := congrArg (fun k : ℕ => (k : ℤ)) e1
      simp only [Int.toNat_of_nonneg (Int.emod_nonneg _ hc)] at this
      exact this
    have e3 : a % c = b % c := by
      have h := Int.ModEq.add_right a' (show Int.ModEq c (a - a') (b - b') from e1')
      rw [← e2'] at h
      simp only [sub_add_cancel] at h
      exact h
    have hpa : a % c = a := by rw [← Int.emod_abs]; exact Int.emod_eq_of_lt ha0 haN
    have hpb : b % c = b := by rw [← Int.emod_abs]; exact Int.emod_eq_of_lt hb0 hbN
    rw [← hpa, e3, hpb, e2']
  have hcard := Finset.card_le_card_of_injOn
    (fun p : ℤ × ℤ => (((p.1 - p.2) % c).toNat, p.2.toNat)) hmaps hinj
  rw [Finset.card_product] at hcard
  rw [sq]
  exact hcard.trans hTle

/-- `#fib(c,t)² ≤ 2 |c| τ(|c|)`. -/
lemma card_fib_sq_le' (n : ℤ) {c : ℤ} (hc : c ≠ 0) (t : ℤ) :
    (fib n c t).card ^ 2 ≤ 2 * (c.natAbs * c.natAbs.divisors.card) := by
  refine (card_fib_sq_le n hc t).trans ?_
  calc ∑ d ∈ Finset.range c.natAbs, Int.gcd (-2 * (d : ℤ)) c
      ≤ ∑ d ∈ Finset.range c.natAbs, 2 * Nat.gcd d c.natAbs :=
        Finset.sum_le_sum fun d _ => gcd_neg_two_mul_le hc d
    _ = 2 * ∑ d ∈ Finset.range c.natAbs, Nat.gcd d c.natAbs := by rw [Finset.mul_sum]
    _ ≤ 2 * (c.natAbs * c.natAbs.divisors.card) := Nat.mul_le_mul_left _ (sum_gcd_le _)

lemma rpow34_sq {x : ℝ} (hx : 0 < x) : (x ^ (3/4 : ℝ)) ^ 2 = x * √x := by
  calc (x ^ (3/4 : ℝ)) ^ 2 = x ^ ((3/4 : ℝ) * ((2 : ℕ) : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    _ = x ^ (1 : ℝ) * x ^ (1/2 : ℝ) := by rw [← Real.rpow_add hx]; norm_num
    _ = x * √x := by rw [Real.rpow_one, Real.sqrt_eq_rpow]

/-- **Exceptional count**: `#fib(c,t) ≤ 2 |c|^(3/4)`. -/
lemma card_fib_le_rpow (n : ℤ) {c : ℤ} (hc : c ≠ 0) (t : ℤ) :
    ((fib n c t).card : ℝ) ≤ 2 * (c.natAbs : ℝ) ^ (3/4 : ℝ) := by
  have hN : (0 : ℝ) < c.natAbs := by exact_mod_cast Int.natAbs_pos.2 hc
  have h1 : ((fib n c t).card : ℝ) ^ 2 ≤ 2 * ((c.natAbs : ℝ) * (c.natAbs.divisors.card : ℝ)) := by
    exact_mod_cast card_fib_sq_le' n hc t
  have h2 : ((fib n c t).card : ℝ) ^ 2 ≤ (2 * (c.natAbs : ℝ) ^ (3/4 : ℝ)) ^ 2 := by
    rw [mul_pow, rpow34_sq hN]
    calc ((fib n c t).card : ℝ) ^ 2 ≤ 2 * ((c.natAbs : ℝ) * (c.natAbs.divisors.card : ℝ)) := h1
      _ ≤ 2 * ((c.natAbs : ℝ) * (2 * √(c.natAbs : ℝ))) := by
          gcongr; exact card_divisors_le_sqrt _
      _ = 2 ^ 2 * ((c.natAbs : ℝ) * √(c.natAbs : ℝ)) := by ring
  have hA : (0 : ℝ) ≤ (fib n c t).card := Nat.cast_nonneg _
  have hB : (0 : ℝ) ≤ 2 * (c.natAbs : ℝ) ^ (3/4 : ℝ) := by positivity
  exact (pow_le_pow_iff_left₀ hA hB two_ne_zero).1 h2

/-- `‖WcF c t‖ ≤ |c|^(3/4) #(Fin 2 → ZMod M)`. -/
lemma norm_WcF_le_rpow (n : ℤ) (δ' : ZMod M) {c : ℤ} (hc : c ≠ 0) (t : ℤ) :
    ‖WcF M n δ' c t‖ ≤ (c.natAbs : ℝ) ^ (3/4 : ℝ) * (Fintype.card (Fin 2 → ZMod M) : ℝ) := by
  refine (norm_WcF_le' n δ' c t).trans ?_
  have h := card_fib_le_rpow n hc t
  have hL : (0 : ℝ) ≤ (Fintype.card (Fin 2 → ZMod M) : ℝ) := Nat.cast_nonneg _
  calc ((fib n c t).card : ℝ) * (Fintype.card (Fin 2 → ZMod M) : ℝ) / 2
      ≤ (2 * (c.natAbs : ℝ) ^ (3/4 : ℝ)) * (Fintype.card (Fin 2 → ZMod M) : ℝ) / 2 := by gcongr
    _ = _ := by ring

/-! ## The `u`-integral at a fixed trace -/

lemma VS_le_u {s : ℝ} (hs : 0 ≤ s) {c n y : ℝ} (hc : c ≠ 0) (hy : 0 < y) (hn : 0 ≤ n) (t u : ℝ) :
    VS s c n u y t ≤ (c ^ 2) ^ (-s - 1) * (y ^ 2) ^ (-s) * (u ^ 2 + y ^ 2)⁻¹ := by
  have hu : 0 < u ^ 2 + y ^ 2 := by positivity
  calc VS s c n u y t ≤ (c ^ 2 * (u ^ 2 + y ^ 2)) ^ (-s - 1) := VS_le_pt hs hc hy.ne' hn t
    _ = (c ^ 2) ^ (-s - 1) * ((u ^ 2 + y ^ 2) ^ (-s) * (u ^ 2 + y ^ 2)⁻¹) := by
        rw [Real.mul_rpow (by positivity) hu.le, Real.rpow_sub_one hu.ne', div_eq_mul_inv]
    _ ≤ (c ^ 2) ^ (-s - 1) * ((y ^ 2) ^ (-s) * (u ^ 2 + y ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_nonpos (by positivity) (le_add_of_nonneg_left (sq_nonneg u))
            (by linarith)) (by positivity)) (by positivity)
    _ = _ := by ring

lemma integral_VS_u_le {s : ℝ} (hs : 0 ≤ s) {c n y : ℝ} (hc : c ≠ 0) (hy : 0 < y) (hn : 0 ≤ n) (t : ℝ) :
    ∫ u, VS s c n u y t ≤ (c ^ 2) ^ (-s - 1) * (y ^ 2) ^ (-s) * (π / y) := by
  have hb : Integrable fun u : ℝ => (c ^ 2) ^ (-s - 1) * (y ^ 2) ^ (-s) * (u ^ 2 + y ^ 2)⁻¹ :=
    (integrable_inv_sq_add_sq hy).const_mul _
  calc ∫ u, VS s c n u y t ≤ ∫ u, (c ^ 2) ^ (-s - 1) * (y ^ 2) ^ (-s) * (u ^ 2 + y ^ 2)⁻¹ :=
        integral_mono (integrable_VS_u hs hc hy hn t) hb fun u => VS_le_u hs hc hy hn t u
    _ = _ := by rw [integral_const_mul, integral_inv_sq_add_sq hy]

lemma abs_rpow34_mul_inv_sq {c : ℝ} (hc : c ≠ 0) :
    |c| ^ (3/4 : ℝ) * (c ^ 2)⁻¹ = |c| ^ (-(5/4 : ℝ)) := by
  have ha : 0 < |c| := abs_pos.2 hc
  rw [← sq_abs c, ← Real.rpow_natCast, ← Real.rpow_neg ha.le, ← Real.rpow_add ha]
  congr 1; norm_num

/-- One exceptional trace: `‖WcF c t‖ ∫_u VS ≤ L (π/y) (y²)^(-s) |c|^(-5/4)`. -/
lemma exc_term_le {n : ℤ} (hn : 0 ≤ n) (δ' : ZMod M) {c : ℤ} (hc : c ≠ 0) {s : ℝ} (hs : 0 ≤ s)
    {y : ℝ} (hy : 0 < y) (t : ℤ) :
    ‖WcF M n δ' c t‖ * ∫ u, VS s c n u y t ≤
      (Fintype.card (Fin 2 → ZMod M) : ℝ) * (π / y) * (y ^ 2) ^ (-s) * |(c : ℝ)| ^ (-(5/4 : ℝ)) := by
  have hc' : (c : ℝ) ≠ 0 := Int.cast_ne_zero.2 hc
  have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 := norm_WcF_le_rpow n δ' hc t
  have h2 := integral_VS_u_le hs hc' hy hn' (t : ℝ)
  have hI : 0 ≤ ∫ u, VS s c n u y t := integral_nonneg fun u => VS_nonneg s hc' hy.ne' hn' _
  have hc1 : (1 : ℝ) ≤ (c : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ |(c : ℝ)| := by exact_mod_cast Int.one_le_abs hc
    nlinarith [sq_abs (c : ℝ), abs_nonneg (c : ℝ)]
  have h3 : ((c : ℝ) ^ 2) ^ (-s - 1) ≤ ((c : ℝ) ^ 2)⁻¹ := by
    rw [← Real.rpow_neg_one]; exact Real.rpow_le_rpow_of_exponent_le hc1 (by linarith)
  have hN : ((c.natAbs : ℕ) : ℝ) = |(c : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  rw [hN] at h1
  have hP : 0 ≤ (y ^ 2) ^ (-s) * (π / y) := by positivity
  calc ‖WcF M n δ' c t‖ * ∫ u, VS s c n u y t
      ≤ (|(c : ℝ)| ^ (3/4 : ℝ) * (Fintype.card (Fin 2 → ZMod M) : ℝ)) *
          (((c : ℝ) ^ 2)⁻¹ * (y ^ 2) ^ (-s) * (π / y)) := by
        refine mul_le_mul h1 (h2.trans ?_) hI (by positivity)
        rw [mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_right h3 hP
    _ = (Fintype.card (Fin 2 → ZMod M) : ℝ) * (π / y) * (y ^ 2) ^ (-s) *
          (|(c : ℝ)| ^ (3/4 : ℝ) * ((c : ℝ) ^ 2)⁻¹) := by ring
    _ = _ := by rw [abs_rpow34_mul_inv_sq hc']

/-- All exceptional traces for one `c`. -/
lemma exc_sum_le {n : ℤ} (hn : 0 ≤ n) (δ' : ZMod M) {c : ℤ} (hc : c ≠ 0) {s : ℝ} (hs : 0 ≤ s)
    {y : ℝ} (hy : 0 < y) :
    ∑ t ∈ excF n, ‖WcF M n δ' c t‖ * ∫ u, VS s c n u y t ≤
      (excF n).card * ((Fintype.card (Fin 2 → ZMod M) : ℝ) * (π / y) * (y ^ 2) ^ (-s)) *
        |(c : ℝ)| ^ (-(5/4 : ℝ)) := by
  calc ∑ t ∈ excF n, ‖WcF M n δ' c t‖ * ∫ u, VS s c n u y t
      ≤ ∑ t ∈ excF n, (Fintype.card (Fin 2 → ZMod M) : ℝ) * (π / y) * (y ^ 2) ^ (-s) *
          |(c : ℝ)| ^ (-(5/4 : ℝ)) :=
        Finset.sum_le_sum fun t _ => exc_term_le hn δ' hc hs hy t
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

lemma summable_abs_int_rpow54 : Summable fun c : ℤ => |(c : ℝ)| ^ (-(5/4 : ℝ)) :=
  Real.summable_abs_int_rpow (by norm_num)

lemma tsum_abs_int_rpow54_le : ∑' c : ℤ, |(c : ℝ)| ^ (-(5/4 : ℝ)) ≤ 10 := by
  have h := tsum_abs_int_rpow_le (s := 1/8) (by norm_num)
  have e : (-(1 + 2 * (1/8 : ℝ))) = -(5/4 : ℝ) := by norm_num
  rw [e] at h
  linarith

end RamanujanPetersson.EllW2


