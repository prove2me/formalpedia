-- Prove2me | Definitions.Def_RPLib_S3_MatchingC
-- name    : RPLib_S3_MatchingC
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:20:01.551118+00:00
-- url     : https://prove2.me/theorems/b0653fd1-db79-4b90-bdf5-cdb3c403ec84
-- title:
--   Weight-two Ramanujan-Petersson library: `charSum`, the scalar term, and the size of the hyperbolic inner sums
-- statement:
--   `charSum`, the scalar term, and the size of the hyperbolic inner sums.
--
--   * `charSum_congr`: `charSum L z ε` depends only on `z mod L`; `abs_charSum_le`: `|charSum L z ε| ≤ L + 1`.
--   * `abs_scalarG1_le`: `|scalarG1 M k n δ| ≤ (k-1)/12 ψ(M) (M+1) √n^{k-2}`.
--   * `hypX` (the inner sum of `hypG1` at a divisor `e`), `hypG1_eq`, `abs_hypX_le`: `|hypX| ≤ #div(M) M (M+1)`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7; M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211

import Mathlib
import Definitions.Def_RPLib_S3_Statements

/-!
# S3-Matching, part C: `charSum`, the scalar term, and the size of the hyperbolic inner sums

* `charSum_congr`: `charSum L z ε` depends only on `z mod L`; `abs_charSum_le`: `|charSum L z ε| ≤ L + 1`.
* `abs_scalarG1_le`: `|scalarG1 M k n δ| ≤ (k-1)/12 ψ(M) (M+1) √n^{k-2}`.
* `hypX` (the inner sum of `hypG1` at a divisor `e`), `hypG1_eq`, `abs_hypX_le`: `|hypX| ≤ #div(M) M (M+1)`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.S3.Match

/-- `charSum L z ε` depends only on `z mod L`. -/
lemma charSum_congr {L : ℕ} {z z' : ℤ} (h : z ≡ z' [ZMOD L]) (ε : ℤ) :
    charSum L z ε = charSum L z' ε := by
  have hz : (z : ZMod L) = (z' : ZMod L) := (ZMod.intCast_eq_intCast_iff _ _ _).2 h
  have hg : Int.gcd z L = Int.gcd z' L := by
    obtain ⟨c, hc⟩ := Int.ModEq.dvd h
    have : z' = z + L * c := by linarith
    rw [this, Int.gcd_add_mul_left_left]
  unfold charSum
  rw [hz, hg]

lemma abs_charSum_le (L : ℕ) (z : ℤ) {ε : ℤ} (hε : |ε| ≤ 1) : |charSum L z ε| ≤ L + 1 := by
  have hT : ((Nat.totient L : ℕ) : ℚ) ≤ L := by exact_mod_cast Nat.totient_le L
  have hT0 : (0 : ℚ) ≤ (Nat.totient L : ℕ) := Nat.cast_nonneg _
  have hL0 : (0 : ℚ) ≤ L := Nat.cast_nonneg _
  have hε' : |(ε : ℚ)| ≤ 1 := by exact_mod_cast hε
  obtain ⟨hε1, hε2⟩ := abs_le.1 hε'
  unfold charSum
  split_ifs <;> rw [abs_le] <;> constructor <;> nlinarith

lemma abs_neg_one_pow_le (k : ℕ) : |((-1 : ℤ) ^ k)| ≤ 1 := by
  rw [abs_pow, abs_neg, abs_one, one_pow]

lemma dedekindPsi_nonneg (M : ℕ) : 0 ≤ dedekindPsi M := by
  unfold dedekindPsi
  exact mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg fun l _ => by positivity)

/-- The scalar term, with the integer square root. -/
lemma abs_scalarG1_le_nat (M k n : ℕ) (hk : 1 ≤ k) (δ : ZMod M) :
    |scalarG1 M k n δ| ≤ ((k : ℚ) - 1) / 12 * dedekindPsi M * (M + 1) * (Nat.sqrt n : ℚ) ^ (k - 2) := by
  have hk1 : (0 : ℚ) ≤ (k : ℚ) - 1 := by
    have : (1 : ℚ) ≤ k := by exact_mod_cast hk
    linarith
  have hψ := dedekindPsi_nonneg M
  have hs : (0 : ℚ) ≤ (Nat.sqrt n : ℚ) ^ (k - 2) := by positivity
  unfold scalarG1
  split_ifs with hsq
  · rw [abs_mul, abs_of_nonneg (by positivity)]
    have hc := abs_charSum_le M ((δ.val : ℤ) * Nat.sqrt n) (abs_neg_one_pow_le k)
    calc ((k : ℚ) - 1) / 12 * dedekindPsi M * (Nat.sqrt n : ℚ) ^ (k - 2) *
          |charSum M ((δ.val : ℤ) * Nat.sqrt n) ((-1) ^ k)|
        ≤ ((k : ℚ) - 1) / 12 * dedekindPsi M * (Nat.sqrt n : ℚ) ^ (k - 2) * (M + 1) := by gcongr
      _ = _ := by ring
  · rw [abs_zero]; positivity

/-- **Scalar bound.** `|A1(n)| ≤ (k-1)/12 ψ(M) (M+1) √n^{k-2}`. -/
lemma abs_scalarG1_le (M k n : ℕ) (hk : 1 ≤ k) (δ : ZMod M) :
    |(scalarG1 M k n δ : ℝ)| ≤
      ((k : ℝ) - 1) / 12 * (dedekindPsi M : ℝ) * (M + 1) * Real.sqrt n ^ (k - 2) := by
  have h := abs_scalarG1_le_nat M k n hk δ
  have h' : |(scalarG1 M k n δ : ℝ)| ≤
      ((k : ℝ) - 1) / 12 * (dedekindPsi M : ℝ) * (M + 1) * (Nat.sqrt n : ℝ) ^ (k - 2) := by
    have := (Rat.cast_le (K := ℝ)).2 h
    push_cast at this
    exact this
  refine h'.trans ?_
  have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hψ : (0 : ℝ) ≤ (dedekindPsi M : ℝ) := by exact_mod_cast dedekindPsi_nonneg M
  gcongr
  exact Real.nat_sqrt_le_real_sqrt

/-- The inner sum of `hypG1` at the divisor `e`. -/
def hypX (M k n : ℕ) (δ : ZMod M) (e : ℕ) : ℚ :=
  ∑ τ ∈ M.divisors, (Nat.totient (Nat.gcd τ (M / τ)) : ℚ) / (Nat.gcd τ (M / τ) : ℚ) *
    ∑ x ∈ (Finset.range M).filter
        (fun x : ℕ => (x : ℤ) ≡ (e : ℤ) [ZMOD (τ : ℤ)] ∧ (x : ℤ) ≡ ((n / e : ℕ) : ℤ) [ZMOD ((M / τ : ℕ) : ℤ)]),
      charSum (M / Nat.gcd τ (M / τ)) ((δ.val : ℤ) * x) ((-1) ^ k)

lemma hypG1_eq (M k n : ℕ) (δ : ZMod M) :
    hypG1 M k n δ = -(1 / 2) * ∑ e ∈ n.divisors,
      ((if e ≤ n / e then e else n / e : ℕ) : ℚ) ^ (k - 1) * hypX M k n δ e := rfl

/-- The constant bounding every `hypX`. -/
def hypB (M : ℕ) : ℚ := M.divisors.card * (M * (M + 1))

lemma abs_hypX_le (M k n : ℕ) (δ : ZMod M) (e : ℕ) : |hypX M k n δ e| ≤ hypB M := by
  unfold hypX hypB
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun τ _ => ?_
  set g := Nat.gcd τ (M / τ)
  have hg : |(Nat.totient g : ℚ) / (g : ℚ)| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    rcases Nat.eq_zero_or_pos g with h0 | hpos
    · rw [h0]; simp
    · rw [div_le_one (by exact_mod_cast hpos)]
      exact_mod_cast Nat.totient_le g
  rw [abs_mul]
  have hM0 : (0 : ℚ) ≤ M * (M + 1) := by positivity
  have hin : |∑ x ∈ (Finset.range M).filter
        (fun x : ℕ => (x : ℤ) ≡ (e : ℤ) [ZMOD (τ : ℤ)] ∧ (x : ℤ) ≡ ((n / e : ℕ) : ℤ) [ZMOD ((M / τ : ℕ) : ℤ)]),
      charSum (M / g) ((δ.val : ℤ) * x) ((-1) ^ k)| ≤ M * (M + 1) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum (g := fun _ => ((M : ℚ) + 1)) fun x _ => ?_).trans ?_
    · refine (abs_charSum_le _ _ (abs_neg_one_pow_le k)).trans ?_
      have : ((M / g : ℕ) : ℚ) ≤ M := by exact_mod_cast Nat.div_le_self M g
      linarith
    · rw [Finset.sum_const, nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_range M).le
  calc |(Nat.totient g : ℚ) / (g : ℚ)| * |_| ≤ 1 * (M * (M + 1)) :=
        mul_le_mul hg hin (abs_nonneg _) zero_le_one
    _ = M * (M + 1) := one_mul _

end RamanujanPetersson.S3.Match


