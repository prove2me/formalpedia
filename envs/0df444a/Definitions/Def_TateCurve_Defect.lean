-- Prove2me | Definitions.Def_TateCurve_Defect
-- name    : TateCurve_Defect
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/2c439b1c-8057-5767-9844-00c07dadd5b6
-- title:
--   Cauchy products and defect coefficients for the Tate parametrisation
-- statement:
--   The module sets up, over a nontrivially normed field $K$, the convolution formalism for $q$-power series and then the coefficient sequences whose vanishing expresses the Weierstrass equation of the Tate parametrisation. `cauchyMul c d N` is the convolution $\sum_{k+l=N} c_k d_l$ over Mathlib's antidiagonal of $N$; its values at $0$ and $1$ are recorded, and for complete $K$ two analytic facts are proved: if $\sum_N \|c_N q^N\|$ and $\sum_N \|d_N q^N\|$ converge then $\bigl(\sum_N c_N q^N\bigr)\bigl(\sum_N d_N q^N\bigr) = \sum_N (c\star d)_N q^N$ and $\sum_N \|(c\star d)_N q^N\|$ converges; and, with $0 \le C$, $\|c_N\| \le B C^N$ for all $N$ and $\|q\| C < 1$, the series $\sum_N \|c_N q^N\|$ converges by geometric comparison.
--
--   For $K$ in addition ultrametric, four coefficient sequences are defined. `xCoeffFull u` has constant term $\mathrm{xfun}(u) = u/(1-u)^2$ and $N$-th term, $N \ge 1$, the divisor sum $\sum_{d \mid N} d\,(u^d + u^{-d} - 2)$; `yCoeffFull u` has constant term $\mathrm{yfun}(u) = u^2/(1-u)^3$ and $N$-th term $\sum_{d \mid N}\bigl(\binom{d}{2}(u^d - u^{-d}) - d\,u^{-d} + d\bigr)$. The sequences `a₄Coeff` and `a₆Coeff` vanish at $0$ and are, at $N \ge 1$, the images in $K$ of $-\sum_{d \mid N} 5d^3$ and $-\sum_{d \mid N} b(d)$ with $b(n) = (5n^3 + 7n^5)/12$. The accompanying bounds are $\|\mathrm{xCoeff}\,u\,N\|, \|\mathrm{yCoeff}\,u\,N\| \le \mathrm{growthBound}(u)^N$ with $\mathrm{growthBound}(u) = \max(\|u\|, \|u^{-1}\|, 1)$, hence $\|\mathrm{xCoeffFull}\,u\,N\|, \|\mathrm{yCoeffFull}\,u\,N\| \le \mathrm{seriesBound}(u)\,\mathrm{growthBound}(u)^N$ for $\mathrm{seriesBound}(u) = \max(\|\mathrm{xfun}(u)\|, \|\mathrm{yfun}(u)\|, 1) \ge 1$, and $\|\mathtt{a₄Coeff}\,N\|, \|\mathtt{a₆Coeff}\,N\| \le 1$, the last because integers have norm at most $1$ in an ultrametric field.
--
--   Finally, for complete ultrametric $K$, $\mathtt{defectCoeff}\,u\,N$ is
--   $$(Q\star Q)_N + (P\star Q)_N - \bigl((P\star(P\star P))_N + (A_4 \star P)_N + (A_6)_N\bigr),$$
--   where $P = \mathtt{xCoeffFull}\,u$, $Q = \mathtt{yCoeffFull}\,u$, $A_4 = \mathtt{a₄Coeff}$, $A_6 = \mathtt{a₆Coeff}$: the $N$-th coefficient of the difference between the two sides of $Y^2 + XY = X^3 + a_4 X + a_6$ for the $q$-expansions of the Tate parametrisation.
--
--   **Relation to Mathlib.** `cauchyMul` is the project's convolution of coefficient sequences, used with Mathlib's summable-norm antidiagonal product theorems; Mathlib has no Tate curve or Tate parametrisation, so the coefficient sequences and the defect sequence are the project's own.
--
--   **Where it is used.** These coefficient sequences are the combinatorial input to the construction of the Tate parametrisation over a complete non-archimedean field: vanishing of `defectCoeff` in each degree is what identifies the $q$-expansions of $X$ and $Y$ as a point on the Tate curve $y^2 + xy = x^3 + a_4(q)x + a_6(q)$. The resulting parametrisation supplies the local description at primes of multiplicative reduction used in the study of the Galois representations attached to the Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_TateCurve_Defect.lean

import Definitions.Def_TateCurve_PointSeries
import Definitions.Def_TateCurve_Tails
import Mathlib.Analysis.Normed.Ring.InfiniteSum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped NNReal
open IsUltrametricDist Filter

namespace TateCurve

section CauchyProduct

variable {K : Type*} [NontriviallyNormedField K] {q : K}

noncomputable def cauchyMul (c d : ℕ → K) (N : ℕ) : K :=
  ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal N, c kl.1 * d kl.2

@[simp] theorem cauchyMul_zero (c d : ℕ → K) : cauchyMul c d 0 = c 0 * d 0 := by
  simp [cauchyMul]

theorem cauchyMul_one (c d : ℕ → K) : cauchyMul c d 1 = c 0 * d 1 + c 1 * d 0 := by
  rw [cauchyMul, Finset.Nat.antidiagonal_succ, Finset.sum_cons, Finset.Nat.antidiagonal_zero,
    Finset.sum_map, Finset.sum_singleton]
  rfl

private theorem antidiagonal_sum_mul_pow (c d : ℕ → K) (N : ℕ) :
    ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal N, (c kl.1 * q ^ kl.1) * (d kl.2 * q ^ kl.2)
      = cauchyMul c d N * q ^ N := by
  rw [cauchyMul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  have hsum : kl.1 + kl.2 = N := Finset.HasAntidiagonal.mem_antidiagonal.mp hkl
  rw [← hsum, pow_add]
  ring

theorem qSeries_mul {c d : ℕ → K} [CompleteSpace K]
    (hc : Summable fun N => ‖c N * q ^ N‖) (hd : Summable fun N => ‖d N * q ^ N‖) :
    (∑' N : ℕ, c N * q ^ N) * (∑' N : ℕ, d N * q ^ N)
      = ∑' N : ℕ, cauchyMul c d N * q ^ N := by
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hc hd]
  exact tsum_congr fun N => antidiagonal_sum_mul_pow c d N

theorem summable_norm_cauchyMul {c d : ℕ → K}
    (hc : Summable fun N => ‖c N * q ^ N‖) (hd : Summable fun N => ‖d N * q ^ N‖) :
    Summable fun N => ‖cauchyMul c d N * q ^ N‖ := by
  have h := summable_norm_sum_mul_antidiagonal_of_summable_norm hc hd
  refine h.congr fun N => ?_
  rw [antidiagonal_sum_mul_pow]

theorem summable_norm_qSeries {c : ℕ → K} {B C : ℝ} (hC0 : 0 ≤ C)
    (hb : ∀ N, ‖c N‖ ≤ B * C ^ N) (hqC : ‖q‖ * C < 1) :
    Summable fun N => ‖c N * q ^ N‖ := by
  have hCq0 : 0 ≤ C * ‖q‖ := mul_nonneg hC0 (norm_nonneg q)
  have hCq1 : C * ‖q‖ < 1 := by rwa [mul_comm] at hqC
  have hgeom : Summable fun N : ℕ => B * (C * ‖q‖) ^ N :=
    (summable_geometric_of_lt_one hCq0 hCq1).mul_left B
  refine Summable.of_nonneg_of_le (fun N => norm_nonneg _) (fun N => ?_) hgeom
  rw [norm_mul, norm_pow]
  calc ‖c N‖ * ‖q‖ ^ N ≤ (B * C ^ N) * ‖q‖ ^ N :=
        mul_le_mul_of_nonneg_right (hb N) (pow_nonneg (norm_nonneg q) N)
    _ = B * (C * ‖q‖) ^ N := by rw [mul_pow]; ring

end CauchyProduct

section Coefficients

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

noncomputable def xCoeffFull (u : K) : ℕ → K
  | 0 => xfun u
  | (N + 1) => xCoeff u (N + 1)

@[simp] theorem xCoeffFull_zero (u : K) : xCoeffFull u 0 = xfun u := rfl

@[simp] theorem xCoeffFull_succ (u : K) (N : ℕ) : xCoeffFull u (N + 1) = xCoeff u (N + 1) := rfl

noncomputable def yCoeffFull (u : K) : ℕ → K
  | 0 => yfun u
  | (N + 1) => yCoeff u (N + 1)

@[simp] theorem yCoeffFull_zero (u : K) : yCoeffFull u 0 = yfun u := rfl

@[simp] theorem yCoeffFull_succ (u : K) (N : ℕ) : yCoeffFull u (N + 1) = yCoeff u (N + 1) := rfl

noncomputable def a₄Coeff : ℕ → K
  | 0 => 0
  | (N + 1) => -(∑ d ∈ (N + 1).divisors, ((5 * d ^ 3 : ℕ) : K))

@[simp] theorem a₄Coeff_zero : a₄Coeff (K := K) 0 = 0 := rfl

@[simp] theorem a₄Coeff_succ (N : ℕ) :
    a₄Coeff (K := K) (N + 1) = -(∑ d ∈ (N + 1).divisors, ((5 * d ^ 3 : ℕ) : K)) := rfl

noncomputable def a₆Coeff : ℕ → K
  | 0 => 0
  | (N + 1) => -(∑ d ∈ (N + 1).divisors, ((b d : ℕ) : K))

@[simp] theorem a₆Coeff_zero : a₆Coeff (K := K) 0 = 0 := rfl

@[simp] theorem a₆Coeff_succ (N : ℕ) :
    a₆Coeff (K := K) (N + 1) = -(∑ d ∈ (N + 1).divisors, ((b d : ℕ) : K)) := rfl

theorem norm_xCoeff_le (u : K) (N : ℕ) : ‖xCoeff u N‖ ≤ growthBound u ^ N := by
  rw [xCoeff]
  refine norm_sum_le_of_forall_le_of_nonneg (pow_nonneg (growthBound_nonneg u) N)
    (fun d hd => ?_)
  exact (norm_xDivTerm_le u d).trans
    (pow_le_pow_right₀ (one_le_growthBound u) (Nat.divisor_le hd))

theorem norm_yCoeff_le (u : K) (N : ℕ) : ‖yCoeff u N‖ ≤ growthBound u ^ N := by
  rw [yCoeff]
  refine norm_sum_le_of_forall_le_of_nonneg (pow_nonneg (growthBound_nonneg u) N)
    (fun d hd => ?_)
  exact (norm_yDivTerm_le u d).trans
    (pow_le_pow_right₀ (one_le_growthBound u) (Nat.divisor_le hd))

noncomputable def seriesBound (u : K) : ℝ := max (max ‖xfun u‖ ‖yfun u‖) 1

theorem one_le_seriesBound (u : K) : 1 ≤ seriesBound u := le_max_right _ _

theorem seriesBound_nonneg (u : K) : 0 ≤ seriesBound u :=
  zero_le_one.trans (one_le_seriesBound u)

theorem norm_xCoeffFull_le (u : K) (N : ℕ) :
    ‖xCoeffFull u N‖ ≤ seriesBound u * growthBound u ^ N := by
  cases N with
  | zero =>
      simp only [xCoeffFull_zero, pow_zero, mul_one]
      exact (le_max_left _ _).trans (le_max_left _ _)
  | succ n =>
      rw [xCoeffFull_succ]
      calc ‖xCoeff u (n + 1)‖ ≤ growthBound u ^ (n + 1) := norm_xCoeff_le u (n + 1)
        _ = 1 * growthBound u ^ (n + 1) := (one_mul _).symm
        _ ≤ seriesBound u * growthBound u ^ (n + 1) :=
            mul_le_mul_of_nonneg_right (one_le_seriesBound u)
              (pow_nonneg (growthBound_nonneg u) _)

theorem norm_yCoeffFull_le (u : K) (N : ℕ) :
    ‖yCoeffFull u N‖ ≤ seriesBound u * growthBound u ^ N := by
  cases N with
  | zero =>
      simp only [yCoeffFull_zero, pow_zero, mul_one]
      exact (le_max_right _ _).trans (le_max_left _ _)
  | succ n =>
      rw [yCoeffFull_succ]
      calc ‖yCoeff u (n + 1)‖ ≤ growthBound u ^ (n + 1) := norm_yCoeff_le u (n + 1)
        _ = 1 * growthBound u ^ (n + 1) := (one_mul _).symm
        _ ≤ seriesBound u * growthBound u ^ (n + 1) :=
            mul_le_mul_of_nonneg_right (one_le_seriesBound u)
              (pow_nonneg (growthBound_nonneg u) _)

theorem norm_a₄Coeff_le (N : ℕ) : ‖a₄Coeff (K := K) N‖ ≤ 1 := by
  cases N with
  | zero => simp
  | succ n =>
      rw [a₄Coeff_succ, norm_neg]
      exact norm_sum_le_of_forall_le_of_nonneg zero_le_one
        (fun d _ => IsUltrametricDist.norm_natCast_le_one K _)

theorem norm_a₆Coeff_le (N : ℕ) : ‖a₆Coeff (K := K) N‖ ≤ 1 := by
  cases N with
  | zero => simp
  | succ n =>
      rw [a₆Coeff_succ, norm_neg]
      exact norm_sum_le_of_forall_le_of_nonneg zero_le_one
        (fun d _ => IsUltrametricDist.norm_natCast_le_one K _)

end Coefficients

section Defect

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q u : K}

noncomputable def defectCoeff (u : K) (N : ℕ) : K :=
  cauchyMul (yCoeffFull u) (yCoeffFull u) N + cauchyMul (xCoeffFull u) (yCoeffFull u) N
    - (cauchyMul (xCoeffFull u) (cauchyMul (xCoeffFull u) (xCoeffFull u)) N
        + cauchyMul a₄Coeff (xCoeffFull u) N + a₆Coeff N)

end Defect

end TateCurve


