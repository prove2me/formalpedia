-- Prove2me | Definitions.Def_MIPRE_Foundations_Cost_Growth
-- name    : MIPRE_Foundations_Cost_Growth
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:35:15.937337+00:00
-- url     : https://prove2.me/theorems/0fbc2cde-ec19-4b3c-a507-ccf59573bf40
-- title:
--   Polynomial versus exponential growth: two elementary bounds on bit length and polynomial evaluation
-- statement:
--   This bundle contains no definitions; it holds two lemmas about natural numbers, the arithmetic behind the threshold of the recursive compression argument. Let `Nat.size n` be the number of binary digits of $n$ (with `Nat.size 0 = 0`), and for a polynomial $Q$ over $\mathbb{N}$ (Mathlib's `Polynomial ℕ`) let $\deg Q$ be `Q.natDegree`, $Q_i$ the coefficient `Q.coeff i` and $Q(y)$ the evaluation `Q.eval y`.
--
--   `MIPRE.Cost.two_pow_size_le (n : ℕ) : 2 ^ Nat.size n ≤ 2 * n + 1`.
--
--   `MIPRE.Cost.polynomial_eval_le_sum_coeff_mul_pow (Q : Polynomial ℕ) {y : ℕ} (hy : 1 ≤ y)`: a polynomial over $\mathbb{N}$ is bounded by its coefficient sum times the top power,
--
--   $$Q(y) \;\le\; \Big(\sum_{i=0}^{\deg Q} Q_i\Big)\, y^{\deg Q} \qquad (y \ge 1).$$
--
--   The second bound is the step that turns "bounded by some polynomial" into a bound by a single monomial, which is how a polynomially bounded function is shown to fall under $2^n$, and under $n^\lambda$ for one exponent $\lambda$ and all $n \ge 2$, in the bundle on polynomially bounded functions; the first relates the bit length of $n$ to $n$ itself.
--
--   **Formalization Note**. The sum is over `Finset.range (Q.natDegree + 1)`. The hypothesis $1 \le y$ is needed because the proof bounds each $y^i$ with $i \le \deg Q$ by $y^{\deg Q}$. Both statements are over `ℕ`, with truncated subtraction playing no role. The module's threshold statement (for every polynomial $Q$ there is $K$ with $Q(x + \log n) \le n + 1$ whenever $n \ge 2^{K+1+x}$) and the auxiliary bound $A \sigma^D \le 2^\sigma$ are not part of this bundle.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Growth.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Growth.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime

/-!
# Polynomial versus exponential growth

The arithmetic behind the threshold of the recursive compression argument
(`planning/compression-track.md`, K3 step 4): for every polynomial `Q` over `ℕ` there is a
constant `K` such that `n ≥ 2 ^ (K + 1 + x)` forces `Q (x + log n) ≤ n + 1`
(`exists_threshold`). The proof is elementary: a polynomial is bounded by its coefficient
sum times the top power (`polynomial_eval_le_sum_coeff_mul_pow`), and `A · σ ^ D ≤ 2 ^ σ`
as soon as `σ ≥ A (D + 1) ^ (D + 1)` (`mul_pow_le_two_pow`).
-/

namespace MIPRE.Cost

open Polynomial

/-- `2 ^ size n ≤ 2n + 1`. -/
theorem two_pow_size_le (n : ℕ) : 2 ^ Nat.size n ≤ 2 * n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h : Nat.size n - 1 < Nat.size n := by
      have := Nat.size_pos.2 hn; omega
    have h2 : 2 ^ (Nat.size n - 1) ≤ n := Nat.lt_size.1 h
    have h3 : 2 ^ Nat.size n = 2 * 2 ^ (Nat.size n - 1) := by
      rw [← pow_succ']; congr 1; have := Nat.size_pos.2 hn; omega
    omega

/-- A polynomial over `ℕ` is bounded by its coefficient sum times the top power. -/
theorem polynomial_eval_le_sum_coeff_mul_pow (Q : Polynomial ℕ) {y : ℕ} (hy : 1 ≤ y) :
    Q.eval y ≤ (∑ i ∈ Finset.range (Q.natDegree + 1), Q.coeff i) * y ^ Q.natDegree := by
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  exact Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right hy (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))

end MIPRE.Cost


