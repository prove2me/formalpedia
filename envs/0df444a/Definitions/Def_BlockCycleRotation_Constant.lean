-- Prove2me | Definitions.Def_BlockCycleRotation_Constant
-- name    : BlockCycleRotation_Constant
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-09-05T09:49:20.968903+00:00
-- url     : https://prove2.me/theorems/4411bb50-dd87-4f9f-bd4c-ae0c243bad5d
-- title:
--   Constant: The constant $C$ of equation (const-c)
-- statement:
--   Defines the summand $c(a,a')$ of equation (const-c) — equal to $\frac{2a+a'}{2a^2(a+a')^2}$ on coprime pairs $a > a' \ge 1$ and zero elsewhere — the constant $C = \sum c(a,a')$, and $D = 1 + 4C$, the constant appearing in **Theorem 14**. The bundle also carries the aggregate main term $G_1(n)$, a double sum over divisors $d \mid n$ and bulk coprime pairs, and the per-divisor error $\mathrm{Eterm}(n,d)$ used to bound it.
--
--   ---
--
--   **The comments in this code predate a citation correction.** They were written against an earlier, incorrect numbering of the source paper; published code is immutable, so they cannot be edited. In this bundle: *Lemma 17* means **Lemma 19**; *Theorem 10* means **Theorem 9**; *Theorem 13* means **Theorem 14**. The numbering used in this description, and in the repository at github.com/dbenbenn/block-cycle-rotation, follows arXiv:2601.00979v1 and is correct.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Constant.lean

-- Generated from BlockCycleRotation/Constant.lean by skeleton subtraction (Def bundle).
import Definitions.Def_BlockCycleRotation_TripleSum
import Mathlib
/-
# The constant `C`

Equation (const-c) of Blomer--Bux defines

```
C = ∑_{a > a' ≥ 1, gcd(a,a') = 1}  (2a + a') / (2 a² (a+a')²),
```

an explicit double series over coprime pairs.  Its value is `≈ 0.2125`, and
`D = 1 + 4C ≈ 1.85`.

Note this is a plain convergent series: no integral is involved.  (Theorem 10 of
the paper separately identifies the limit as `∫₀¹ ρ`, but that representation
plays no part in computing `C`.)  Remark 21 rewrites `C` using Euler's
`ζ(2,1) = ζ(3)`; that rewriting is optional.

Convergence is by comparison: for `a' < a` the term is at most `3/(2a³)`, and
summing over the fewer than `a` admissible `a'` leaves `3/(2a²)`.
-/


namespace BlockCycleRotation

/-- The summand of equation (const-c), extended by zero. -/
noncomputable def cTerm (p : ℕ × ℕ) : ℝ :=
  if 1 ≤ p.2 ∧ p.2 < p.1 ∧ Nat.gcd p.1 p.2 = 1 then
    (2 * (p.1 : ℝ) + (p.2 : ℝ)) / (2 * (p.1 : ℝ) ^ 2 * ((p.1 : ℝ) + (p.2 : ℝ)) ^ 2)
  else 0







/-! ## Convergence -/









/-- **The constant `C`** of equation (const-c). -/
noncomputable def cConst : ℝ := ∑' p : ℕ × ℕ, cTerm p



/-- **The constant `D = 1 + 4C`** of Theorem A and Theorem 13.

Numerically, truncating the series for `C` at `a ≤ 20000` gives
`C ≈ 0.21138` and `D ≈ 1.8455`, consistent with the paper's `D ≈ 1.85`.
(The tail is `O(1/N)`, so the truncation converges slowly.) -/
noncomputable def dConst : ℝ := 1 + 4 * cConst

/-! ## The summand of Lemma 17

The bulk part of `G₁` in the paper's proof of Lemma 17 has summand

```
n²/(d²a²(a+a'))  -  n²a'/(2a²d²(a+a')²)  =  (n²/d²) · (2a + a')/(2a²(a+a')²),
```

so the coefficient is exactly `cTerm`.  This is the algebraic identity that
makes `C` appear. -/









/-! ## The tail bound

`∑_{a > N} 1/a² ≤ 1/N`, by telescoping against `1/(a-1) - 1/a`.  Mathlib has the
summability of the `p`-series but no tail estimate, so this is proved here. -/












/-! ## The substitution of Lemma 17

Substituting the paper's coefficients `A = d·a + m/a`, `B = -a'/a` and the real
bound `V = m/(a+a')` into the main term `(1/a)(A·V + B·V²/2)` gives

```
d·m/(a+a')  +  m² · cTerm(a, a').
```

The first term is lower order; the second is what sums to `m²·C`.  This is the
step where the constant appears. -/



/-! ## Assembling the main term

After substitution the main term splits into a lower-order part
`d·m·∑ 1/(a+a')` and `m²` times a partial sum of the series for `C`.  The latter
is squeezed between `C - 3/(2N)` and `C`. -/







/-! ## Reconciling the index shapes

`bulk_sum_close` is stated over the double sum `∑_{a ≤ N} ∑_{a' < a}`, while
`G1_split` produces a sum over a `Finset (ℕ × ℕ)` of bulk pairs.  The first is a
sum over `{(a,a') : a ≤ N, a' < a}`, whose nonzero terms all lie in the second. -/







/-! ## The sum over divisors

For `d ∣ n` the natural-number quotient `n/d` is exact, so `m = n/d` gives
`m² = n²/d²` and the main terms sum to `C·n²·∑_{d∣n} 1/d²` — the shape of
Lemma 17.  The errors, of size `O((n/d)^{3/2}√d) = O(n^{3/2}/d)`, sum to
`O(n^{3/2}·d(n))`. -/







/-! ## Lemma 17

At a single divisor, the main term is `m²·C` up to the lower-order part and the
truncation error.  Summing over `d ∣ n` then gives the statement of the paper's
Lemma 17. -/



/-- **`G₁`**, the main term of the triple sum, in its substituted form.

By `main_term_substitute` the summand here is the paper's
`(1/a)(A·V + B·V²/2)` at `A = d·a + m/a`, `B = -a'/a`, `V = m/(a+a')`. -/
noncomputable def G1 (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors,
    ∑ p ∈ (coprimePairs (n / d)).filter (fun p => d * p.1 * (p.1 + p.2) ≤ n / d),
      ((d : ℝ) * ((n / d : ℕ) : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ))
        + ((n / d : ℕ) : ℝ) ^ 2 * cTerm p)



/-! ## Instantiating the error

When `2d ≤ m` the cut-off `N = √(m/(2d))` is positive and `lemma17_local`
applies.  Otherwise `m < 2d ≤ 6d`, and the bulk set is empty — `a > a' ≥ 1`
forces `a ≥ 2` and `a + a' ≥ 3`, so `d·a·(a+a') ≥ 6d > m` — leaving the error
`m²·C`. -/



/-- **The per-divisor error of Lemma 17.** -/
noncomputable def Eterm (n d : ℕ) : ℝ :=
  if 2 * d ≤ n / d then
    ((Nat.sqrt ((n / d - 1) / d) : ℝ) + 1) * ((d : ℝ) * ((n / d : ℕ) : ℝ))
      + ((n / d : ℕ) : ℝ) ^ 2 * (3 / (2 * ((Nat.sqrt ((n / d) / (2 * d)) : ℕ) : ℝ)))
  else ((n / d : ℕ) : ℝ) ^ 2 * cConst





/-! ## Bounding the total error

The truncation term is `m²·3/(2N)` with `N = √(m/(2d))`, so a lower bound on `N`
is needed.  The natural-number square root satisfies `q ≤ 4·(√q)²` for `q ≥ 1`,
and `m < 4dq`, giving `m ≤ 16·d·N²` — equivalently `√m ≤ 4√d·N`, which turns
`m²/N` into `4·m^{3/2}·√d`. -/













end BlockCycleRotation


