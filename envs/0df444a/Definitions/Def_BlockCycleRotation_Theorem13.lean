-- Prove2me | Definitions.Def_BlockCycleRotation_Theorem13
-- name    : BlockCycleRotation_Theorem13
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-09-05T09:49:18.48873+00:00
-- url     : https://prove2.me/theorems/5927c1b7-bceb-487d-9bdc-9e8ac191fe75
-- title:
--   Theorem13: The decomposition $G_1 + G_2 + G_3$
-- statement:
--   Defines the three parts into which §4 splits the restricted quadruple sum: the main term $G_1$, the rounding term $G_2$ and the oscillating term $G_3$, together with the coefficients and cut-offs of the inner sums.
--
--   ---
--
--   **The comments in this code predate a citation correction.** They were written against an earlier, incorrect numbering of the source paper; published code is immutable, so they cannot be edited. In this bundle: *Lemma 17* means **Lemma 19**; *Theorem 13* means **Theorem 14**. The numbering used in this description, and in the repository at github.com/dbenbenn/block-cycle-rotation, follows arXiv:2601.00979v1 and is correct.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem13.lean

-- Generated from BlockCycleRotation/Theorem13.lean by skeleton subtraction (Def bundle).
import Definitions.Def_BlockCycleRotation_TripleSum
import Mathlib
/-
# Theorem 13

The paper's main theorem: the average cost of the block cycle scheme is

```
avgCost n = D·n + O(n^{1/2+ε}),     D = 1 + 4C ≈ 1.85.
```

`Constant.lean` proves Lemma 17 — the `G₁` main term is `C·n²·∑_{d∣n} 1/d²` up
to `O(n^{3/2+ε})` — and `TripleSum.lean` proves the error layers bounding
`G₂ + G₃`.  What is still missing, and is supplied here, is the link between
the two: the estimate at a single coprime pair, which says that the actual inner
sum over `b'` differs from the `G₁` summand by at most the `G₂ + G₃` bound.
Everything after that is aggregation.
-/


namespace BlockCycleRotation

open Finset

/-! ## The estimate at a single pair

Fix `d`, `m = n/d`, and a coprime pair `a > a' ≥ 1` in the bulk, meaning
`d·a·(a+a') ≤ m`.  By `gtBound_bulk_eq` the cut-off is then `K+1` with
`K = ⌊(m-1)/(a+a')⌋`, and `K ≤ V ≤ K+1` for the paper's real cut-off
`V = m/(a+a')`.  Three proved facts combine:

* `inner_gt_estimate` — removing the congruence condition costs
  `(|A| + |B|·K)(1 + log a)`;
* `main_term_vs_sum` — replacing the discrete sum by `A·V + B·V²/2` costs
  `|A| + |B|·V`;
* `main_term_substitute` — the result is `d·m/(a+a') + m²·cTerm(a,a')`, the
  summand of `G₁`.

Since `|A| = d·a + m/a` and `|B|·V ≤ m/a`, both costs are at most
`W = d·a + 2m/a`, and the total is at most `2·W·(1 + log m)`. -/



/-! ## The paper's `G₁ + G₂ + G₃`

The paper splits the inner sum at a coprime pair into three named pieces:
`G₁` is the closed form `(1/a)(A·Y + B·Y²/2)` at the *real* cut-off `Y`, `G₂`
is the rounding error against the discrete sum, and `G₃` is what the
non-trivial characters contribute.  `bulk_pair_estimate` bounds `G₂ + G₃`
together; the three are named here so that Lemmas 18 and 19 can be stated
individually. -/

/-- The paper's `A = d·a + m/a`. -/
noncomputable def aCoeff (m d a : ℕ) : ℝ := ((d * a : ℕ) : ℝ) + (m : ℝ) / (a : ℝ)

/-- The paper's `B = -a'/a`. -/
noncomputable def bCoeff (a a' : ℕ) : ℝ := -(a' : ℝ) / (a : ℝ)

/-- The paper's cut-off `Y = m/(a+a')`, which on the bulk branch is the active
one of the two. -/
noncomputable def yCut (m a a' : ℕ) : ℝ := (m : ℝ) / ((a : ℝ) + (a' : ℝ))

/-- The discrete sum `∑_{1 ≤ b' < Y} (A + B·b')`. -/
noncomputable def innerLinear (m d a a' : ℕ) : ℝ :=
  ∑ b' ∈ Finset.Ico 1 (gtBound m d a a'), (aCoeff m d a + bCoeff a a' * (b' : ℝ))

/-- The actual inner sum over the arithmetic progression. -/
noncomputable def innerActual (m d a a' : ℕ) : ℝ :=
  ((∑ b' ∈ (Finset.Ico 1 (gtBound m d a a')).filter (fun b' => a ∣ (m - a' * b')),
      (d * a + (m - a' * b') / a) : ℕ) : ℝ)

/-- **`G₁`**, the main term at the real cut-off. -/
noncomputable def G1term (m d a a' : ℕ) : ℝ :=
  (1 / (a : ℝ)) * (aCoeff m d a * yCut m a a' + bCoeff a a' * yCut m a a' ^ 2 / 2)

/-- **`G₂`**, the rounding error. -/
noncomputable def G2term (m d a a' : ℕ) : ℝ :=
  (1 / (a : ℝ)) * innerLinear m d a a' - G1term m d a a'

/-- **`G₃`**, the contribution of the non-trivial characters. -/
noncomputable def G3term (m d a a' : ℕ) : ℝ :=
  innerActual m d a a' - (1 / (a : ℝ)) * innerLinear m d a a'









/-! ## Aggregating over the pairs

The bulk part of the triple sum decomposes by pairs, and `bulk_pair_estimate`
applies to each.  The complementary part is bounded by `small_part_le`. -/





/-! ## Summing over the divisors

Both per-divisor errors are dominated by the quantity `outer_layer` and
`error_isBigO` handle, namely `d(n)·(√n+1)·3n(1+log n)`: the middle layer
directly, and the small part because `(2d+2)(2m) = 4dm + 4m ≤ 8n`. -/

/-- The aggregate error bound of `outer_layer`. -/
noncomputable def Err (n : ℕ) : ℝ :=
  (n.divisors.card : ℝ) * (((Nat.sqrt n : ℝ) + 1) * (3 * (n : ℝ) * (1 + Real.log n)))



/-- **Lemma 18.**  `G₂(n) = O(n^{3/2+ε})`. -/
noncomputable def G2sum (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, ∑ p ∈ (coprimePairs (n / d)).filter
    (fun p => d * p.1 * (p.1 + p.2) ≤ n / d), G2term (n / d) d p.1 p.2

/-- **Lemma 19.**  `G₃(n) = O(n^{3/2+ε})`. -/
noncomputable def G3sum (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, ∑ p ∈ (coprimePairs (n / d)).filter
    (fun p => d * p.1 * (p.1 + p.2) ≤ n / d), G3term (n / d) d p.1 p.2













/-! ## `Q(n)` in closed form

Adding the diagonal (bounded by `sum_diag_isBigO`) and Lemma 17. -/



/-! ## Möbius inversion

`∑_{d ∣ n} d² = n²·∑_{e ∣ n} 1/e²`, so Möbius inversion turns the main term of
`Q` into `C·n²` when it is summed against `μ`. -/





/-! ## The remainder sums

Equation (heilbron) turns `R(n)` into `∑_{k} remSum(n,k)` at the cost of
`∑_k gcd(n,k) ≤ n·d(n) = O(n^{1+ε})`. -/



/-! ## The symmetry `M(n,k) = M(n,n-k)`

The algorithm's cost at shift `k` depends only on `min k (n-k)`, so summing
over all `0 ≤ k < n` double-counts every shift `1 ≤ j` with `2j ≤ n`, except
the midpoint `j = n/2` when `n` is even. -/











/-! ## Theorem 13 -/



end BlockCycleRotation


