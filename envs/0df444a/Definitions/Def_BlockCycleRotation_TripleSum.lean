-- Prove2me | Definitions.Def_BlockCycleRotation_TripleSum
-- name    : BlockCycleRotation_TripleSum
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-09-05T09:42:23.507495+00:00
-- url     : https://prove2.me/theorems/cb8dc37b-72fc-4b35-873f-0f257a4f8bf9
-- title:
--   TripleSum: Quadruples, triples and the index sets of §4
-- statement:
--   Defines the index sets of §4: the quadruples $\mathcal{Q}(n)$ attached to shifts by Heilbronn's correspondence, the coprime pairs and triples they reduce to, and the bulk cut-off separating the range where progression estimates apply.
--
--   ---
--
--   **The comments in this code predate a citation correction.** They were written against an earlier, incorrect numbering of the source paper; published code is immutable, so they cannot be edited. In this bundle: *Lemma 17* means **Lemma 19**; *Theorem 13* means **Theorem 14**. The numbering used in this description, and in the repository at github.com/dbenbenn/block-cycle-rotation, follows arXiv:2601.00979v1 and is correct.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/TripleSum.lean

-- Generated from BlockCycleRotation/TripleSum.lean by skeleton subtraction (Def bundle).
import Definitions.Def_BlockCycleRotation_Continuant
import Mathlib
/-
# The triple sum of section 4

After (eq. heilbron), Blomer--Bux rewrite the lattice point count as a triple
sum.  Ordering the pairs `(a, a')` by `d = gcd(a, a')`, which necessarily
divides `n`, and eliminating `b` via `b = n/(d·a) - a'·b'/a`, they obtain

```
Q(n) = ∑_{d ∣ n} ∑_{a > a' ≥ 1, gcd(a,a') = 1} ∑_{b'} ( n/(d·a) − a'·b'/a + d·a )
         + O(n^{1+ε})
```

where `b'` runs over `1 ≤ b' < U` subject to `n/d ≡ a'·b' (mod a)`, with
`U = min( n/(d(a+a')), (n/d − d·a²)/a' )`.

The innermost sum is a linear function summed over an arithmetic progression —
exactly the shape estimated in `Progression.lean`.  This file records that: the
general estimate applies to the paper's summand verbatim, with

  `A = n/(d·a) + d·a`  and  `B = −a'/a`.

What remains for Theorem 13 is the two outer layers — the sum over `a > a' ≥ 1`
coprime, and the Möbius-inverted sum over `d ∣ n` — together with collecting the
resulting pieces `G₁ + G₂ + G₃` into `O(n^{3/2+ε})`.  Every ingredient those need
is proved: this estimate, `exists_card_divisors_le`, and Mathlib's Möbius
inversion.
-/


namespace BlockCycleRotation

open Real



/-! ## Equation (invquant)

The paper discards the `∑ gcd(n,k)` term of (eq. heilbron) as `O(n^{1+ε})`.
That bound is `∑_{k} gcd(n,k) ≤ n · d(n)`, which the divisor bound turns into
`O(n^{1+ε})`. -/







/-! ## Eliminating `b`

The paper solves `n = a·b + a'·b'` for `b`, turning the quadruples into triples
`(a, a', b')`.  The condition `b > b'` becomes `(a + a')·b' < n`, and `b` being
an integer becomes `a ∣ n - a'·b'` — the congruence `n ≡ a'b' (mod a)`. -/

/-- The triples `(a, a', b')` of the triple sum. -/
def triples (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter
    (fun t => 1 ≤ t.2.1 ∧ t.2.1 < t.1 ∧ 1 ≤ t.2.2 ∧ (t.1 + t.2.1) * t.2.2 < n
      ∧ t.1 ∣ (n - t.2.1 * t.2.2))





/-! ## The triple sum

Combining the divisor layer `Q(n) = ∑_{d ∣ n} R(n/d)` with the `b`-elimination
applied to each `R(n/d)` gives the paper's triple sum: over divisors `d ∣ n`,
over coprime pairs `a > a' ≥ 1`, and over `b'` in an arithmetic progression. -/

/-- The triples with `gcd(a,a') = 1`. -/
def coprimeTriples (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (triples n).filter (fun t => Nat.gcd t.1 t.2.1 = 1)







/-! ## The congruence is an arithmetic progression

The triple sum's divisibility condition `a ∣ m - a'·b'` is, because
`gcd(a,a') = 1`, a condition on `b'` modulo `a` — the shape the estimate of
`Progression.lean` requires.  This produces the residue `c` explicitly from
Bézout. -/





/-! ## Decomposing the triple sum by pairs

The triples split as a pair `(a, a')` together with `b'` ranging over an initial
segment cut by `(a + a')·b' < m` and filtered by the divisibility condition.
After this the innermost sum is literally the arithmetic-progression sum of
`inner_sum_nat_eq`. -/

/-- The bound on `b'` for a given pair. -/
def bBound (m a a' : ℕ) : ℕ := (m - 1) / (a + a') + 1



/-- The coprime pairs `a > a' ≥ 1`. -/
def coprimePairs (m : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (m + 1)) ×ˢ (Finset.range (m + 1))).filter
    (fun p => 1 ≤ p.2 ∧ p.2 < p.1 ∧ Nat.gcd p.1 p.2 = 1)







/-! ## Symmetrisation

Following the paper: `Q(n) = ½ ∑ (b + a)`, and the involution swapping the two
halves pairs the quadruples with `b > a` against those with `b < a`, leaving the
diagonal `a = b`.  So

  `Q(n) = ∑_{b > a} (a + b) + ∑_{a = b} a`,

exactly (the diagonal term is what the paper discards as `O(n^{1+ε})`).  The
restriction `b > a` is what will bound `a` by about `√n` in the estimates. -/









/-! ## The diagonal is `O(n^{1+ε})`

On the diagonal `a = b` we have `n = a² + a'b'`, so `a ≤ √n` and `a'` divides
`n - a²`; the quadruple is determined by `(a, a')`.  Counting gives
`√n · ∑_{a ≤ √n} d(n - a²)`, which the divisor bound makes `O(n^{1+ε})`. -/







/-! ## Carrying `b > a` through the classification

Classifying the symmetrised sum by `d = gcd(a,a')` turns the restriction
`b > a` into the paper's `b > d·a`, since `a = d·a₁`. -/

/-- The coprime quadruples of `m` with `b > d·a`. -/
def quadGT (m d : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (quadruplesAll m).filter (fun q => d * q.1 < q.2.1)





/-- The triples with the paper's condition `m - a'·b' > d·a²`, which is `b > d·a`
after eliminating `b`. -/
def gtTriples (m d : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (coprimeTriples m).filter (fun t => d * t.1 * t.1 < m - t.2.1 * t.2.2)









/-! ## The innermost range

For a fixed pair `(a, a')` the conditions `(a+a')b' < m` and `m - a'b' > d·a²`
are two upper bounds on `b'`, so the range is an initial segment cut at the
paper's `U = min( m/(a+a'), (m - d·a²)/a' )`. -/

/-- The paper's `U`. -/
def gtBound (m d a a' : ℕ) : ℕ :=
  min ((m - 1) / (a + a') + 1) ((m - d * a * a - 1) / a' + 1)







/-! ## The estimate, over the reals

`Progression.lean` states the progression estimate over `ℂ`.  The triple sum is
real, so we record the real form. -/







/-! ## The middle layer

Summing the per-pair error over `a' < a` coprime and then over `a ≤ √(m/d)`.
The grouping matters: the `a` values of `a'` cancel the `1/a` in the
coefficient `2m/a`, leaving `d·a² + 2m ≤ 3m` per value of `a`. -/











/-! ## The outer layer

Summing the middle-layer bound over the divisors `d ∣ n`, with `m = n/d`.
Bounding each factor by its value at `d = 1` costs only a factor `d(n)`, which
the divisor bound absorbs. -/





/-! ## The bulk / small split

Lemma 17 splits `G₁` according to which of the two bounds defining `U` is
active.  Comparing `m/(a+a')` with `(m - d·a²)/a'`, the first is the smaller
exactly when `d·a·(a+a') ≤ m`.  On that branch — the *bulk* — the constraint
`(a+a')·b' < m` implies the other one, so the range of `b'` is a single initial
segment.  The complementary branch is the *small* part. -/









/-! ## Counting an arithmetic progression

The divisibility condition `a ∣ m - a'·b'` puts `b'` in a single residue class
modulo `a`, so within an interval of length `U` there are at most `U/a + 1` of
them.  This factor of `1/a` is what makes the small part `O(m^{3/2})`: without
it a crude count would be too large by exactly that factor. -/





/-! ## The small-part bound

On the small branch `d·a² > m/2`, so `m/a² < 2d` and the residue class meets the
range in at most `2d+2` points; each summand is at most `2·(m/a)`.  Summing over
`a' < a` the factor `a` cancels the `1/a`, leaving `O(d·m)` per value of `a`, and
`a` ranges over at most `√(m/d)+1` values. -/





/-! ## Towards the main term

The main term per pair is `(1/a)·∑_{1 ≤ b' < U} (A + B·b')` with the paper's
coefficients.  Evaluating that sum in closed form and substituting
`U = m/(a+a')`, `A = d·a + m/a`, `B = -a'/a` gives

```
d·m/(a+a')  +  m²·[ 1/(a²(a+a')) - a'/(2a²(a+a')²) ]  =  d·m/(a+a')  +  m²·cTerm(a,a'),
```

by `cTerm_summand_eq`.  Summing over all coprime pairs gives `m²·C`, and over
`d ∣ n` with `m = n/d` gives `C·n²·∑_{d∣n} 1/d²` — Lemma 17. -/









/-! ## The floor analysis

The main term is evaluated at the natural-number bound `U`, but the paper's
computation substitutes the real value `V = m/(a+a')`.  The two differ, and the
discrepancy must be bounded.  It has an exact algebraic form: for the quadratic
`f(x) = A(x-1) + B(x-1)x/2`,

```
f(U) - f(V) = (U - V) · (A + (B/2)(U + V - 1)),
```

so with `|U - V| ≤ 1` — which is exactly the floor property — the discrepancy is
controlled by the coefficients. -/









/-! ## The lower-order part

After substitution the main term carries a term `d·m/(a+a')`.  Summing it over
`a' < a` gives at most `d·m` per value of `a` — the `a` choices of `a'` cancel
the `1/a` again — and `a` ranges over at most `√((m-1)/d)+1` values, so the
whole thing is `O(m^{3/2}√d)`, the same order as the other errors. -/



/-! ## Sanity checks -/

-- The `b`-elimination, checked numerically.
-- The triple sum, checked numerically.
-- The fully decomposed triple sum, checked numerically.
-- The symmetrisation, checked numerically.
-- The small-part bound, checked numerically.
-- The restricted triple sum, checked numerically.
-- `∑ gcd(n,k) ≤ n · d(n)`.

end BlockCycleRotation


