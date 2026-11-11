-- Prove2me | Definitions.Def_EqualSubsetSum_Faster_Problem
-- name    : EqualSubsetSum_Faster_Problem
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T23:22:17.325202+00:00
-- url     : https://prove2.me/theorems/b05c3b21-a732-48ba-9d1b-e4057cf37bcc
-- title:
--   Equal-Subset-Sum: solutions, support, maximum bit length, correct guesses, input and output words, guess procedures (§1.1, §2.1, §3, §7.3)
-- statement:
--   An instance of **Equal-Subset-Sum** is a vector $x=(x_1,\dots,x_n)\in\mathbb Z^n$ of arbitrary integers ($n\ge 0$; any sign, zero allowed). For an integer vector $a$, its **weighted sum** (or *key*) is $a\cdot y=\sum_i a_i y_i$.
--
--   - A **solution** for weights $y$ is a vector $d\in\{-1,0,1\}^n$ with $d\ne 0$ and $d\cdot y=0$; its **support** is $\mathrm{supp}(d)=\{i: d_i\ne 0\}$.
--   - $m=\mathrm{maxBits}(x)=\max_i$ (number of binary digits of $|x_i|$), and $0$ when $n=0$.
--   - A guess $k\in\mathbb N$ is **correct** for $x$ if $x$ has a solution and the smallest support of a solution has size $n-k$.
--   - Algorithms are programs of the published log-cost randomized RAM (`SubsetSumPartialMatch_SubsetSum_RAM`). An instance is given as the input words $n, x_1,\dots,x_n$ (one machine word per integer); a procedure that also receives a guess gets $n, k, x_1,\dots,x_n$. The output words are $[0]$ (failure) or $1, d_1,\dots,d_n$; an output is **admissible** for $x$ if it is failure or $1,d_1,\dots,d_n$ with $d$ a solution for $x$.
--   - $\mathrm{failProb}(P,\text{input})$ is the probability, over a tape of independent fair bits, that $P$ halts with output $[0]$.
--   - $P$ is a **guess procedure** for a set $R$ of zero fractions with exponent $E$ if there are constants $C,K,c>0,C'$ such that for all $n\ge1$, $x\in\mathbb Z^n$ and $k<n$ with $k/n\in R$: on every tape $P$ halts with an admissible output, within
--   $$C\,(n+m+1)^K\,2^{\,n\,E(k/n)}$$
--   charged bit operations; and if $k$ is correct, $\mathrm{failProb}\le C'2^{-cn}$.
--
--   **Formalization Note.** Vectors are `Fin n → ℤ` (0-based indices); bit length is `Nat.size` of the absolute value; "correct guess" is written without natural-number subtraction.
-- source:
--   Cheshm Jahan, Keshavarz Hedayati, Safari, Shahrezaei, Faster Equal-Subset-Sum via Truncated Inclusion–Exclusion, STOC 2027 submission (manuscript, sha256 7ad8c8b2…61dacd1), p. 1, §1.1; p. 13, §2.1; p. 16, §3; p. 47, §7.3

import Mathlib
import Definitions.Def_SubsetSumPartialMatch_SubsetSum_RAM

namespace EqualSubsetSum.Faster

open SubsetSumPartialMatch.SubsetSum

/-! Cheshm Jahan, Keshavarz Hedayati, Safari, Shahrezaei, *Faster Equal-Subset-Sum via Truncated
Inclusion–Exclusion*, §1.1 (p. 1), §2.1 (p. 13), §3 (p. 16) and §7.3 (p. 47).

An instance is a vector `x : Fin n → ℤ` of arbitrary integers (any sign, zero allowed, `n = 0`
allowed). Algorithms run on the published log-cost randomized RAM
`SubsetSumPartialMatch.SubsetSum` (one integer per memory cell). -/

/-- The weighted sum `a · y = ∑ᵢ aᵢ yᵢ` of an integer vector `a` with respect to the weights `y`
(its *key* in §2.4). -/
def weightedSum {n : ℕ} (a y : Fin n → ℤ) : ℤ := ∑ i, a i * y i

/-- `d` is a *solution* for the weights `y`: a nonzero vector in `{-1, 0, 1}ⁿ` with `d · y = 0`
(§1.1, p. 1; §3, p. 16). -/
def IsSolution {n : ℕ} (y d : Fin n → ℤ) : Prop :=
  d ≠ 0 ∧ (∀ i, d i = -1 ∨ d i = 0 ∨ d i = 1) ∧ weightedSum d y = 0

/-- The support `supp(d) = {i : dᵢ ≠ 0}` (§2.1, p. 13). -/
def supp {n : ℕ} (d : Fin n → ℤ) : Finset (Fin n) := Finset.univ.filter fun i => d i ≠ 0

/-- `m`, the maximum bit length of an input integer: `max_i` of the number of binary digits of
`|xᵢ|` (`Nat.size`, so `0` has bit length `0`); `0` when `n = 0`. -/
def maxBits {n : ℕ} (x : Fin n → ℤ) : ℕ := Finset.univ.sup fun i => Nat.size (x i).natAbs

/-- The guess `k` is *correct* (§3, p. 16): `x` has a solution, and the smallest support of a
solution has size `n - k` (written without natural-number subtraction: some solution has
`|supp| + k = n`, and every solution has `|supp| + k ≥ n`). -/
def GuessCorrect {n : ℕ} (x : Fin n → ℤ) (k : ℕ) : Prop :=
  (∃ d, IsSolution x d ∧ (supp d).card + k = n) ∧
    ∀ d, IsSolution x d → n ≤ (supp d).card + k

/-- Input words of an Equal-Subset-Sum instance: the length `n`, then `x₁, …, xₙ`, one machine
word per integer. -/
def instanceWords {n : ℕ} (x : Fin n → ℤ) : List ℤ := (n : ℤ) :: List.ofFn x

/-- Input words of a procedure that also receives a guess `k` (Theorems 4.1, 6.1, Lemma 7.1):
`n`, `k`, then `x₁, …, xₙ`. -/
def guessWords {n : ℕ} (x : Fin n → ℤ) (k : ℕ) : List ℤ := (n : ℤ) :: (k : ℤ) :: List.ofFn x

/-- The output word that reports failure. -/
def failureWord : List ℤ := [0]

/-- An output is admissible for the instance `x`: either failure `[0]`, or `1` followed by the
entries of a vector `d` that is a solution for `x` (checked on the decoded vector). -/
def ValidOutput {n : ℕ} (x : Fin n → ℤ) (out : List ℤ) : Prop :=
  out = failureWord ∨ ∃ d : Fin n → ℤ, out = 1 :: List.ofFn d ∧ IsSolution x d

/-- The probability, over the random tape, that program `P` on `input` halts with output
`failureWord`. -/
noncomputable def failProb (P : Program) (input : List ℤ) : ENNReal :=
  tapeMeasure {ω | Outputs P ω input failureWord}

/-- `P` is a procedure for the guesses whose zero fraction `p = k/n` lies in `range`, with
exponent `E` (the shape of Theorems 4.1, 6.1 and of each row of Lemma 7.1). There are constants
`C`, `K`, `c > 0`, `C'`, fixed before the input, such that for every `n ≥ 1`, every
`x : Fin n → ℤ` and every guess `k ∈ {0, …, n-1}` with `k/n ∈ range`, on input words
`n, k, x₁, …, xₙ`:
* on every tape `P` halts with an admissible output (failure or a solution for `x`);
* on every tape `P` halts within `C (n + m + 1)^K 2^{n E(k/n)}` charged bit operations,
  where `m = maxBits x`;
* if the guess `k` is correct, `P` outputs failure with probability at most `C' 2^{-c n}`. -/
def IsGuessProcedure (P : Program) (range : Set ℝ) (E : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, ∃ K : ℕ, ∃ c C' : ℝ, 0 < c ∧
    ∀ (n : ℕ) (x : Fin n → ℤ) (k : ℕ), 0 < n → k < n → ((k : ℝ) / n) ∈ range →
      (∀ ω : ℕ → Bool, ∃ out, Outputs P ω (guessWords x k) out ∧ ValidOutput x out) ∧
      (∀ ω : ℕ → Bool, CostWithin P ω (guessWords x k)
          (C * ((n : ℝ) + maxBits x + 1) ^ K * (2 : ℝ) ^ ((n : ℝ) * E ((k : ℝ) / n)))) ∧
      (GuessCorrect x k →
          failProb P (guessWords x k) ≤ ENNReal.ofReal (C' * (2 : ℝ) ^ (-(c * n))))

end EqualSubsetSum.Faster


