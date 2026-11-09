-- Prove2me | Definitions.Def_SubsetSumPartialMatch_SubsetSum_Reduction
-- name    : SubsetSumPartialMatch_SubsetSum_Reduction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:52.163081+00:00
-- url     : https://prove2.me/theorems/739375ef-0460-4447-9e70-47461f456f7d
-- title:
--   The objects of the reduction: lists, keys, layers, cost and filter
-- statement:
--   Fix $n$ with $6\mid n$ and an instance $(z,\tau)$. The **prefix** is the first $n/3$ coordinates, and $N_{\mathrm{sum}}$ is the number of distinct subset sums of $z_1,\dots,z_{n/3}$. For $a,b\in\mathbb Z^n$, the **left key** of $a$ is $a\cdot z$ and the **right key** of $b$ is $\tau-b\cdot z$.
--
--   A **layer** is a density $s\in\{0,3/n,\dots,1/2\}$, written $s=3w/n$ with $w=sn/3\in\{0,\dots,n/6\}$. For $l,r$ let $\ell$ be the largest even integer not greater than
--   $$\frac n6\bigl(1+h(s)+s-2(l-r)(1-s)\bigr).$$
--   The conceptual lists are
--   $$\mathcal A=\{0,1\}^{n/3}\times\{0,1\}^{\ell}\times0^{2n/3-\ell},\qquad \mathcal B=T_{n/3,s}\times0^{\ell}\times\{0,1\}^{2n/3-\ell},$$
--   where $T_{m,s}\subseteq\{-1,0,1\}^m$ is the set of vectors with exactly $sm$ nonzero entries. With $n'=(2-2s)n/3$,
--   $$\mathrm{cost}(N_L,N_R)=2^{(l+\varepsilon)n'}N_L+2^{(r+\varepsilon)n'}N_R.$$
--
--   For a solution $c$, a **correct key** of a layer is the left key of some $a\in\mathcal A$ with $c-a\in\mathcal B$.
--
--   The hash modulus $p$ is the smallest power of two with $p>2N_{\mathrm{sum}}(|\tau|+\sum_i|z_i|+1)$ and the window is $q=p/2^{\lfloor\log_2N_{\mathrm{sum}}\rfloor}$. An element of $\mathcal A$ or $\mathcal B$ **survives** if its key does; the surviving elements are the **records**. Equal keys of distinct assignments give distinct records.
--
--   **Formalization Note** The list $\mathcal A$ has the literal block form above, as a finite set of integer vectors. Records are written for the machine coordinate by coordinate, preceded by the two list lengths. The record generator receives the instance, $w$, $\ell$, $p$, $q$, $\alpha$, $\beta$ as input, and the matching stage receives the instance, $w$, $\ell$ and the records; the real numbers $l,r$ are not part of any input.
-- source:
--   Li & Ye, Subset Sum via Partial Match, STOC 2027 submission #24, preprint, source.pdf sha256 e5f396c346fb73c14219a019a35c9a16b1adc4b4b84978d3658736d31958ae5c, pp. 10–13, §2.2

import Mathlib
import Definitions.Def_SubsetSumPartialMatch_SubsetSum_Problem
import Definitions.Def_SubsetSumPartialMatch_SubsetSum_Entropy
import Definitions.Def_SubsetSumPartialMatch_SubsetSum_Hash

namespace SubsetSumPartialMatch.SubsetSum

/-- The dot product `a · z`. -/
def dot {n : ℕ} (a z : Fin n → ℤ) : ℤ := ∑ i, a i * z i

/-- The left key `a · z`. -/
def leftKey {n : ℕ} (z a : Fin n → ℤ) : ℤ := dot a z

/-- The right key `τ - b · z`. -/
def rightKey {n : ℕ} (z : Fin n → ℤ) (τ : ℤ) (b : Fin n → ℤ) : ℤ := τ - dot b z

/-- A binary vector viewed as an integer vector. -/
def boolVec {n : ℕ} (c : Fin n → Bool) : Fin n → ℤ := fun i => if c i then 1 else 0

/-- The set of distinct subset sums of the prefix `z_1, …, z_{n/3}`. -/
def prefixSums {n : ℕ} (z : Fin n → ℤ) : Finset ℤ :=
  (Finset.univ.filter fun i : Fin n => i.val < n / 3).powerset.image fun S => ∑ i ∈ S, z i

/-- `N_sum`: the number of distinct subset sums of the prefix. -/
def Nsum {n : ℕ} (z : Fin n → ℤ) : ℕ := (prefixSums z).card

/-- The support density `s = 3w/n` of a layer. As `w` runs over `0, …, n/6`, `s` runs over
`{0, 3/n, …, 1/2}`, and `w = sn/3` is the number of nonzero prefix entries of a right vector. -/
noncomputable def density (n w : ℕ) : ℝ := 3 * (w : ℝ) / n

/-- `ℓ`: the largest even integer not greater than
`(n/6) (1 + h(s) + s - 2 (l - r) (1 - s))`. -/
noncomputable def splitPoint (n : ℕ) (l r s : ℝ) : ℕ :=
  2 * ⌊(n : ℝ) / 6 * (1 + binEntropy s + s - 2 * (l - r) * (1 - s)) / 2⌋₊

/-- The conceptual left list `{0,1}^{n/3} × {0,1}^ℓ × 0^{2n/3-ℓ}`. -/
def leftList (n ℓ : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun i => if i.val < n / 3 + ℓ then {0, 1} else {0}

/-- The conceptual right list `T_{n/3,s} × 0^ℓ × {0,1}^{2n/3-ℓ}`, where `w = sn/3` is the exact
number of nonzero prefix entries. -/
def rightList (n ℓ w : ℕ) : Finset (Fin n → ℤ) :=
  (Fintype.piFinset fun i : Fin n =>
    if i.val < n / 3 then {-1, 0, 1} else if i.val < n / 3 + ℓ then {0} else {0, 1}).filter
    fun b => (Finset.univ.filter fun i : Fin n => i.val < n / 3 ∧ b i ≠ 0).card = w

/-- The length `n' = (2 - 2s) n / 3` of the padded partial match strings. -/
noncomputable def paddedLength (n : ℕ) (s : ℝ) : ℝ := (2 - 2 * s) * n / 3

/-- `cost(N_L, N_R) = 2^{(l+ε)n'} N_L + 2^{(r+ε)n'} N_R`. -/
noncomputable def pmCost (n : ℕ) (l r ε s NL NR : ℝ) : ℝ :=
  (2 : ℝ) ^ ((l + ε) * paddedLength n s) * NL + (2 : ℝ) ^ ((r + ε) * paddedLength n s) * NR

/-- The correct keys of the solution `c` in a layer: the left keys of the `a` in the left list with
`c - a` in the right list. -/
def correctKeys {n : ℕ} (z : Fin n → ℤ) (c : Fin n → Bool) (ℓ w : ℕ) : Finset ℤ :=
  ((leftList n ℓ).filter fun a => boolVec c - a ∈ rightList n ℓ w).image (leftKey z)

/-- The hash modulus `p`: the smallest power of two exceeding
`2 N_sum (|τ| + ∑_i |z_i| + 1)`. -/
def hashModulus {n : ℕ} (z : Fin n → ℤ) (τ : ℤ) : ℕ :=
  2 ^ (Nat.log 2 (2 * Nsum z * (τ.natAbs + ∑ i, (z i).natAbs + 1)) + 1)

/-- The filter size `q = p / 2^{⌊log₂ N_sum⌋}`. -/
def hashWindow {n : ℕ} (z : Fin n → ℤ) (τ : ℤ) : ℕ :=
  hashModulus z τ / 2 ^ Nat.log 2 (Nsum z)

/-- The left list of a layer filtered by `h_{α,β}`: its surviving records. -/
def survivingLeft {n : ℕ} (z : Fin n → ℤ) (τ : ℤ) (ℓ : ℕ) (α β : ℕ) : Set (Fin n → ℤ) :=
  {a | a ∈ leftList n ℓ ∧ Survives (hashModulus z τ) (hashWindow z τ) α β (leftKey z a)}

/-- The right list of a layer filtered by `h_{α,β}`: its surviving records. -/
def survivingRight {n : ℕ} (z : Fin n → ℤ) (τ : ℤ) (ℓ w : ℕ) (α β : ℕ) : Set (Fin n → ℤ) :=
  {b | b ∈ rightList n ℓ w ∧ Survives (hashModulus z τ) (hashWindow z τ) α β (rightKey z τ b)}

/-- The input of the record generator: the instance, then `w`, `ℓ`, `p`, `q`, `α`, `β`. -/
def filterWords {n : ℕ} (z : Fin n → ℤ) (τ : ℤ) (w ℓ α β : ℕ) : List ℤ :=
  instanceWords z τ ++
    [(w : ℤ), (ℓ : ℤ), (hashModulus z τ : ℤ), (hashWindow z τ : ℤ), (α : ℤ), (β : ℤ)]

/-- Records as machine words: the two list lengths, then the entries of the vectors. -/
def recordWords {n : ℕ} (LA LB : List (Fin n → ℤ)) : List ℤ :=
  (LA.length : ℤ) :: (LB.length : ℤ) ::
    (LA.flatMap fun a => List.ofFn a) ++ (LB.flatMap fun b => List.ofFn b)

/-- The input of the matching stage: the instance, then `w`, `ℓ`, then the surviving records. -/
def matchWords {n : ℕ} (z : Fin n → ℤ) (τ : ℤ) (w ℓ : ℕ) (LA LB : List (Fin n → ℤ)) : List ℤ :=
  instanceWords z τ ++ [(w : ℤ), (ℓ : ℤ)] ++ recordWords LA LB

/-- The pair `(a, b)` forms the solution `c`: the two keys agree and `a + b = c ∈ {0,1}^n`. -/
def PairFormsSolution {n : ℕ} (z : Fin n → ℤ) (τ : ℤ) (a b : Fin n → ℤ) (c : Fin n → Bool) :
    Prop :=
  leftKey z a = rightKey z τ b ∧ a + b = boolVec c

end SubsetSumPartialMatch.SubsetSum


