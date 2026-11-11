-- Prove2me | Definitions.Def_ArbLindbladLearn_lowerMedian
-- name    : ArbLindbladLearn_lowerMedian
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:21:22.547719+00:00
-- url     : https://prove2.me/theorems/5a4c3da8-9b60-4cee-96ec-04d986608785
-- title:
--   Median of batch means
-- statement:
--   The median of $K$ reals is taken as the lower median (the entry of index $\lfloor(K-1)/2\rfloor$ of the sorted list). `batchMedian X K m` is the median of the $K$ batch means of $X_0,\dots,X_{Km-1}$, batch $k$ holding the indices $km,\dots,km+m-1$.
--
--   **Formalization Note** For even $K$ the paper does not fix which middle value is the median; any value between the two middle ones obeys Fact 2.7's bound.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Fact 2.7, p.17; Algorithm 2 lines 18–19, p.31

import Mathlib

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn

/-- The (lower) median of `K` reals: the entry of index `⌊(K − 1)/2⌋` of the sorted list
(Fact 2.7, Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.17).

**Formalization Note** For even `K` the paper does not fix which middle value is "the median"; the
lower one is used. (Any value between the two middle ones obeys the same bound.) -/
def lowerMedian (K : ℕ) (v : Fin K → ℝ) : ℝ :=
  ((List.ofFn v).insertionSort (· ≤ ·)).getD ((K - 1) / 2) 0

/-- The median of the `K` batch means of `X₀, …, X_{Km−1}`, batch `k` holding the indices
`km, …, km + m − 1` (Fact 2.7, p.17; Algorithm 2 lines 18–19, p.31). -/
def batchMedian {Ω : Type*} (X : ℕ → Ω → ℝ) (K m : ℕ) (ω : Ω) : ℝ :=
  lowerMedian K fun k => (∑ i ∈ Finset.range m, X (k * m + i) ω) / m

end ArbLindbladLearn


