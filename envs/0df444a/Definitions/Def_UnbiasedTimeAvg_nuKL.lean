-- Prove2me | Definitions.Def_UnbiasedTimeAvg_nuKL
-- name    : UnbiasedTimeAvg_nuKL
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:18:37.10914+00:00
-- url     : https://prove2.me/theorems/6682ad53-25cb-4104-b10f-07ad302172e3
-- title:
--   The averages $\nu_{k,l}$
-- statement:
--   For $k\ge1$, $b'=b'(k)\le k/2$ and $l\ge0$,
--   $$\nu_{k,l}:=\frac{\sum_{i=b'+k(2^l-1)}^{k2^l-1}\nu(i)}{k-b'},$$
--   the average of $\nu$ over the $k-b'$ indices $b'+k(2^l-1)\le i\le k2^l-1$. It bounds the second moment of the level increments (Lemma F.2).
--
--   **Formalization Note** The index range is the interval $[b'+k(2^l-1),\,k2^l)$ of naturals; the denominator is computed in $\mathbb R$.
-- source:
--   N. Kahalé, Unbiased time-average estimators for Markov chains, arXiv:2209.09581v1 (20 Sep 2022), Appendix F, p.27 (definition of ν_{k,l})

import Mathlib

namespace UnbiasedTimeAvg

/-- **The averages `ν_{k,l}`.** Kahalé, arXiv:2209.09581v1, Appendix F, p.27: "For `l ≥ 0`, let
`ν_{k,l} := (Σ_{i=b′(k)+k(2^l−1)}^{k2^l−1} ν(i))/(k − b′(k))`."

`nuKL ν b' k l` is the average of `ν(i)` over the `k − b′` indices
`b′ + k(2^l − 1) ≤ i ≤ k2^l − 1`.

**Formalization Note.** The index range is `Finset.Ico (b' + k * (2^l - 1)) (k * 2^l)`; `2^l - 1`
never truncates since `2^l ≥ 1`. The denominator `k − b′` is taken in `ℝ`. -/
noncomputable def nuKL (ν : ℕ → ℝ) (b' k l : ℕ) : ℝ :=
  (∑ i ∈ Finset.Ico (b' + k * (2 ^ l - 1)) (k * 2 ^ l), ν i) / ((k : ℝ) - b')

end UnbiasedTimeAvg


