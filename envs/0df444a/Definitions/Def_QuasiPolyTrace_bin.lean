-- Prove2me | Definitions.Def_QuasiPolyTrace_bin
-- name    : QuasiPolyTrace_bin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:30:53.208021+00:00
-- url     : https://prove2.me/theorems/4a9d14e4-2eb9-4639-86be-029f12dac870
-- title:
--   Binomial probability $\mathrm{bin}(n,j,p)$
-- statement:
--   For a natural number $n$, an integer $j$ and a real $p$, the **binomial probability** is
--
--   $$
--   \mathrm{bin}(n,j,p)=\binom{n}{j}p^{j}(1-p)^{n-j}\quad\text{if }0\le j\le n,\qquad \mathrm{bin}(n,j,p)=0\ \text{otherwise}.
--   $$
--
--   For $p\in[0,1]$ it is the probability of exactly $j$ heads in $n$ independent flips of a $p$-biased coin, i.e. the probability mass function of $\mathrm{Bin}(n,p)$ at $j$.
--
--   The paper uses $\mathrm{bin}(R,\cdot,p)$ both as the law of how many of the first $R$ bits of a string survive the deletion channel (Lemma 5, Corollary 6) and as a convolution kernel ("binomial blurring", Lemmas 14 and 16, Corollary 34).
--
--   **Formalization Note** $j$ ranges over the integers so that $\mathrm{bin}(n,\cdot,p)$ is a sequence on $\mathbb Z$. No condition on $p$ is built in; every statement using it assumes $p\in[0,1]$ or a sub-interval.
-- source:
--   Burudgunte, Valiant, Wang, Quasipolynomial Trace Reconstruction, manuscript of November 2, 2026 (later version of arXiv:2607.04073; sha256 9ecb6d18…), §2, p.6 (definition of bin(n, j, p))

import Mathlib

namespace QuasiPolyTrace

/-- **The binomial probability `bin(n, j, p)`.** Burudgunte, Valiant, Wang, *Quasipolynomial Trace Reconstruction*, manuscript of November 2, 2026
(later version of arXiv:2607.04073; sha256 9ecb6d18…), §2, p.6:
"`bin(n, j, p) := (n choose j) p^j (1 − p)^{n−j}`, though taking values 0 when `j ∉ {0, …, n}`".

The probability of exactly `j` heads in `n` flips of a `p`-biased coin; zero outside `0 ≤ j ≤ n`.

**Formalization Note.** `j` is an integer so that `bin` can be used as a sequence on `ℤ` (the paper
convolves sequences on `ℤ` with it). No condition on `p` is built in; every statement using `bin`
assumes `p ∈ [0, 1]` (or a sub-interval) itself. -/
noncomputable def bin (n : ℕ) (j : ℤ) (p : ℝ) : ℝ :=
  if 0 ≤ j ∧ j ≤ n then (n.choose j.toNat : ℝ) * p ^ j.toNat * (1 - p) ^ (n - j.toNat) else 0

end QuasiPolyTrace


