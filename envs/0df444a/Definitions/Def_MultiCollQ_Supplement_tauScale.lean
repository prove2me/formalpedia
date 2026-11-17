-- Prove2me | Definitions.Def_MultiCollQ_Supplement_tauScale
-- name    : MultiCollQ_Supplement_tauScale
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:58:26.548606+00:00
-- url     : https://prove2.me/theorems/8fd0cdec-c8bc-4e22-9cef-f53f849e166c
-- title:
--   Eligible bucket count $n_*$ and query scale $\tau_{r,\ell}(N,n_*)$ of (4.25)
-- statement:
--   For an exact type $\lambda=(1^{n_1},\dots,k^{n_k})$ and a collision order $r\le k$, the number of **eligible buckets** (buckets, i.e. equality classes, of size at least $r$) is
--
--   $$
--   n_*=\sum_{i=r}^{k}n_i .
--   $$
--
--   The **query scale** is
--
--   $$
--   \tau_{r,\ell}(N,n_*)=\frac{\sqrt N\,\ell^{1/(2-2^{1-r})}}{n_*^{1/(2^{r+1}-2)}} .
--   $$
--
--   It is the scale of the function-query lower bound (Theorem 4.4), of the exponential database tail (Theorem 4.6) and of the matching upper bound (Theorem 4.8). For the pure type $(k^n)$, $n_*=n=N/k$ and it reduces, up to constants depending on $k$, to $\ell^{2^{r-1}/(2^r-1)}N^{(2^{r-1}-1)/(2^r-1)}$.
--
--   **Formalization Note** The type is a function $n:\mathbb N\to\mathbb N$; powers are real powers.
-- source:
--   Peng, Hou, Dong, Quantum multi-collision lower bounds for arbitrary bounded types, manuscript (Oct. 2026; STOC 2027 submission, sha256 e20a0870b16226a4c1b2ff8ccbc19ad9605f91268e96586242ff551b9f17fdf1), §4.1, (4.1), p.34 and §4.4, (4.25), p.41

import Mathlib

namespace MultiCollQ.Supplement

/-- The number of eligible buckets `n_* = Σ_{i=r}^{k} n_i` of an exact type
`λ = (1^{n_1}, …, k^{n_k})`, i.e. the number of buckets (equality classes) of size at least `r`
(Peng, Hou, Dong, *Quantum multi-collision lower bounds for arbitrary bounded types*, manuscript
(Oct. 2026), §4.1, (4.1), p.34).

**Formalization Note.** The type is the function `n : ℕ → ℕ`, read at `r ≤ i ≤ k`. -/
def nStar (k r : ℕ) (n : ℕ → ℕ) : ℕ := ∑ i ∈ Finset.Icc r k, n i

/-- The query scale `τ_{r,ℓ}(N, n_*) = √N ℓ^{1/(2−2^{1−r})} / n_*^{1/(2^{r+1}−2)}` of (4.25) (Peng,
Hou, Dong, manuscript (Oct. 2026), §4.4, (4.25), p.41; also the scale of (4.15), p.38, and (4.31),
p.44).

**Formalization Note.** Real powers (`Real.rpow`); `2^{1−r}` is `(2 : ℝ) ^ (1 − r)` with real
exponent and `2^{r+1}` a natural power. Every use has `ℓ ≥ 1` and `n_* ≥ 1`. -/
noncomputable def tauScale (r ℓ N ns : ℕ) : ℝ :=
  Real.sqrt N * (ℓ : ℝ) ^ (1 / (2 - (2 : ℝ) ^ (1 - (r : ℝ)))) /
    (ns : ℝ) ^ (1 / ((2 : ℝ) ^ (r + 1) - 2))

end MultiCollQ.Supplement


