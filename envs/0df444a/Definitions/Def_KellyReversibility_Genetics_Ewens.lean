-- Prove2me | Definitions.Def_KellyReversibility_Genetics_Ewens
-- name    : KellyReversibility_Genetics_Ewens
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T02:50:38.184138+00:00
-- url     : https://prove2.me/theorems/eb0f3439-d88d-4ad3-bc90-55fd2a01a9c8
-- title:
--   Eq. (7.6) — the Ewens distribution $\pi_n$ on descriptions of a population of size $n$
-- statement:
--   Consider a set of $n$ individuals, each carrying an allelic type. Its **description** is $\mathbf M=(M_1,M_2,\dots,M_n)$, where $M_i$ is the number of allelic types represented by exactly $i$ individuals of the set. Every description satisfies
--
--   $$\sum_{i=1}^{n} i\,M_i = n. \qquad (7.3)$$
--
--   For a real parameter $\nu$, the **Ewens distribution** (the equilibrium distribution of the infinite alleles model) assigns to a description $\mathbf M$ satisfying (7.3) the number
--
--   $$\pi_n(\mathbf M)=\binom{\nu+n-1}{n}^{-1}\prod_{i=1}^{n}\Big(\frac{\nu}{i}\Big)^{M_i}\frac{1}{M_i!}, \qquad (7.6)$$
--
--   where, for real $x$, $\binom{x}{k}=x(x-1)\cdots(x-k+1)/k!$ is the generalized binomial coefficient; in particular $\binom{\nu+n-1}{n}=\nu(\nu+1)\cdots(\nu+n-1)/n!$.
--
--   This is the distribution whose consistency under sampling (Theorem 7.1) is the goal of the mission; it is also used in Corollary 7.5.
--
--   **Formalization Note** A description of $n$ individuals is encoded as a partition $p$ of $n$ (`Nat.Partition n`) whose parts are the sizes of the allelic classes, so $M_i$ is the multiplicity `p.parts.count i` of the part $i$; condition (7.3) is then automatic and every description arises from exactly one partition. The generalized binomial coefficient is the published definition `AppliedComb.GenFun.binomReal`. The product runs over $i=1,\dots,n$ (`Finset.Icc 1 n`). The definition is stated for every real $\nu$; the theorems assume $\nu>0$, as in the book.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 146, Eq. (7.6) with Eq. (7.3)

import Mathlib
import Definitions.Def_AppliedComb_GenFun_binomReal

namespace KellyReversibility.Genetics

open AppliedComb.GenFun

/-- Kelly (1979), §7.1, p. 146, Eq. (7.6), with (7.3). A *description* of a set of `n`
individuals is `M = (M₁, M₂, …, Mₙ)`, `Mᵢ` the number of alleles represented by exactly `i`
individuals, so that `∑ᵢ i Mᵢ = n` (7.3). It is encoded as a partition `p` of `n` whose parts
are the class sizes: `Mᵢ = p.parts.count i`.

The Ewens distribution (7.6), for a real parameter `ν`:
`π_n(M) = C(ν + n − 1, n)⁻¹ ∏_{i=1}^{n} (ν / i)^{Mᵢ} (1 / Mᵢ!)`,
where `C(x, k) = x (x − 1) ⋯ (x − k + 1) / k!` is the generalized binomial coefficient
`binomReal` for real `x`. -/
noncomputable def ewens (ν : ℝ) (n : ℕ) (p : Nat.Partition n) : ℝ :=
  (binomReal (ν + (n : ℝ) - 1) n)⁻¹ *
    ∏ i ∈ Finset.Icc 1 n,
      (ν / (i : ℝ)) ^ (p.parts.count i) / ((p.parts.count i).factorial : ℝ)

end KellyReversibility.Genetics


