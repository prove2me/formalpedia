-- Prove2me | Definitions.Def_KallMayerSLP_Bonferroni_binomialMoment
-- name    : KallMayerSLP_Bonferroni_binomialMoment
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:13:04.611089+00:00
-- url     : https://prove2.me/theorems/47741d4d-0b07-4189-a8a9-99945e9e5a91
-- title:
--   Binomial moment $S_k$ of a family of events
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space and $B_1,\dots,B_r$ events. For $1\le k\le r$ the **$k$-th binomial moment** is
--   $$
--   S_k=\sum_{1\le i_1<\dots<i_k\le r}\mathbb P(B_{i_1}\cap\dots\cap B_{i_k}),
--   $$
--   and $S_0=1$. The name comes from the identity $S_k=\mathbb E\binom{\nu}{k}$ for the number $\nu$ of events which occur.
--
--   **Formalization Note** The index set is the set of $k$-element subsets of `Fin r`. At $k=0$ the only subset is empty, the intersection is the whole space, and the sum is $\mathbb P(\Omega)=1$, so the book's separate convention $S_0=1$ needs no special case for a probability measure.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 4, §3.4, eq. (3.10), p.285 (PDF 294)

import Mathlib

open MeasureTheory

namespace KallMayerSLP.Bonferroni

/-- The `k`-th **binomial moment** of the events `B 0, …, B (r-1)`:
`S_k = ∑_{i₁ < ⋯ < i_k} ℙ(B_{i₁} ∩ ⋯ ∩ B_{i_k})`.

Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 4, eq. (3.10), p.285 (PDF 294).

**Formalization Note.** The book's index set `1 ≤ i₁ < ⋯ < i_k ≤ r` is the set of `k`-element
subsets of `Fin r`. The book sets `S₀ := 1` separately; here the single subset `∅` of size `0`
has the empty intersection `Set.univ`, so `binomialMoment μ B 0 = μ.real Set.univ`, which is `1`
for the probability measures of the book. For `k > r` the sum is empty, so the value is `0`;
the book does not use that range. -/
noncomputable def binomialMoment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {r : ℕ}
    (B : Fin r → Set Ω) (k : ℕ) : ℝ :=
  ∑ I ∈ Finset.powersetCard k (Finset.univ : Finset (Fin r)), μ.real (⋂ i ∈ I, B i)

end KallMayerSLP.Bonferroni


