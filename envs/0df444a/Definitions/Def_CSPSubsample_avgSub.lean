-- Prove2me | Definitions.Def_CSPSubsample_avgSub
-- name    : CSPSubsample_avgSub
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:13:57.420564+00:00
-- url     : https://prove2.me/theorems/0b9cc80c-34f6-4073-8b37-5a56bdd9533b
-- title:
--   Average over a uniformly random $N$-subset of $[n]$
-- statement:
--   For a function $F$ of subsets of $[n]$, the expectation of $F(U)$ when $U$ is a **uniformly random subset of $[n]$ of size $N$** (sampling without replacement; the law $\mu$ of §5) is
--   $$
--   \mathbb E_{U\sim\mu}[F(U)]=\binom{n}{N}^{-1}\sum_{U\subseteq[n],\ |U|=N}F(U).
--   $$
--   This is the expectation in the structure lemma and in the subsampling theorem.
--
--   **Formalization Note** For $N>n$ there is no such subset and Lean returns $0$; the mission's statements only use $N\le n$.
-- source:
--   Bernasconi, Castiglioni, Celli, Farina, Malavolta, A Subsampling Theorem for Constraint Satisfaction Problems with Large Arity, arXiv:2608.00203 (PDF sha256 fd9ae01113266fee273c46c14c8a1a39f36a958dba3fc276cd74bf4c3daff445), §3, Lemma 3.2 and Theorem 3.3, pp.6–7 (PDF pp.8–9); law µ, p.12 (PDF p.14)

import Mathlib

set_option autoImplicit false

namespace CSPSubsample

/-- The expectation `E_{U ∼ µ}[F(U)]` over a **uniformly random subset `U ⊆ [n]` of size `N`**
(sampling without replacement; the law `µ` of arXiv:2608.00203 (PDF sha256 fd9ae011…), p.12 =
PDF p.14, used in Lemma 3.2 and Theorem 3.3, pp.6–7):
`avgSub n N F = (1 / C(n, N)) ∑_{U ⊆ [n], |U| = N} F(U)`.

**Formalization Note** A finite average over `Finset.powersetCard N univ`. For `N > n` there is
no such subset and Lean returns `0/0 = 0`; the statements of the mission only use `N ≤ n`
(Theorem 3.3's hypothesis on `n` implies it in every nontrivial case). -/
noncomputable def avgSub (n N : ℕ) (F : Finset (Fin n) → ℝ) : ℝ :=
  (∑ U ∈ (Finset.univ : Finset (Fin n)).powersetCard N, F U) / (n.choose N : ℝ)

end CSPSubsample


