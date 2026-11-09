-- Prove2me | Definitions.Def_MinSumFPT_wSum
-- name    : MinSumFPT_wSum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:43.864451+00:00
-- url     : https://prove2.me/theorems/9d557406-883d-4d3f-8ca2-66a8116134f1
-- title:
--   Adaptive distance sampling: $d(q,m_q)$, $\Gamma_i$, $A_{i,M}$ and the weights of $P_{i,M}$
-- statement:
--   Let $M\subseteq A$ be a nonempty set of candidate core proxies. For a point $q$ write $d(q,m_q)=\min_{m\in M}d(q,m)$. For $i\in\{0,1,2,\dots\}$ let
--
--   $$
--   \Gamma_i=2^{-i}\sum_{q\in A}d(q,m_q),\qquad A_{i,M}=\{q\in A:\ d(q,m_q)\le\Gamma_i\},
--   $$
--
--   and let $P_{i,M}$ be the distribution on $A_{i,M}$ with $P_{i,M}[p]=d(p,m_p)/\sum_{q\in A_{i,M}}d(q,m_q)$. For $S\subseteq A$, $w(S)=\sum_{p\in S}d(p,m_p)$ is the weight of $S$, so that $P_{i,M}[S]=w(S\cap A_{i,M})/w(A_{i,M})$.
--
--   Algorithm 1 samples new candidate centers from $P_{i,M}$ for $i\le10\log(nk/\varepsilon)$; Lemmas 10 and 11 bound the probability that such a sample lies in the core of a largest uncovered cluster.
--
--   **Formalization Note** Probabilities under $P_{i,M}$ are stated through the weight $w$ in multiplied form: $P_i[X]\ge c$ is $w(X\cap A_i)\ge c\,w(A_i)$, and $P_i[X: Y]\ge c$ is $w(X\cap Y\cap A_i)\ge c\,w(Y\cap A_i)$. This agrees with the ratio whenever the denominator is positive.
-- source:
--   Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), §2.3, Adaptive Sampling, p.13

import Mathlib

namespace MinSumFPT

/-!
# The adaptive distance-sampling objects of §2.3

Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, *A Fixed Parameter Sublinear Time Approximation
Scheme for Metric Min-Sum Clustering*, arXiv:2610.15148 (held version of November 2, 2026, sha256
12e81235…), §2.3, "Adaptive Sampling", p.13: for a nonempty set M of candidate core proxies,
m_q = argmin_{m∈M} d(q, m), Γ_i = 2^{−i} ∑_{q∈A} d(q, m_q), A_{i,M} = {q ∈ A : d(q, m_q) ≤ Γ_i},
and the law P_{i,M}[p] = d(p, m_p)/∑_{q∈A_{i,M}} d(q, m_q) on A_{i,M}.

This module bundles `distToSet` (d(q, m_q)), `Gamma`, `levelSet` (A_{i,M}) and `wSum`.

**Formalization Note.** Only d(q, m_q) enters, so no arg min is chosen: `distToSet d M q` is
min_{m∈M} d(q, m) (M nonempty; the empty set gives the junk value of `Finset.inf'`'s absence, so
the definition takes the nonemptiness proof). P_{i,M} is not a measure here: P_i[X] ≥ c is stated as
`wSum (X ∩ A_i) ≥ c ⋅ wSum A_i`, and P_i[X : Y] ≥ c as `wSum (X ∩ Y ∩ A_i) ≥ c ⋅ wSum (Y ∩ A_i)`
(multiplied form; it agrees with the ratio whenever the denominator is positive). -/

/-- `d(q, m_q) = min_{m ∈ M} d(q, m)` for a nonempty `M`. -/
noncomputable def distToSet {n : ℕ} (d : Fin n → Fin n → ℝ) (M : Finset (Fin n))
    (hM : M.Nonempty) (q : Fin n) : ℝ :=
  M.inf' hM (d q)

/-- `Γ_i = 2^{−i} ∑_{q∈A} d(q, m_q)`. -/
noncomputable def Gamma {n : ℕ} (d : Fin n → Fin n → ℝ) (M : Finset (Fin n)) (hM : M.Nonempty)
    (i : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ i * ∑ q, distToSet d M hM q

/-- `A_{i,M} = {q ∈ A : d(q, m_q) ≤ Γ_i}`. -/
noncomputable def levelSet {n : ℕ} (d : Fin n → Fin n → ℝ) (M : Finset (Fin n))
    (hM : M.Nonempty) (i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun q => distToSet d M hM q ≤ Gamma d M hM i)

/-- The sampling weight `∑_{p∈S} d(p, m_p)` of a set `S` (P_{i,M}[S] is
`wSum (S ∩ A_{i,M}) / wSum A_{i,M}`). -/
noncomputable def wSum {n : ℕ} (d : Fin n → Fin n → ℝ) (M : Finset (Fin n)) (hM : M.Nonempty)
    (S : Finset (Fin n)) : ℝ :=
  ∑ p ∈ S, distToSet d M hM p

end MinSumFPT


