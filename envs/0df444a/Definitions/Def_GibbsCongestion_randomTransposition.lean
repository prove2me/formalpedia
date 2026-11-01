-- Prove2me | Definitions.Def_GibbsCongestion_randomTransposition
-- name    : GibbsCongestion_randomTransposition
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:00:23.120475+00:00
-- url     : https://prove2.me/theorems/8eae3de8-991d-48e9-85c7-30b0efa8a772
-- title:
--   The random transposition Markov chain on $S_n$
-- statement:
--   The **random transposition Markov chain** on the permutations of $\{1,\dots,n\}$ selects two positions $a,b$ and interchanges the elements $\sigma(a)$ and $\sigma(b)$. The paper fixes its step probabilities in App. B.3, display (23): each transposition has probability $P(\sigma,\sigma\circ(a\,b))=1/(n(n-1))$, and the identity $\sum_{M'\in H(s)}P(M,M')=P_\alpha(s,s)$ forces holding probability $\tfrac12$. So
--   $$P=\tfrac12 I+\tfrac12 T,\qquad T(\sigma,\sigma')=\frac{1}{n(n-1)}\#\{(a,b):a\ne b,\ \sigma'=\sigma\circ(a\,b)\},$$
--   with the identity chain for $n<2$. Its stationary distribution is uniform, and its modified log-Sobolev constant is the $\rho_{rt}$ of display (15).
-- source:
--   Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §4.2, p.18; App. B.3, pp.29–30, display (23)

import Mathlib

namespace GibbsCongestion

/-- The **random transposition Markov chain** on the permutations of `{1, …, n}` (Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §4.2, p.18 and App. B.3, pp.29–30):
select two positions `a, b` and interchange the elements `σ(a)` and `σ(b)`.

**Formalization Note** The page leaves the step probabilities to App. B.3, display (23), p.30: each
transposition has probability `P(M, M') = 1/(n(n-1))`, and `∑_{M' ∈ H(s)} P(M, M') = P_α(s, s)`, which
forces holding probability `1/2`. So the chain is `(1/2)·id + (1/2)·T`, where `T` swaps a uniform
ordered pair of distinct positions, exactly the swap step of `swapStep`. For `n < 2` there is no such
pair and the chain is the identity. Its stationary distribution is uniform on `Equiv.Perm (Fin n)`. -/
noncomputable def randomTransposition (n : ℕ) :
    Matrix (Equiv.Perm (Fin n)) (Equiv.Perm (Fin n)) ℝ :=
  fun σ σ' =>
    (1 / 2) * (if σ' = σ then 1 else 0) +
      (1 / 2) * if 2 ≤ n then
        (1 / ((n : ℝ) * ((n : ℝ) - 1))) *
          ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, (if σ' = σ * Equiv.swap i j then (1 : ℝ) else 0)
      else if σ' = σ then 1 else 0

end GibbsCongestion


