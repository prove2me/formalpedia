-- Prove2me | Definitions.Def_FranklKupavskii2022_EMC_emcMax
-- name    : FranklKupavskii2022_EMC_emcMax
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:13:11.304932+00:00
-- url     : https://prove2.me/theorems/89785419-de63-4661-801d-e8cdd703282c
-- title:
--   The Erdős matching function $m(n,k,s)$
-- statement:
--   Let $n,k,s$ be natural numbers and $[n]=\{1,\dots,n\}$. The **Erdős matching function** is
--
--   $$
--   m(n,k,s)=\max\Big\{|\mathcal F| : \mathcal F\subseteq\binom{[n]}{k},\ \nu(\mathcal F)\le s\Big\},
--   $$
--
--   the largest number of $k$-element subsets of $[n]$ in a family with no $s+1$ pairwise disjoint members. Determining $m(n,k,s)$ is Erdős's problem; the Erdős Matching Conjecture asserts $m(n,k,s)=\max\{\binom nk-\binom{n-s}k,\binom{k(s+1)-1}k\}$.
--
--   **Formalization Note** The ground set is $\{1,\dots,n\}\subseteq\mathbb N$. The maximum is a finite maximum over feasible families; the empty family is feasible, so it is always attained. The condition $\nu(\mathcal F)<s+1$ of the paper is written $\nu(\mathcal F)\le s$.
-- source:
--   Frankl–Kupavskii, The Erdős Matching Conjecture and concentration inequalities, arXiv:1806.08855v3, Sect. 1, p. 1 (definition of m(n, k, s))

import Mathlib
import Definitions.Def_FranklKupavskii2022_EMC_matchingNumber

namespace FranklKupavskii2022.EMC

/-- The Erdős matching function `m(n, k, s)` (Frankl–Kupavskii, arXiv:1806.08855v3, Sect. 1,
p. 1): "determine the maximum m(n, k, s) of |F| subject to the condition ν(F) < s + 1", where
`F ⊂ \binom{[n]}{k}` is a family of `k`-element subsets of `[n] = {1, …, n}`.

**Formalization Note.** The ground set is `[n] = Finset.Icc 1 n ⊆ ℕ` (1-indexed, as in the
paper). `ν(F) < s + 1` is written `matchingNumber F ≤ s`. The maximum is a finite `sup` over the
feasible families; the empty family is always feasible, so the maximum is attained and
`m(n, k, s)` is the size of an actual extremal family. -/
def emcMax (n k s : ℕ) : ℕ :=
  (((Finset.Icc 1 n).powersetCard k).powerset.filter (fun F => matchingNumber F ≤ s)).sup
    Finset.card

end FranklKupavskii2022.EMC


