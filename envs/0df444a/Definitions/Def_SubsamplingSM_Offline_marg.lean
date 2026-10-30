-- Prove2me | Definitions.Def_SubsamplingSM_Offline_marg
-- name    : SubsamplingSM_Offline_marg
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:46:14.624907+00:00
-- url     : https://prove2.me/theorems/fbbeafac-0051-47f4-a47d-ccf035518da6
-- title:
--   Marginal gain $f(u \mid S)$
-- statement:
--   Let $N$ be a finite ground set and $f:2^N\to\mathbb R$ a set function. The **marginal gain** of an element $u\in N$ with respect to a set $S\subseteq N$ is
--   $$f(u\mid S)=f(S\cup\{u\})-f(S).$$
--
--   Marginal gains drive both greedy algorithms of the mission: SampleGreedy and Algorithm 2 add the candidate with the largest marginal gain, and every bound of the analysis is a sum of marginal gains.
--
--   **Formalization Note** Subsets of the ground set are `Finset α`; $S\cup\{u\}$ is `insert u S`.
-- source:
--   Harshaw, Kazemi, Feldman, Karbasi, The Power of Subsampling in Submodular Maximization, arXiv:2104.02772v1, §3, p. 5

import Mathlib

namespace SubsamplingSM.Offline

/-- **Marginal gain `f(u | S)`.**
Harshaw, Kazemi, Feldman, Karbasi, *The Power of Subsampling in Submodular Maximization*,
arXiv:2104.02772v1, §3, p. 5 (unnumbered): "we write the marginal gain of an element as
`f(e | S) := f(S ∪ {e}) − f(S)`".

`marg f S u = f(S ∪ {u}) − f(S)`. Sets are `Finset α` and `f : Finset α → ℝ`; `S ∪ {u}` is
`insert u S`. -/
def marg {α : Type*} [DecidableEq α] (f : Finset α → ℝ) (S : Finset α) (u : α) : ℝ :=
  f (insert u S) - f S

end SubsamplingSM.Offline


