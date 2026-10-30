-- Prove2me | Definitions.Def_SubsamplingSM_Offline_bernW
-- name    : SubsamplingSM_Offline_bernW
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:50:43.082987+00:00
-- url     : https://prove2.me/theorems/2e7aeeec-282f-4d5b-929e-7fc251bca888
-- title:
--   Probability of a sample under independent sampling
-- statement:
--   When each element of the ground set $N$ ($|N|=n$) is put into the sample $N'$ independently with probability $q$, the probability that the sample equals a given set $T\subseteq N$ is
--   $$\Pr[N'=T]=q^{|T|}(1-q)^{\,n-|T|}.$$
--
--   This is the law of the subsampling step of SampleGreedy, and also of the coin flips of Algorithm 2.
--
--   **Formalization Note** The exponent $n-|T|$ is a natural-number difference, exact because $|T|\le n$; with $0^0=1$, $q=1$ gives the point mass at $T=N$.
-- source:
--   Harshaw, Kazemi, Feldman, Karbasi, The Power of Subsampling in Submodular Maximization, arXiv:2104.02772v1, Algorithm 1, Lines 2–5, p. 9, and §4, p. 7

import Mathlib

namespace SubsamplingSM.Offline

/-- **Probability of a sample under independent Bernoulli(`q`) sampling.**
Harshaw, Kazemi, Feldman, Karbasi, *The Power of Subsampling in Submodular Maximization*,
arXiv:2104.02772v1, Algorithm 1, Lines 2–5, p. 9: "for each `u ∈ N` do with probability `q` do Add `u` to
`N′`", and §4, p. 7: "a random subset `N′ ⊆ N` of the ground set, where each element appears
independently with some probability `q`".

`bernW q T = q^{|T|} (1 − q)^{n − |T|}` is the probability that the sample `N′` equals `T`,
for `n = |α|`.

**Formalization Note.** The natural-number subtraction `n − |T|` is exact because
`|T| ≤ n`. With `0 ^ 0 = 1`, `q = 1` gives the point mass at `T = N` and `q = 0` the point
mass at `T = ∅`. -/
def bernW {α : Type*} [Fintype α] (q : ℝ) (T : Finset α) : ℝ :=
  q ^ T.card * (1 - q) ^ (Fintype.card α - T.card)

end SubsamplingSM.Offline


