-- Prove2me | Definitions.Def_SubsamplingSM_Offline_expectSample
-- name    : SubsamplingSM_Offline_expectSample
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:51:11.565829+00:00
-- url     : https://prove2.me/theorems/dd753329-174a-48f6-947f-0dc4a0f91293
-- title:
--   Expectation over the independent sample
-- statement:
--   For a sampling probability $q$ and a real function $X$ of subsets of $N$, the expectation of $X$ under independent sampling is the finite sum
--   $$\mathbb E_q[X]=\sum_{T\subseteq N}q^{|T|}(1-q)^{\,n-|T|}\,X(T).$$
--
--   All expectations of Theorem 1 and of Lemmas 7, 8 and 10 are of this form: over the sample $N'$ of SampleGreedy, or over the coin vector $b$ of Algorithm 2 ($b_u=1$ if and only if $u\in b$), which has the same law.
--
--   **Formalization Note** The sum ranges over all $2^n$ subsets, so no integrability condition arises.
-- source:
--   Harshaw, Kazemi, Feldman, Karbasi, The Power of Subsampling in Submodular Maximization, arXiv:2104.02772v1, Algorithm 1, Lines 2–5, p. 9; the expectations of Theorem 1, p. 7, and Lemmas 7, 8, 10, pp. 13–16

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_bernW

namespace SubsamplingSM.Offline

/-- **Expectation over the Bernoulli(`q`) sample.**
Harshaw, Kazemi, Feldman, Karbasi, *The Power of Subsampling in Submodular Maximization*,
arXiv:2104.02772v1, Algorithm 1, Lines 2–5, p. 9 (each element is sampled independently with probability
`q`) and the expectations `E[·]` of Theorem 1 (p. 7) and Lemmas 7, 8, 10 (pp. 13–16).

`expectSample q X = Σ_{T ⊆ N} q^{|T|}(1 − q)^{n − |T|} X(T)` is the expectation of a
function `X` of the sample. The coins of Algorithm 2 (`b_u = 1` iff `u ∈ b`, p. 10) have the
same law, so expectations over them are `expectSample q` too.

**Formalization Note.** The expectation is an exact finite sum over the `2^n` subsets (paper.md
Reading 1); there is no integrability side condition. -/
def expectSample {α : Type*} [Fintype α] (q : ℝ) (X : Finset α → ℝ) : ℝ :=
  ∑ T : Finset α, bernW q T * X T

end SubsamplingSM.Offline


