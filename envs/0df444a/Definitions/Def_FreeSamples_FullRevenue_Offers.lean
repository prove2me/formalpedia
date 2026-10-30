-- Prove2me | Definitions.Def_FreeSamples_FullRevenue_Offers
-- name    : FreeSamples_FullRevenue_Offers
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T13:53:16.714063+00:00
-- url     : https://prove2.me/theorems/d075d59b-1c6e-4aa0-a8ba-7ecec2c5dbbd
-- title:
--   Terminal allocations, Bayesian willingness to pay, and accepted payment
-- statement:
--   At a Buyer belief $N(m,v)$, let $k\in[0,\infty]$ be an offered amount of additional data and $q\ge0$ its price. For finite $k$, the cumulative additional signal $Z$ has law $N(mk,vk^2+nk)$. Its posterior mean and variance are the source's Gaussian update from $(m,v)$ with noise variance $n$. Define the post-allocation optimized utility $A(k;m,v)$ as the expectation of $U$ at that posterior. At $k=\infty$, the entire remainder reveals $\Theta$ and $A=\mathbb E[M]$.
--   $$W(k;m,v)=A(k;m,v)-U(m,v),\qquad\operatorname{pay}(k,q;m,v)=q\,\mathbf1\{q\le W(k;m,v)\}.$$
--   The Buyer accepts at indifference, as the exact extraction in Lemma 3 requires. These definitions include zero, partial and full releases; their payment is computed from the genuine utility gain. Neither optimal full allocation nor its Bayes-risk price is assumed. Integrability of post-signal optimized utility is a conclusion of Lemma 3.
-- source:
--   Drakopoulos & Makhdoumi, Providing Data Samples for Free, SSRN 3611003, pinned local PDF snapshot (creation metadata 2021-08-30; SHA-256 2e29ad6e37639d93e587e9999f63959d3eb52c66a1fe2ac7e78f3d33976e44c0), p.16, §4 policy definition and Lemma 3; p.30, proof of Lemma 3

import Definitions.Def_FreeSamples_FullRevenue_Regularity

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace FreeSamples.FullRevenue

/-- Utility after k more data points. k=∞ reveals the latent state exactly;
k=0 supplies no additional information. Finite k uses the actual Gaussian
signal with mean mk and variance vk²+nk and the source's posterior update. -/
noncomputable def afterUtility (u : ℝ → ℝ → ℝ) (n m v : ℝ)
    (k : WithTop ℝ≥0) : ℝ :=
  if k = ⊤ then fullUtility u m v else
    let h : ℝ := (k.untopD 0 : ℝ≥0)
    ∫ y, U u (Revenue.postMean n m v h y) (Revenue.postVar n v h)
      ∂(Revenue.N (m * h) (v * h ^ 2 + n * h))

/-- Buyer's genuine expected utility gain from the offered allocation. -/
noncomputable def willingnessToPay (u : ℝ → ℝ → ℝ) (n m v : ℝ)
    (k : WithTop ℝ≥0) : ℝ := afterUtility u n m v k - U u m v

/-- Nonnegative payment on acceptance, including indifference; zero on rejection. -/
noncomputable def payment (u : ℝ → ℝ → ℝ) (n m v : ℝ)
    (k : WithTop ℝ≥0) (q : ℝ≥0) : ℝ :=
  if (q : ℝ) ≤ willingnessToPay u n m v k then q else 0

end FreeSamples.FullRevenue


