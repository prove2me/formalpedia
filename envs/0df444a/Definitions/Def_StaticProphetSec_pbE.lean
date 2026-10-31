-- Prove2me | Definitions.Def_StaticProphetSec_pbE
-- name    : StaticProphetSec_pbE
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:09:35.422677+00:00
-- url     : https://prove2.me/theorems/181edee0-2bb1-4c1b-bff1-0b68b8d37fa0
-- title:
--   The Poisson binomial expectation $\mathbb E[f(D_q)]$
-- statement:
--   For $q\in[0,1]^n$, let $D_q$ be the sum of independent Bernoulli random variables with means $q_1,\dots,q_n$. For $f:\mathbb N_0\to\mathbb R$,
--
--   $$\mathbb E[f(D_q)]=\sum_{\ell=0}^nf(\ell)\,\mathbb P(D_q=\ell).$$
--
--   The binomial $\mathrm{Bin}(n,r)$ is the case in which every $q_i$ equals $r$.
--
--   **Formalization Note** $\mathbb P(D_q=\ell)$ is the published `pbPMF q univ ℓ`, a counting formula. It is a probability when $q\in[0,1]^n$, which every statement about a law assumes.
-- source:
--   Arnosti & Ma, Tight Guarantees for Static Threshold Policies in the Prophet Secretary Problem, arXiv:2108.12893v2, p.17

import Mathlib
import Definitions.Def_CommitteeVoting_SingleVoter_PoissonBinomial

open CommitteeVoting.SingleVoter (pbPMF)

namespace StaticProphetSec

/-- The expectation `E[f(D_q)]` where `D_q` is the sum of independent Bernoulli variables with
means `q_1, …, q_n`, the Poisson binomial law (Arnosti & Ma, arXiv:2108.12893v2, p.17). The
binomial `Bin(n, r)` is the constant vector `fun _ => r`.

**Formalization Note.** `pbPMF q Finset.univ ℓ` is the counting formula for `P(D_q = ℓ)`, which
vanishes for `ℓ > n`, so the sum over `0, …, n` is the whole expectation. The formula is a
probability when `q i ∈ [0, 1]`; every statement about a law assumes this, except the limit
`StaticProphetSec.poisson_limit`, which holds as `n → ∞`, when `k / n ≤ 1` eventually. -/
noncomputable def pbE {n : ℕ} (f : ℕ → ℝ) (q : Fin n → ℝ) : ℝ :=
  ∑ ℓ ∈ Finset.range (n + 1), f ℓ * pbPMF q Finset.univ ℓ

end StaticProphetSec


