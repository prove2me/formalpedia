-- Prove2me | Definitions.Def_ComplementFreeCA_XOSRounding_Rounding
-- name    : ComplementFreeCA_XOSRounding_Rounding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:19:34.444552+00:00
-- url     : https://prove2.me/theorems/fb868728-ffc2-4654-9a00-cb7910cffa89
-- title:
--   Randomized rounding of the LP relaxation: law of the preallocation and expectation
-- statement:
--   Let $x$ be a feasible solution of the LP relaxation of the combinatorial auction. **Randomized rounding** draws a preallocation $(S_1,\dots,S_n)$ as follows: independently for each bidder $i$, every bundle $S$ is chosen with probability $x_{i,S}$, and the empty bundle is chosen with the remaining probability $1-\sum_S x_{i,S}$. Hence bidder $i$'s bundle has law
--   $$q_i(S)=x_{i,S}+\mathbf 1[S=\emptyset]\Big(1-\sum_{T} x_{i,T}\Big),$$
--   the empty bundle receiving both its own weight $x_{i,\emptyset}$ and the leftover mass. A profile $\sigma=(\sigma_1,\dots,\sigma_n)$ of bundles has probability $P(\sigma)=\prod_{i} q_i(\sigma_i)$, and the expectation of a function $F$ of the preallocation is the finite sum
--   $$\mathbb E[F]=\sum_{\sigma} P(\sigma)\,F(\sigma).$$
--
--   This is the random experiment behind every expectation in the analysis of the XOS rounding algorithm.
--
--   **Formalization Note** The distribution is written as explicit finite sums over all profiles `σ : Fin n → Finset (Fin m)` rather than as a measure, which makes independence across bidders literal. For every $x$, $\sum_S q_i(S)=1$; for feasible $x$ each $q_i(S)$ is also nonnegative, so $q_i$ is a probability distribution.
-- source:
--   Dobzinski, Nisan, Schapira, Approximation Algorithms for Combinatorial Auctions with Complement-Free Bidders, Math. Oper. Res. 35(1), 2010, p. 5, §3, the randomized rounding procedure

import Mathlib

namespace ComplementFreeCA.XOSRounding

open Finset

/-- The law of bidder `i`'s preallocated bundle under randomized rounding (p. 5): every bundle
`S` is chosen with probability `x_{i,S}`, and the empty bundle additionally receives the
leftover mass `1 - ∑_T x_{i,T}`. -/
def roundingLaw {n m : ℕ} (x : Fin n → Finset (Fin m) → ℝ) (i : Fin n) (S : Finset (Fin m)) :
    ℝ :=
  x i S + if S = ∅ then 1 - ∑ T, x i T else 0

/-- The probability of a preallocation profile `σ` (bundle `σ i` for bidder `i`) when the
bidders' bundles are drawn independently from `roundingLaw x i`. -/
def profileProb {n m : ℕ} (x : Fin n → Finset (Fin m) → ℝ) (σ : Fin n → Finset (Fin m)) : ℝ :=
  ∏ i, roundingLaw x i (σ i)

/-- The expectation of a function `F` of the preallocation profile under randomized rounding:
the finite sum `∑_σ P(σ) F(σ)` over all profiles `σ : Fin n → Finset (Fin m)`. -/
def roundingExpectation {n m : ℕ} (x : Fin n → Finset (Fin m) → ℝ)
    (F : (Fin n → Finset (Fin m)) → ℝ) : ℝ :=
  ∑ σ, profileProb x σ * F σ

end ComplementFreeCA.XOSRounding


