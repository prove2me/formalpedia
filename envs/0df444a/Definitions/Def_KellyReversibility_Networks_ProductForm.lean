-- Prove2me | Definitions.Def_KellyReversibility_Networks_ProductForm
-- name    : KellyReversibility_Networks_ProductForm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T02:37:52.222917+00:00
-- url     : https://prove2.me/theorems/18a39db5-b2a5-49dc-aa2e-725e39a60eef
-- title:
--   Product form $\pi(\mathbf C)=\prod_j \pi_j(\mathbf c_j)$ for the open network of §3.1
-- statement:
--   For the open network of queues of Section 3.1, let
--   $$\alpha_j(i,s)=\begin{cases}\nu(i) & \text{if } r(i,s)=j,\\ 0 & \text{otherwise,}\end{cases}\qquad a_j=\sum_{i=1}^{I}\sum_{s=1}^{S(i)}\alpha_j(i,s),$$
--   so that $a_j$ is the mean number of customers arriving at queue $j$ per unit time in equilibrium. Let
--   $$b_j^{-1}=\sum_{n=0}^{\infty}\frac{a_j^n}{\prod_{l=1}^{n}\phi_j(l)},$$
--   and for a state $\mathbf c_j=(c_j(1),\dots,c_j(n_j))$ of queue $j$ define
--   $$\pi_j(\mathbf c_j)=b_j\prod_{l=1}^{n_j}\frac{\alpha_j(t_j(l),s_j(l))}{\phi_j(l)},\qquad \pi(\mathbf C)=\prod_{j=1}^{J}\pi_j(\mathbf c_j).$$
--
--   These are the candidate equilibrium distributions of a single queue and of the whole network in Theorem 3.1 and Corollary 3.4.
--
--   **Formalization Note** $b_j$ is defined as the inverse of the series written with Lean's `tsum`. The book assumes none of $b_1,\dots,b_J$ is zero, i.e. that each series converges; when a series diverges Lean's `tsum` is $0$ and so is $b_j$, so every theorem that uses $b_j$ carries the convergence of the series as an explicit summability hypothesis.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 61, §3.1 (definitions of α_j(i,s), a_j, b_j, π_j(c_j) and Theorem 3.1)

import Mathlib
import Definitions.Def_KellyReversibility_Networks_OpenNetwork

namespace KellyReversibility.Networks

namespace Network

variable {I J : ℕ}

/-- `α_j(i, s) = ν(i)` if `r(i, s) = j` and `0` otherwise (p. 61; Lean stages are `0`-based). -/
noncomputable def alpha (N : Network I J) (j : Fin J) (i : Fin I) (s : Fin (N.S i)) : ℝ :=
  if N.r i s = j then N.ν i else 0

/-- `a_j = ∑_{i=1}^{I} ∑_{s=1}^{S(i)} α_j(i, s)`, the mean number of arrivals at queue `j` per
unit time in equilibrium (p. 61). -/
noncomputable def a (N : Network I J) (j : Fin J) : ℝ :=
  ∑ i : Fin I, ∑ s : Fin (N.S i), N.alpha j i s

/-- `∏_{l=1}^{n} φ_j(l)` (the empty product, `n = 0`, is `1`). -/
noncomputable def phiProd (N : Network I J) (j : Fin J) (n : ℕ) : ℝ :=
  ∏ l ∈ Finset.Icc 1 n, N.φ j l

/-- `b_j = (∑_{n=0}^{∞} a_j^n / ∏_{l=1}^{n} φ_j(l))⁻¹` (p. 61). The book assumes `b_j ≠ 0`, i.e.
that the series converges; every theorem using `b` carries that summability as a hypothesis
(without it Lean's `tsum` is `0` and `b j = 0`). -/
noncomputable def b (N : Network I J) (j : Fin J) : ℝ :=
  (∑' n : ℕ, N.a j ^ n / N.phiProd j n)⁻¹

/-- `π_j(c_j) = b_j ∏_{l=1}^{n_j} α_j(t_j(l), s_j(l)) / φ_j(l)` for a state
`c_j = (c_j(1), …, c_j(n_j))` of queue `j` (p. 61). -/
noncomputable def queuePi (N : Network I J) (j : Fin J) (c : List (N.Cls j)) : ℝ :=
  N.b j * ∏ l : Fin c.length, N.alpha j (c.get l).1.1 (c.get l).1.2 / N.φ j (l + 1)

/-- The product form `π(C) = ∏_{j=1}^{J} π_j(c_j)` of Theorem 3.1 (p. 61). -/
noncomputable def netPi (N : Network I J) (C : N.State) : ℝ :=
  ∏ j : Fin J, N.queuePi j (C j)

end Network

end KellyReversibility.Networks


