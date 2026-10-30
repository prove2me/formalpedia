-- Prove2me | Definitions.Def_AdaGradDHS_Diag_accNorm
-- name    : AdaGradDHS_Diag_accNorm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:17:09.248468+00:00
-- url     : https://prove2.me/theorems/a4035874-d408-4490-82bd-11055ba55bc8
-- title:
--   Accumulated gradient norm $s_{t,i} = \|g_{1:t,i}\|_2$
-- statement:
--   Let $g_1, g_2, \dots \in \mathbb{R}^d$ be the observed subgradients. For a round $t$ and a coordinate $i$, the **accumulated gradient norm** is the Euclidean norm of the $i$-th coordinates observed so far,
--   $$s_{t,i} = \|g_{1:t,i}\|_2 = \Big( \sum_{\tau=1}^t g_{\tau,i}^2 \Big)^{1/2}.$$
--
--   These are the diagonal entries of the AdaGrad preconditioner $H_t = \delta I + \operatorname{diag}(s_t)$; the regret bounds of Theorem 5 are stated in terms of $\sum_{i=1}^d \|g_{1:T,i}\|_2$.
--
--   **Formalization Note** For $t = 0$ the sum is empty and $s_{0,i} = 0$, matching the initialization $g_{1:0} = [\,]$ of Algorithm 1.
-- source:
--   Duchi, Hazan, Singer, Adaptive Subgradient Methods for Online Learning and Stochastic Optimization, JMLR 12 (2011), Figure 1 (Algorithm 1), p. 2130 ("st,i = ‖g1:t,i‖2"); §1.1, p. 2122 (g1:t,i)

import Mathlib

namespace AdaGradDHS.Diag

/-- **Accumulated gradient norm `s_{t,i} = ‖g_{1:t,i}‖₂`.**
Duchi, Hazan, Singer, *Adaptive Subgradient Methods for Online Learning and Stochastic
Optimization*, JMLR 12 (2011), Figure 1 (Algorithm 1), p. 2130: "UPDATE g1:t = [g1:t−1 gt], st,i = ‖g1:t,i‖2"; §1.1,
p. 2122: g1:t,i is "the ith row of this matrix, which amounts to the concatenation of the ith
component of each subgradient we observe".

`accNorm g t i = √(Σ_{τ=1}^t (g_τ)_i²)`.

**Formalization Note.** `accNorm g 0 i = 0` (the paper's `g1:0 = []`, so `s_0 = 0`). -/
noncomputable def accNorm {d : ℕ} (g : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ) (i : Fin d) : ℝ :=
  Real.sqrt (∑ τ ∈ Finset.Icc 1 t, (g τ i) ^ 2)

end AdaGradDHS.Diag


