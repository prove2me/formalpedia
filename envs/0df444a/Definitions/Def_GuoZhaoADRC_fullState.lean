-- Prove2me | Definitions.Def_GuoZhaoADRC_fullState
-- name    : GuoZhaoADRC_fullState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:40:41.589313+00:00
-- url     : https://prove2.me/theorems/96560ea3-3200-4879-bbe3-2ed8769e91a8
-- title:
--   The extended plant state $(x^i_1,\dots,x^i_{n_i},x^i_{n_i+1})$
-- statement:
--   For subsystem $i$ at time $t$, this is the vector $(x^i_1,\dots,x^i_{n_i},x^i_{n_i+1})\in\mathbb R^{n_i+1}$: the plant states followed by the extended state $x^i_{n_i+1}=f_i(x,\xi,w_i)+\sum_k(a_{ik}-b_{ik})u_k$. The observer state $\hat x^i$ estimates it componentwise, and Theorem 3.1 (3.4) bounds $|x^i_j-\hat x^i_j|$ for $1\le j\le n_i+1$.
--
--   **Formalization Note** 0-based index $j$: for $j<n_i$ the plant state, for $j=n_i$ (the page's $n_i+1$) the extended state.
-- source:
--   B.-Z. Guo, Z.-L. Zhao, On convergence of the nonlinear active disturbance rejection control for MIMO systems, SIAM J. Control Optim. 51(2) (2013) 1727–1757, doi:10.1137/110856824, (1.6), p.1730, with x^i_{n_i+1} defined after (3.2), p.1737

import Mathlib
import Definitions.Def_GuoZhaoADRC_ADRCData
import Definitions.Def_GuoZhaoADRC_extState

namespace GuoZhaoADRC

/-- **The extended plant state `(x^i_1, …, x^i_{n_i}, x^i_{n_i+1})` of subsystem `i`.**
Guo–Zhao, SIAM J. Control Optim. 51 (2013), (1.6), p.1730, with `x^i_{n_i+1}` defined after (3.2),
p.1737.

This is the vector the ESO state `x̂^i` estimates, componentwise, in Theorem 3.1 (3.4).

**Formalization Note.** 0-based `j : Fin (n i + 1)`: for `j < n i` the plant state
`x ⟨i, j⟩`, for `j = n i` (the page's `n_i + 1`) the extended state `extState`. -/
noncomputable def fullState {m : ℕ} {n : Fin m → ℕ} {s : ℕ} (D : ADRCData m n s)
    (x : ℝ → EuclideanSpace ℝ (Σ i : Fin m, Fin (n i))) (ξ : ℝ → EuclideanSpace ℝ (Fin s))
    (xhat : ℝ → (i : Fin m) → Fin (n i + 1) → ℝ) (i : Fin m) (t : ℝ) (j : Fin (n i + 1)) : ℝ :=
  if h : j.val < n i then x t ⟨i, ⟨j.val, h⟩⟩ else extState D x ξ xhat i t

end GuoZhaoADRC


