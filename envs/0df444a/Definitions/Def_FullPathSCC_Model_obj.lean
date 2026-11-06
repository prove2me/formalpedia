-- Prove2me | Definitions.Def_FullPathSCC_Model_obj
-- name    : FullPathSCC_Model_obj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:22:28.1001+00:00
-- url     : https://prove2.me/theorems/0d6255c0-fe49-447c-b429-71c80d193de4
-- title:
--   (8) — the objective of the risk-sensitive Bellman equation
-- statement:
--   For a time $t$, a continuation value function $W$ on states, a state $x=(K,T,\vartheta)$ and an action $a=(C,\mu)$, the **objective of the Bellman equation (8)** is
--
--   $$
--   \mathrm{obj}_t(W;x,a)=U_t(C)-\frac1{k_t}\ln\Bigl(\sum_{j\in\mathcal S}p_{\vartheta j}(T)\exp\bigl(-k_t\beta\,W(g_{K,t}(K,T,\vartheta,C,\mu),\,g_{T,t}(K,T,\mu),\,j)\bigr)\Bigr),\qquad k_t=k\beta^t .
--   $$
--
--   The sum is the conditional expectation (7). The Bellman equation (8) reads $V_t(x)=\max_{a}\mathrm{obj}_t(V_{t+1};x,a)$ over the admissible actions, and (A.4), (A.9) select maximizers of this objective with $W=V^*_{t+1}$.
-- source:
--   Zhao, Basu, Lontzek & Schmedders, The Social Cost of Carbon When We Wish for Full-Path Robustness, Management Science 69(12) (2023), doi:10.1287/mnsc.2023.4736, (7) and (8), p.7591; (A.4), p.7601

import Mathlib
import Definitions.Def_FullPathSCC_Model

namespace FullPathSCC

namespace Model

variable {S : Type*}

/-- The objective maximized in the Bellman equation (8) (Management Science 69(12) (2023), (7)
and (8), p.7591; also (A.4), p.7601): for a continuation value function `W` (the paper's
`V_{t+1}`), a state `x = (K, T, ϑ)` and an action `a = (C, μ)`,
`U_t(C) − (1/k_t) ln Σ_{j ∈ 𝒮} p_{ϑ j}(T) exp(−k_t β W(g_{K,t}(K,T,ϑ,C,μ), g_{T,t}(K,T,μ), j))`,
with `k_t = k β^t`.

**Formalization Note** The conditional expectation (7) is the finite sum over the next disaster
state `j`. -/
noncomputable def obj [Fintype S] (M : Model S) (t : ℕ) (W : State S → ℝ) (x : State S)
    (a : ℝ × ℝ) : ℝ :=
  M.U t a.1 - 1 / M.kt t *
    Real.log (∑ j : S, M.p x.2.2 j x.2.1 * Real.exp (-(M.kt t) * M.β * W (M.next t x a j)))

end Model

end FullPathSCC


