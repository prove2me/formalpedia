-- Prove2me | Definitions.Def_RobustMDP_Shared_supportFunction
-- name    : RobustMDP_Shared_supportFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:16:48.867295+00:00
-- url     : https://prove2.me/theorems/27d1aa67-784d-4cd8-9054-dccbc69c15bc
-- title:
--   Support function $\sigma_{\mathcal P}$ of a set of probability vectors
-- statement:
--   For a set $\mathcal P\subseteq\mathbb R^n$ and a vector $v\in\mathbb R^n$, the **support function** of $\mathcal P$ at $v$ is
--
--   $$
--   \sigma_{\mathcal P}(v) := \sup\{p^{\mathsf T} v : p\in\mathcal P\}.
--   $$
--
--   In the robust dynamic programming recursion, $\mathcal P$ is the set $\mathcal P_i^a$ of possible next-state distributions from state $i$ under action $a$, and $v$ is the value function of the next stage; $\sigma_{\mathcal P_i^a}(v)$ is then the worst-case expected continuation cost chosen by nature.
--
--   It serves chunk 01-finite-horizon (Nilim–El Ghaoui p. 780, Notation; the finite-horizon recursions (7) and (10) and the maps $g_t$ of (15)/(16), p. 783) and chunk 02-discounted (p. 780, Notation; the robust Bellman recursions (19)/(20) and (23), pp. 785–786, and the operators (29)/(30), p. 786).
--
--   **Formalization Note** The supremum is Lean's real `sSup` of the image of $\mathcal P$ under $p\mapsto\sum_j p_j v_j$. On $\mathbb R$, `sSup` of an empty or unbounded-above set is $0$; every theorem that uses it applies $\sigma$ only to nonempty sets contained in the probability simplex $\Delta_n$, for which the image is nonempty and bounded above by $\max_j v_j$, so the value is the true supremum.
-- source:
--   Nilim and El Ghaoui, Robust Control of Markov Decision Processes with Uncertain Transition Matrices, Oper. Res. 53 (2005), p. 780, Notation

import Mathlib

namespace RobustMDP.Shared

/-- The support function of a set `S ⊆ ℝⁿ` (Nilim–El Ghaoui 2005, Notation, p. 780):
`σ_S(v) := sup {pᵀ v : p ∈ S}`, written as the real `sSup` of the image of `S` under
`p ↦ ∑ⱼ p j * v j`. On `ℝ`, `sSup` of an empty or unbounded-above set is `0`; every use in this
mission takes `S` nonempty and contained in the probability simplex, where the image is nonempty
and bounded above by `maxⱼ v j`, so `sSup` is the genuine supremum. -/
noncomputable def supportFunction {n : ℕ} (S : Set (Fin n → ℝ)) (v : Fin n → ℝ) : ℝ :=
  sSup ((fun p : Fin n → ℝ => ∑ j, p j * v j) '' S)

end RobustMDP.Shared


