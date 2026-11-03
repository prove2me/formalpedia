-- Prove2me | Definitions.Def_IncentiveFinNet_Stable
-- name    : IncentiveFinNet_Stable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:17:54.576856+00:00
-- url     : https://prove2.me/theorems/3239e6b9-91ad-47ed-861f-d280c584f03a
-- title:
--   Feasible and stable networks of contracts and prices (Definitions 2 and 3)
-- statement:
--   Fix a network setting $(\mu_i, \gamma_i, \Sigma_i, \Psi_i)_{i\in[n]}$ with utilities $g_i$.
--
--   **Feasibility (Definition 2).** A pair $(W, P)$ of $n\times n$ matrices is *feasible* if $W = W^{\top}$ (contracts need mutual agreement), $P = -P^{\top}$ (payments are zero-sum), and $W$ and $P$ obey the constraints encoded in $(\Psi_i)$: whenever $k \notin J_i$,
--   $$
--   W_{ik} = W_{ki} = P_{ik} = P_{ki} = 0 .
--   $$
--
--   **Stability (Definition 3).** A feasible $(W,P)$ is *stable* if every agent attains its maximum possible utility at the prices $P$:
--   $$
--   g_i(W,P) = \max_{(W',P)\ \text{feasible}} g_i(W',P) \qquad \text{for all } i \in [n].
--   $$
--   The prices $P$ are the same on both sides; only the contract sizes are varied.
--
--   A stable point is a network of contracts together with prices at which no agent wants to change any of its contracts. Theorem 1 characterizes when one exists and when it is unique.
--
--   **Formalization Note** The constraints are stated as "$k \notin J_i$ implies $W_{ik} = 0$ and $P_{ik} = 0$"; with the symmetry of the sets $J_i$ and of $W$ and $-P$, this gives all four zeros. "$g_i(W,P) = \max$" is stated as "$g_i(W',P) \le g_i(W,P)$ for every feasible $(W',P)$", which is equivalent because $(W,P)$ is itself feasible. The module defines `Feasible` and `Stable`.
-- source:
--   Jalan, Chakrabarti, Sarkar, Incentive-Aware Models of Financial Networks, arXiv:2212.06808v3, §2.1, Definition 2 (Feasibility) and Definition 3 (Stable point), p.10; constraints encoded in Ψ_i, p.9

import Mathlib
import Definitions.Def_IncentiveFinNet_NetworkSetting

open Matrix

namespace IncentiveFinNet

variable {n : ℕ}

/-- **Definition 2 (Feasibility)**, arXiv:2212.06808v3, p.10: `(W, P)` is feasible if
`W = Wᵀ`, `P = −Pᵀ`, and `W` and `P` obey the constraints encoded in `(Ψ_i)`, namely (p.9)
"if `k ∉ J_i` (and hence `i ∉ J_k`), we have `W_ik = W_ki = P_ik = P_ki = 0`".

**Formalization Note** The constraints are written as `k ∉ J_i → W_ik = 0 ∧ P_ik = 0`; with the
symmetry of `J` and of `W`, `−P`, this gives all four zeros. -/
def Feasible (S : NetworkSetting n) (W P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Wᵀ = W ∧ Pᵀ = -P ∧ ∀ i k, k ∉ S.J i → W i k = 0 ∧ P i k = 0

/-- **Definition 3 (Stable point)**, arXiv:2212.06808v3, p.10: a feasible `(W, P)` is stable if
each agent achieves its maximum possible utility given prices `P`:
`g_i(W, P) = max_{feasible (W′, P) under {Ψ_i}} g_i(W′, P)` for all `i ∈ [n]`.

**Formalization Note** "`= max`" is written as "`≥ g_i(W′, P)` for every feasible `(W′, P)`";
since `(W, P)` is itself feasible, the two are equivalent. The prices `P` are the same on both
sides. -/
def Stable (S : NetworkSetting n) (W P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Feasible S W P ∧
    ∀ (i : Fin n) (W' : Matrix (Fin n) (Fin n) ℝ), Feasible S W' P → S.utility i W' P ≤ S.utility i W P

end IncentiveFinNet


