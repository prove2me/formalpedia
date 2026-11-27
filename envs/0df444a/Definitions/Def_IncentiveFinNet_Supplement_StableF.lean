-- Prove2me | Definitions.Def_IncentiveFinNet_Supplement_StableF
-- name    : IncentiveFinNet_Supplement_StableF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:31:02.900664+00:00
-- url     : https://prove2.me/theorems/fdeabb27-b93a-4191-972f-5ae9c467df41
-- title:
--   Utility with friction (2) and its stable points
-- statement:
--   Given penalty functions $F_i:\mathbb R^n\to\mathbb R$, agent $i$'s **utility with friction** (eq. (2)) is
--
--   $$
--   g_i(W,P) = w_i^{\top}(\mu_i - Pe_i) - \gamma_i\, w_i^{\top}\Sigma_i w_i - F_i(w_i),
--   $$
--
--   where $w_i$ is the $i$-th column of $W$. A feasible $(W,P)$ (Definition 2) is a **stable point for the utilities (2)** if every agent attains its maximum utility (2) given the prices $P$ (Definition 3 with (2) in place of (1)):
--
--   $$
--   g_i(W,P) = \max_{\text{feasible }(W',P)} g_i(W',P)\qquad\text{for all } i\in[n].
--   $$
--
--   These are the stable points of Theorem 6, which models frictions imposed by a regulator, such as penalties on large contracts.
--
--   **Formalization Note** As in the published `IncentiveFinNet.Stable`, "$=\max$" is written as "$\ge g_i(W',P)$ for every feasible $(W',P)$".
-- source:
--   Jalan, Chakrabarti, Sarkar, Incentive-Aware Models of Financial Networks, arXiv:2212.06808v3, §3.1, eq. (2), p.18; Definitions 2–3, p.10

import Mathlib
import Definitions.Def_IncentiveFinNet_NetworkSetting
import Definitions.Def_IncentiveFinNet_Stable

open Matrix

namespace IncentiveFinNet.Supplement

variable {n : ℕ}

/-- Agent `i`'s **utility with friction**, Jalan, Chakrabarti, Sarkar, arXiv:2212.06808v3, §3.1,
eq. (2), p.18: `g_i(W, P) := w_iᵀ(µ_i − P e_i) − γ_i · w_iᵀ Σ_i w_i − F_i(w_i)`, the utility (1)
minus a penalty `F_i : ℝⁿ → ℝ` of agent `i`'s contract vector `w_i` (column `i` of `W`). -/
def utilityF (S : NetworkSetting n) (F : Fin n → (Fin n → ℝ) → ℝ) (i : Fin n)
    (W P : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  S.utility i W P - F i (fun j => W j i)

/-- A **stable point for the utilities (2)** (arXiv:2212.06808v3, §3.1, pp.18–19): Definitions 2–3
(p.10) with eq. (2) in place of eq. (1). `(W, P)` is feasible and every agent `i` attains, at `W`,
the maximum of `g_i(·, P)` (eq. (2)) over the feasible `(W′, P)`.

**Formalization Note** As in the published `IncentiveFinNet.Stable`, "`= max`" is written as
"`≥ g_i(W′, P)` for every feasible `(W′, P)`". -/
def StableF (S : NetworkSetting n) (F : Fin n → (Fin n → ℝ) → ℝ)
    (W P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Feasible S W P ∧
    ∀ (i : Fin n) (W' : Matrix (Fin n) (Fin n) ℝ), Feasible S W' P →
      utilityF S F i W' P ≤ utilityF S F i W P

end IncentiveFinNet.Supplement


