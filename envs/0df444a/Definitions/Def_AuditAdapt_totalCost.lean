-- Prove2me | Definitions.Def_AuditAdapt_totalCost
-- name    : AuditAdapt_totalCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:00:31.831263+00:00
-- url     : https://prove2.me/theorems/81c96e50-bb6f-4c05-af29-7e905059d8ba
-- title:
--   Expected total cost $J(\pi)$
-- statement:
--   For a Markov policy $\pi$ in a finite-horizon MDP $M$ with costs $\ell_t:\mathcal S\times\mathcal A\to\mathbb R$, the **expected total cost** is
--
--   $$
--   J(\pi)=\mathbb E^\pi\Big[\sum_{t=1}^H\ell_t(s_t,a_t)\Big]=\sum_{t=1}^H\sum_{s\in\mathcal S}d^\pi_t(s)\sum_{a\in\mathcal A}\pi_t(a\mid s)\,\ell_t(s,a),
--   $$
--
--   where $d^\pi_t$ is the law of $s_t$. The second expression is linearity of expectation applied to the joint law $P_t(s,a)=d^\pi_t(s)\pi_t(a\mid s)$ of $(s_t,a_t)$.
--
--   Costs rather than rewards are used so that a positive difference $J(\pi)-J(\nu)$ means $\pi$ does worse than $\nu$, the sign convention of regret.
--
--   **Formalization Note** The cost $\ell_t$ is the field `R t` of the published `EpisodicMDP` (documented there as a mean reward; here it is an arbitrary real function read as a cost). $J$ is defined forward, from the state laws, and not as the initial value $\mathbb E_{s_1\sim\rho}V^\pi_1(s_1)$; that identity is a separate theorem of the mission. Layers are 0-based: `Finset.range H` is $t=1,\dots,H$.
-- source:
--   Aldridge, Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing Adaptive Policies, STOC 2027 submission (held version, sha256 3f6ad545b0454d8de6836d32bb81359da5022bbc373510a7c75452ab66ec9fc2), §2 "MDPs and policies" and "Information quantities", p.3

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_AuditAdapt_stateLaw

namespace AuditAdapt

open FoundationsRL.RLBasics

/-- The expected total cost `J(π) = E^π[∑_{t=1}^H ℓ_t(s_t, a_t)]` of a Markov policy `π`
(Aldridge, *Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing
Adaptive Policies*, STOC 2027 submission (held version, sha256 3f6ad545…), §2, p.3).

`totalCost M π = ∑_{t<H} ∑_s d^π_t(s) ∑_a π_t(a | s) ℓ_t(s, a)`: linearity of expectation
applied to the law `d^π_t(s) π_t(a | s)` of `(s_t, a_t)` (the paper's `P_t`, §2, p.3).

**Formalization Note** The cost `ℓ_t` is the field `M.R t` of the published `EpisodicMDP`
(documented there as a mean reward; here it is an arbitrary real function and is read as a cost,
with no sign change). Layers are 0-based: `t ∈ Finset.range H` is the paper's `t = 1, …, H`.
`J` is defined forward, from the state laws, and not as `E_ρ V^π_1`; that identity is a
separate theorem of the mission. -/
noncomputable def totalCost {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] {H : ℕ}
    (M : EpisodicMDP S A H) (π : Policy S A H) : ℝ :=
  ∑ t ∈ Finset.range H, ∑ s : S, stateLaw M π t s * ∑ a : A, π t s a * M.R t s a

end AuditAdapt


