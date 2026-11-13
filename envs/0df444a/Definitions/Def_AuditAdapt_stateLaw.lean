-- Prove2me | Definitions.Def_AuditAdapt_stateLaw
-- name    : AuditAdapt_stateLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T05:58:07.927619+00:00
-- url     : https://prove2.me/theorems/49a45fad-06d0-4d51-a2ad-a2c55f5e2015
-- title:
--   State law $d^\pi_t$ of a Markov policy started from $s_1\sim\rho$
-- statement:
--   Let $M=(\mathcal S,\mathcal A,H,(P_t)_{t\le H},(\ell_t)_{t\le H},\rho)$ be a finite-horizon MDP with finite state and action sets and let $\pi=(\pi_t)_{t\le H}$ be a Markov policy. Running $\pi$ generates $s_1\sim\rho$, $a_t\sim\pi_t(\cdot\mid s_t)$ and $s_{t+1}\sim P_t(\cdot\mid s_t,a_t)$. The **state law** $d^\pi_t$ is the law of $s_t$:
--
--   $$
--   d^\pi_t(s)=\sum_{s_0\in\mathcal S}\rho(s_0)\,\Pr\nolimits^\pi\big[s_t=s\mid s_1=s_0\big],
--   $$
--
--   the $\rho$-mixture of the state laws obtained by starting the run at each fixed state.
--
--   Every expectation in the covariance characterization (the expected cost, the average action distribution, the trace covariance and the joint law of $(s_t,a_t)$) is taken under $d^\pi_t$, the law of the policy's own states.
--
--   **Formalization Note** The fixed-start law is the published `stateDist` of `FoundationsRL.RLBasics` (a forward recursion), and $\rho$ is the field `d1` of the published `EpisodicMDP`. Layers are 0-based: `stateLaw M π t` is the paper's $d^\pi_{t+1}$, and `stateLaw M π 0` $=\rho$.
-- source:
--   Aldridge, Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing Adaptive Policies, STOC 2027 submission (held version, sha256 3f6ad545b0454d8de6836d32bb81359da5022bbc373510a7c75452ab66ec9fc2), §2 "MDPs and policies", p.3 (PDF p.3; the PDF prints no page numbers)

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core

namespace AuditAdapt

open FoundationsRL.RLBasics

/-- The state law `d^π_t` of a Markov policy `π` started from `s_1 ∼ ρ`
(Aldridge, *Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing
Adaptive Policies*, STOC 2027 submission (held version, sha256 3f6ad545…), §2, p.3: "Write d^π_t ∈ Δ(S) for the law of s_t").

`stateLaw M π t s = ∑_{s₀} ρ(s₀) · stateDist M π s₀ t s`: the `ρ`-mixture of the published
forward recursion `stateDist` from each start state.

**Formalization Note** Layers are 0-based: `stateLaw M π t` is the paper's `d^π_{t+1}`, the
law of `s_{t+1}`; `stateLaw M π 0 = ρ`. The initial law `ρ` is the field `M.d1` of the
published `EpisodicMDP`. -/
noncomputable def stateLaw {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] {H : ℕ}
    (M : EpisodicMDP S A H) (π : Policy S A H) (t : ℕ) (s : S) : ℝ :=
  ∑ s0 : S, M.d1 s0 * stateDist M π s0 t s

end AuditAdapt


