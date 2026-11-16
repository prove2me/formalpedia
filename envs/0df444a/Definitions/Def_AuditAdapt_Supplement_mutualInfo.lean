-- Prove2me | Definitions.Def_AuditAdapt_Supplement_mutualInfo
-- name    : AuditAdapt_Supplement_mutualInfo
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:34:31.144975+00:00
-- url     : https://prove2.me/theorems/157287b1-33bd-4d37-940a-6ec1b4355002
-- title:
--   Mutual information $I(s_t;a_t)=\mathrm{KL}(P_t\|P^S_t\otimes P^A_t)$ in nats
-- statement:
--   Under a Markov policy $\pi$, let $P_t(s,a)=d^\pi_t(s)\pi_t(a\mid s)$ be the joint law of $(s_t,a_t)$, with marginals $P^S_t=d^\pi_t$ and $P^A_t=\bar p_t$. The **mutual information** between state and action at step $t$ is
--
--   $$
--   I_t(\pi)=I(s_t;a_t)=\mathrm{KL}\big(P_t\,\|\,P^S_t\otimes P^A_t\big)=\sum_{s,a}P_t(s,a)\,\ln\frac{P_t(s,a)}{d^\pi_t(s)\,\bar p_t(a)},
--   $$
--
--   measured in nats (natural logarithm), with $0\ln 0=0$.
--
--   It is zero exactly when the action at step $t$ is independent of the state, i.e. when $\pi$ acts open-loop on its own state distribution, and it controls the adaptivity cost in Theorem 4.2.
--
--   **Formalization Note** The definition applies the published Shannon mutual information of a finite joint law, `GuhaBroadcast.mutualInfo` (natural logarithm, marginals computed from the joint law), to $P_t$; for a Markov policy and $t<H$ those marginals are $d^\pi_t$ and $\bar p_t$. $P_t\ll P^S_t\otimes P^A_t$ always holds ($P_t(s,a)>0$ forces $d^\pi_t(s)>0$ and $\bar p_t(a)\ge P_t(s,a)>0$), so the divergence is finite. Layers are 0-based.
-- source:
--   Aldridge, Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing Adaptive Policies, STOC 2027 submission (held version, sha256 3f6ad545b0454d8de6836d32bb81359da5022bbc373510a7c75452ab66ec9fc2), §2 "Information quantities", p.3 (PDF p.3)

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_AuditAdapt_stateLaw
import Definitions.Def_GuhaBroadcast_mutualInfo

namespace AuditAdapt.Supplement

open FoundationsRL.RLBasics AuditAdapt

/-- The mutual information `I_t(π) = I(s_t; a_t) = KL(P_t ∥ P^S_t ⊗ P^A_t)`, in nats, between state and
action at step `t` under `π` (Aldridge, *Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing
Adaptive Policies*, STOC 2027 submission (held version, sha256 3f6ad545…), §2 "Information quantities", p.3:
"Under π, let P_t(s, a) = d^π_t(s)π_t(a | s) be the joint law of (s_t, a_t), with marginals P^S_t = d^π_t
and P^A_t = p̄_t. The mutual information is I_t(π) := I(s_t; a_t) = KL(P_t∥P^S_t ⊗ P^A_t), in units of
information, nats").

`mutualInfo M π t` is the published Shannon mutual information `GuhaBroadcast.mutualInfo` of the joint
law `P_t(s,a) = d^π_t(s) π_t(a | s)`:
`Σ_s Σ_a P_t(s,a) · ln (P_t(s,a) / (P^S_t(s) P^A_t(a)))`, with `P^S_t`, `P^A_t` the marginals of `P_t`.

**Formalization Note** Natural logarithm (`Real.log`), so the unit is nats; a term with `P_t(s,a) = 0`
is `0` (`0 log 0 = 0`). The marginals are computed from `P_t`; for a Markov policy and a layer `t < H`
they are `d^π_t` (`Σ_a π_t(a|s) = 1`) and the published `marginal M π t` (`p̄_t`). `P_t ≪ P^S_t ⊗ P^A_t`
always holds, so the KL divergence is finite and no `∞` case is needed. Layers are 0-based. -/
noncomputable def mutualInfo {S A : Type} [Fintype S] [Fintype A] [DecidableEq S] {H : ℕ}
    (M : EpisodicMDP S A H) (π : Policy S A H) (t : ℕ) : ℝ :=
  GuhaBroadcast.mutualInfo (fun s a => stateLaw M π t s * π t s a)

end AuditAdapt.Supplement


