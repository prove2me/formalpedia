-- Prove2me | Definitions.Def_AuditAdapt_Supplement_span
-- name    : AuditAdapt_Supplement_span
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:33:54.557284+00:00
-- url     : https://prove2.me/theorems/4a34ae3b-ffbb-44cc-8d5c-d331ebc24140
-- title:
--   Action span $\mathrm{span}_t(\pi)$ (Definition 4.1)
-- statement:
--   Let $\pi$ be a Markov policy in a finite-horizon MDP with open-loop marginal $\nu=\nu^\pi$, state laws $d^\pi_t$ and average action distributions $\bar p_t$. The **action span** at step $t$ is
--
--   $$
--   \mathrm{span}_t(\pi)=\max_{s\in\operatorname{supp}d^\pi_t}\Big(\max_{a\in\operatorname{supp}\bar p_t}Q^\nu_t(s,a)-\min_{a\in\operatorname{supp}\bar p_t}Q^\nu_t(s,a)\Big).
--   $$
--
--   It measures how much the choice of action can matter in a single reachable state, using the action-values of the open-loop marginal and only the actions that are ever played at step $t$. It is the Lipschitz constant in the information bound (Theorem 4.2).
--
--   **Formalization Note** Layers are 0-based. The supports are $\{s: d^\pi_t(s)>0\}$ and $\{a:\bar p_t(a)>0\}$ (published `stateLaw` and `marginal`), and $Q^\nu_t$ is the published `Q` of `openLoopMarginal M π`. The maxima and minimum are `⨆`/`⨅` over these finite subtypes; for a Markov policy and $t<H$ both supports are nonempty, so they are genuine maxima and minima. On an empty support the Lean value is $0$, a case no statement uses.
-- source:
--   Aldridge, Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing Adaptive Policies, STOC 2027 submission (held version, sha256 3f6ad545b0454d8de6836d32bb81359da5022bbc373510a7c75452ab66ec9fc2), Definition 4.1 (Action span), p.4 (PDF p.4)

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_AuditAdapt_stateLaw
import Definitions.Def_AuditAdapt_openLoopMarginal

namespace AuditAdapt.Supplement

open FoundationsRL.RLBasics AuditAdapt

/-- The action span `span_t(π)` of a Markov policy `π` with marginal `ν = ν^π`
(Aldridge, *Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing
Adaptive Policies*, STOC 2027 submission (held version, sha256 3f6ad545…), Definition 4.1, p.4):
`span_t(π) = max_{s ∈ supp d^π_t} ( max_{a ∈ supp p̄_t} Q^ν_t(s, a) − min_{a ∈ supp p̄_t} Q^ν_t(s, a) )`.

**Formalization Note** Layers are 0-based (`span M π t` is the paper's `span_{t+1}(π)`).
`supp d^π_t = {s | 0 < stateLaw M π t s}`, `supp p̄_t = {a | 0 < marginal M π t a}` and
`Q^ν_t = Q M (openLoopMarginal M π) t` (published layer). The maxima and the minimum are `⨆`/`⨅`
over these finite subtypes, so they are genuine maxima/minima whenever the subtypes are nonempty; that
holds for every Markov policy at every layer `t < H` (both laws are distributions). On an empty
subtype the real `⨆`/`⨅` is `0`, which no statement of the mission uses. -/
noncomputable def span {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] {H : ℕ}
    (M : EpisodicMDP S A H) (π : Policy S A H) (t : ℕ) : ℝ :=
  ⨆ s : {s : S // 0 < stateLaw M π t s},
    ((⨆ a : {a : A // 0 < marginal M π t a}, Q M (openLoopMarginal M π) t s.1 a.1) -
      ⨅ a : {a : A // 0 < marginal M π t a}, Q M (openLoopMarginal M π) t s.1 a.1)

end AuditAdapt.Supplement


