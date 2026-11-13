-- Prove2me | Definitions.Def_AuditAdapt_jointMinusProduct
-- name    : AuditAdapt_jointMinusProduct
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:03:57.291484+00:00
-- url     : https://prove2.me/theorems/837cff81-14a0-4d78-b7f2-4b5971f23b5c
-- title:
--   $\mathbb E_{P_t}f-\mathbb E_{P^S_t\otimes P^A_t}f$: joint law versus product of marginals
-- statement:
--   Under a Markov policy $\pi$, the pair $(s_t,a_t)$ has joint law $P_t(s,a)=d^\pi_t(s)\pi_t(a\mid s)$, with marginals $P^S_t=d^\pi_t$ and $P^A_t=\bar p^\pi_t$. For $f:\mathcal S\times\mathcal A\to\mathbb R$ this definition is the difference
--
--   $$
--   \mathbb E_{(s,a)\sim P_t}[f(s,a)]-\mathbb E_{(s,a)\sim P^S_t\otimes P^A_t}[f(s,a)]=\sum_{s,a}d^\pi_t(s)\pi_t(a\mid s)f(s,a)-\sum_{s,a}d^\pi_t(s)\bar p^\pi_t(a)f(s,a).
--   $$
--
--   It measures how much the dependence between state and action, as opposed to the product law in which they are independent, changes the mean of $f$. The summands of display (4) of Theorem 3.4 are this quantity for $f=Q^\nu_t$.
--
--   **Formalization Note** Layers are 0-based; $\bar p^\pi_t$ is `marginal M π t`.
-- source:
--   Aldridge, Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing Adaptive Policies, STOC 2027 submission (held version, sha256 3f6ad545b0454d8de6836d32bb81359da5022bbc373510a7c75452ab66ec9fc2), §2 "Information quantities" and Theorem 3.4 (4), p.3

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_AuditAdapt_stateLaw
import Definitions.Def_AuditAdapt_openLoopMarginal

namespace AuditAdapt

open FoundationsRL.RLBasics

/-- The difference `E_{(s,a)∼P_t}[f(s,a)] − E_{(s,a)∼P^S_t⊗P^A_t}[f(s,a)]` between the expectation
of `f` under the joint law `P_t(s,a) = d^π_t(s) π_t(a | s)` of `(s_t, a_t)` and under the product
of its marginals `P^S_t = d^π_t`, `P^A_t = p̄^π_t`
(Aldridge, *Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing
Adaptive Policies*, STOC 2027 submission (held version, sha256 3f6ad545…), §2 "Information quantities", p.3, and Theorem 3.4 (4), p.3).

**Formalization Note** Layers are 0-based. The summand of the paper's (4) is
`jointMinusProduct M π t (Q M ν t)` with `ν = openLoopMarginal M π`. -/
noncomputable def jointMinusProduct {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] {H : ℕ}
    (M : EpisodicMDP S A H) (π : Policy S A H) (t : ℕ) (f : S → A → ℝ) : ℝ :=
  (∑ s : S, ∑ a : A, stateLaw M π t s * π t s a * f s a) -
    ∑ s : S, ∑ a : A, stateLaw M π t s * marginal M π t a * f s a

end AuditAdapt


