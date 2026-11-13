-- Prove2me | Definitions.Def_AuditAdapt_trCov
-- name    : AuditAdapt_trCov
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:03:42.395218+00:00
-- url     : https://prove2.me/theorems/0db83095-565d-41be-9ea4-0e3381299769
-- title:
--   Trace covariance $\operatorname{tr}\operatorname{Cov}(f(s_t,\cdot),\pi_t(\cdot\mid s_t))$ under $d^\pi_t$
-- statement:
--   For random vectors $q,z\in\mathbb R^{\mathcal A}$ with finite second moments, the **trace covariance** is $\operatorname{tr}\operatorname{Cov}(q,z)=\mathbb E\langle q,z\rangle-\langle\mathbb Eq,\mathbb Ez\rangle$.
--
--   Fix a Markov policy $\pi$, a step $t$ and a function $f:\mathcal S\times\mathcal A\to\mathbb R$. With $s_t\sim d^\pi_t$, take $q=f(s_t,\cdot)$ and $z=\pi_t(\cdot\mid s_t)$, so that $\mathbb Ez=\bar p^\pi_t$. Then
--
--   $$
--   \operatorname{tr}\operatorname{Cov}\big(f(s_t,\cdot),\pi_t(\cdot\mid s_t)\big)=\sum_{s}d^\pi_t(s)\sum_a f(s,a)\,\pi_t(a\mid s)-\sum_a\Big(\sum_s d^\pi_t(s)f(s,a)\Big)\bar p^\pi_t(a).
--   $$
--
--   The paper's $\operatorname{tr}\operatorname{Cov}(q_t,z_t)$, with $q_t=Q^{\nu}_t(s_t,\cdot)$, is this quantity for $f=Q^\nu_t$, where $\nu=\nu^\pi$ is the open-loop marginal.
--
--   **Formalization Note** This is the first form $\mathbb E\langle q,z\rangle-\langle\mathbb Eq,\mathbb Ez\rangle$ of the paper's definition, with $\mathbb Ez$ written out as $\bar p^\pi_t$ (`marginal`). Second moments are finite because $\mathcal S$ and $\mathcal A$ are finite. Layers are 0-based.
-- source:
--   Aldridge, Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing Adaptive Policies, STOC 2027 submission (held version, sha256 3f6ad545b0454d8de6836d32bb81359da5022bbc373510a7c75452ab66ec9fc2), §2 "Covariances", p.3

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_AuditAdapt_stateLaw
import Definitions.Def_AuditAdapt_openLoopMarginal

namespace AuditAdapt

open FoundationsRL.RLBasics

/-- The trace covariance `tr Cov(f(s_t, ·), π_t(· | s_t))` with `s_t ∼ d^π_t`
(Aldridge, *Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing
Adaptive Policies*, STOC 2027 submission (held version, sha256 3f6ad545…), §2 "Covariances", p.3: `tr Cov(q, z) = E⟨q, z⟩ − ⟨Eq, Ez⟩`).

For `f : S → A → ℝ`, the random vectors are `q = f(s_t, ·) ∈ ℝ^A` and `z = π_t(· | s_t) ∈ ℝ^A`
with `s_t ∼ d^π_t`, so
`trCov M π t f = ∑_s d^π_t(s) ∑_a f(s,a) π_t(a|s) − ∑_a (∑_s d^π_t(s) f(s,a)) · p̄^π_t(a)`,
where `Ez_t = p̄^π_t` is written out as `marginal M π t`.

**Formalization Note** This is the first form `E⟨q,z⟩ − ⟨Eq,Ez⟩` of the paper's definition.
Finite second moments hold automatically: `S` and `A` are finite. The paper's `tr Cov(q_t, z_t)`
is `trCov M π t (Q M ν t)` with `ν = openLoopMarginal M π`. Layers are 0-based. -/
noncomputable def trCov {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] {H : ℕ}
    (M : EpisodicMDP S A H) (π : Policy S A H) (t : ℕ) (f : S → A → ℝ) : ℝ :=
  (∑ s : S, stateLaw M π t s * ∑ a : A, f s a * π t s a) -
    ∑ a : A, (∑ s : S, stateLaw M π t s * f s a) * marginal M π t a

end AuditAdapt


