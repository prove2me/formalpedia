-- Prove2me | Definitions.Def_FTPLLinBandit_FTPLRun_regret
-- name    : FTPLLinBandit_FTPLRun_regret
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:09:31.68794+00:00
-- url     : https://prove2.me/theorems/86c073f3-d0d9-43bb-b1ef-d21b9a059476
-- title:
--   Regret $\mathrm{Reg}_T(a)=\mathbb E\sum_{t\le T}\langle a-a_t,\theta_t\rangle$
-- statement:
--   For a run, a horizon $T$ and a fixed comparator $a\in\mathbb R^d$, the **regret** is
--   $$\mathrm{Reg}_T(a)=\mathbb E\Big[\sum_{t=1}^{T}\big(r_t(a)-r_t(a_t)\big)\Big]=\mathbb E\Big[\sum_{t=1}^{T}\langle a-a_t,\theta_t\rangle\Big],$$
--   where $a_t$ is the action played in round $t$ and $r_t(a)=\langle a,\theta_t\rangle+b_t$.
--
--   **Formalization Note** Rounds $0,\dots,T-1$ are the paper's rounds $1,\dots,T$. The intercepts cancel. The integrand is measurable and bounded, so the integral is the expectation.
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, §2, p.4

import Mathlib
import Definitions.Def_FTPLLinBandit_FTPLRun_thetaHat

open MeasureTheory
open scoped InnerProductSpace

namespace FTPLLinBandit

variable {d : ℕ} {A : Set (EuclideanSpace ℝ (Fin d))} {ν : Measure (EuclideanSpace ℝ (Fin d))}
  {x : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} {s : Scheme} {γ β : ℝ} {N : ℕ}
  {lam : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **The regret `Reg_T(a)` of a run against a fixed comparator.** Wei, arXiv:2610.17818, §2,
p.4: "For every fixed comparator a ∈ A, we study the regret:
Reg_T(a) = E[∑_{t=1}^T (r_t(a) − r_t(a_t))] = E[∑_{t=1}^T ⟨a − a_t, θ_t⟩]."

`run.regret T a = E[∑_{t<T} ⟨a − a_t, θ_t⟩]`, where `a_t` is the played action (slot `0` of round
`t`, `FTPLRun.slotAction` evaluated on the run's own estimates).

**Formalization Note.** Rounds `0, …, T − 1` are the paper's rounds `1, …, T`. The intercept `b_t`
cancels in `r_t(a) − r_t(a_t)`, so the regret is the expected sum of `⟨a − a_t, θ_t⟩`. The
integrand is measurable and bounded (all draws, `θ_t`, `x` and `sq` are measurable, and
`|r_t| ≤ 1` on `A`), so the Bochner integral is the expectation. -/
noncomputable def FTPLRun.regret (run : FTPLRun A ν x s γ β N lam Ω P) (T : ℕ)
    (a : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∫ ω, ∑ t ∈ Finset.range T,
    ⟪a - run.slotAction (fun τ => run.thetaHat τ ω) t ⟨0, by omega⟩ ω, run.θ t ω⟫_ℝ ∂P

end FTPLLinBandit


