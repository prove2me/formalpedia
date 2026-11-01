-- Prove2me | Definitions.Def_RiskStopTC_nested
-- name    : RiskStopTC_nested
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:34:17.890554+00:00
-- url     : https://prove2.me/theorems/a7f4aef4-6232-482c-a885-52f489d89728
-- title:
--   Nested functionals $\rho_{s,t}=\varrho_s\circ\cdots\circ\varrho_{t-1}$ (5.1)
-- statement:
--   Given one-step mappings $\varrho_t$, the **nested functionals** are
--   $$\rho_{s,t}(\cdot)=\varrho_{s|\mathcal F_s}\Big(\varrho_{s+1|\mathcal F_{s+1}}\big(\cdots\varrho_{t-1|\mathcal F_{t-1}}(\cdot)\big)\Big),\qquad 0\le s<t\le T,$$
--   and $\rho_{t,t}$ is the identity. They are computed by $\rho_{s,t}(X)=\varrho_s(\rho_{s+1,t}(X))$ for $s<t$.
--
--   The composition $\rho_{0,T}$ is the risk functional applied to the stopped reward in the optimal stopping problem (5.15); $\rho_{m,T}$ is its conditional version from time $m$.
--
--   **Formalization Note** `nested ϱ s t X` is `X` when $t\le s$. The paper defines $\rho_{T,T}=\mathrm{id}$ (footnote 10, p.20); here $\rho_{m,m}=\mathrm{id}$ for every $m$, which is what clause (iv) of Theorem 5.6 needs at $m=0$.
-- source:
--   Pichler, Liu & Shapiro, Risk averse stochastic programming: time consistency and optimal stopping, arXiv:1808.10807v3, Definition 5.1, equation (5.1), p.17; footnote 10, p.20

import Mathlib

namespace RiskStopTC

/-- **The nested functionals (5.1).** Pichler, Liu & Shapiro, arXiv:1808.10807v3, Definition 5.1,
p.17: "ρs,t(·) := ϱs|Fs(ϱs+1|Fs+1(· · · ϱt−1|Ft−1(·))), 0 ≤ s < t ≤ T", and footnote 10, p.20:
"By the definition ρT,T(ZT) ≡ ZT."

`nested ϱ s t X = ϱ s (nested ϱ (s+1) t X)` for `s < t`, and `nested ϱ s t X = X` for `t ≤ s`.

**Formalization Note.** `ρ_{m,m}` is the identity for every `m` (the paper writes this for
`m = T`; the case `m = 0` is what makes clause (iv) of Theorem 5.6 read `𝔳₀ = E₀`). -/
noncomputable def nested {Ω : Type*} (ϱ : ℕ → (Ω → ℝ) → Ω → ℝ) (s t : ℕ) (X : Ω → ℝ) :
    Ω → ℝ :=
  if s < t then ϱ s (nested ϱ (s + 1) t X) else X
termination_by t - s

end RiskStopTC


