-- Prove2me | Definitions.Def_RiskStopTC_stopRiskRec
-- name    : RiskStopTC_stopRiskRec
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:34:28.273339+00:00
-- url     : https://prove2.me/theorems/8d94a2bc-8703-4786-99a3-4d46a4de8225
-- title:
--   The stopping risk measure in recursive form: $W_T=\mathbb 1_{\{\tau=T\}}Z_T$, $W_t=\mathbb 1_{\{\tau=t\}}Z_t+\varrho_t(W_{t+1})$
-- statement:
--   For a stopping time $\tau$, define backwards
--   $$W_T=\mathbb 1_{\{\tau=T\}}Z_T,\qquad W_t=\mathbb 1_{\{\tau=t\}}Z_t+\varrho_{t|\mathcal F_t}(W_{t+1}),\quad t<T.$$
--   $W_0$ is the right-hand side of (5.2):
--   $$\mathbb 1_{\{\tau=0\}}Z_0+\varrho_{0|\mathcal F_0}\Big(\mathbb 1_{\{\tau=1\}}Z_1+\cdots+\varrho_{T-1|\mathcal F_{T-1}}\big(\mathbb 1_{\{\tau=T\}}Z_T\big)\Big).$$
--
--   **Formalization Note** For $t\ge T$ the value is $\mathbb 1_{\{\tau=T\}}Z_T$; only $t\le T$ is used.
-- source:
--   Pichler, Liu & Shapiro, Risk averse stochastic programming: time consistency and optimal stopping, arXiv:1808.10807v3, equation (5.2), p.17

import Mathlib

namespace RiskStopTC

/-- **The stopping risk measure in recursive form (5.2).** Pichler, Liu & Shapiro,
arXiv:1808.10807v3, (5.2), p.17: "ρ0,T(Zτ) = 1{τ=0} Z0 + ϱ0|F0(1{τ=1} Z1 + · · · +
ϱT−1|FT−1(1{τ=T} ZT))."

`stopRiskRec ϱ Z τ T t` is the bracket of (5.2) that starts at time `t`:
`W_T = 1{τ=T} Z_T` and `W_t = 1{τ=t} Z_t + ϱ_t(W_{t+1})` for `t < T`; (5.2) is `W_0`.

**Formalization Note.** For `t ≥ T` the value is `1{τ=T} Z_T`; only `t ≤ T` is used. -/
noncomputable def stopRiskRec {Ω : Type*} (ϱ : ℕ → (Ω → ℝ) → Ω → ℝ) (Z : ℕ → Ω → ℝ)
    (τ : Ω → WithTop ℕ) (T t : ℕ) : Ω → ℝ :=
  if T ≤ t then ({ω | τ ω = (T : WithTop ℕ)}).indicator (Z T)
  else ({ω | τ ω = (t : WithTop ℕ)}).indicator (Z t) + ϱ t (stopRiskRec ϱ Z τ T (t + 1))
termination_by T - t

end RiskStopTC


