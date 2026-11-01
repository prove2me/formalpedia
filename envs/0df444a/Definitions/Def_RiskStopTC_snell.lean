-- Prove2me | Definitions.Def_RiskStopTC_snell
-- name    : RiskStopTC_snell
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:34:14.631966+00:00
-- url     : https://prove2.me/theorems/ca49a733-75e5-451b-9937-0a8486bb37e4
-- title:
--   The Snell envelope $E_T=Z_T$, $E_t=Z_t\vee\varrho_{t|\mathcal F_t}(E_{t+1})$ (5.14)
-- statement:
--   For a process $(Z_0,\dots,Z_T)$ and one-step mappings $\varrho_t$, the **Snell envelope** is defined backwards by
--   $$E_T:=Z_T,\qquad E_t:=Z_t\vee\varrho_{t|\mathcal F_t}(E_{t+1}),\quad t=0,\dots,T-1,$$
--   where $\vee$ is the pointwise maximum.
--
--   Theorem 5.6 shows that $E_m$ is the conditional value of the risk-averse optimal stopping problem started at time $m$.
--
--   **Formalization Note** The maximum is taken pointwise on the representatives. For $t>T$ (not used) the value is set to $Z_T$.
-- source:
--   Pichler, Liu & Shapiro, Risk averse stochastic programming: time consistency and optimal stopping, arXiv:1808.10807v3, Definition 5.5, equation (5.14), p.20

import Mathlib

namespace RiskStopTC

/-- **The Snell envelope (5.14).** Pichler, Liu & Shapiro, arXiv:1808.10807v3, Definition 5.5,
p.20: "ET := ZT, Et := Zt ∨ ϱt|Ft(Et+1), t = 0, . . . , T − 1, (5.14) defined in backwards
recursive way."

`snell ϱ Z T t = Z T` for `t ≥ T`, and `snell ϱ Z T t ω = max (Z t ω) (ϱ t (snell ϱ Z T (t+1)) ω)`
for `t < T`.

**Formalization Note.** The maximum is taken pointwise on the representatives. Values for
`t > T` are not used by the paper; they are set to `Z T`. -/
noncomputable def snell {Ω : Type*} (ϱ : ℕ → (Ω → ℝ) → Ω → ℝ) (Z : ℕ → Ω → ℝ) (T : ℕ)
    (t : ℕ) : Ω → ℝ :=
  if T ≤ t then Z T else fun ω => max (Z t ω) (ϱ t (snell ϱ Z T (t + 1)) ω)
termination_by T - t

end RiskStopTC


