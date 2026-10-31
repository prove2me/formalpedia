-- Prove2me | Definitions.Def_TechBreakthrough_Model_V
-- name    : TechBreakthrough_Model_V
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:34:33.966779+00:00
-- url     : https://prove2.me/theorems/2f62acbd-f5ba-40a0-9f00-fc573a09f7ff
-- title:
--   The value functions $V_R$, $\bar J$, $\bar V$ and $V$
-- statement:
--   The mission's value functions are
--
--   $$V_R(x)=\sup_{\tau\in T_X}\mathbf E_x[e^{-r\tau}R(X_\tau)],\qquad \bar V(x)=\sup_{\tau\in T_X}\bar J(x,\tau),$$
--
--   $$\bar J(x,\tau)=\mathbb E_x\big[1_{\{\tau<\tau_{X\ge Y}\}}e^{-r\tau}R(X_\tau)+1_{\{\tau\ge\tau_{X\ge Y}\}}e^{-r\tau_{X\ge Y}}G(X_{\tau_{X\ge Y}})\big],$$
--
--   with $\tau_{X\ge Y}=\inf\{t\ge0:X_t\ge Y\}$ and $\mathbb E_x$ the expectation under $P_x\otimes Q$, and
--
--   $$V(x,m)=\sup_{\tau}\mathbf E_{x,m}\Big[[1-F(M_\tau)]e^{-r\tau}R(X_\tau)+\int_0^\tau e^{-rt}G(M_t)f(M_t)\,dM_t\Big].$$
--
--   $V_R$ is the stand-alone problem without a breakthrough, $\bar V$ the original problem, and $V$ its Markovian form.
--
--   **Formalization Note** The page takes the supremum in $V$ over $T_{X,M}$ under $P_{x,m}$, and observes that these times are almost surely in $T_X$. Since $M$ is a function of $X$ and $m$, the supremum here is over $T_X$ under $P_x$. All suprema are real suprema; `Theorem 1` gives $V$ as a least upper bound.
-- source:
--   Décamps, Gensbittel & Mariotti, Investment Timing and Technological Breakthroughs, arXiv:2106.05112v1, (8)–(10), pp.9–10; (19), p.13

import Definitions.Def_TechBreakthrough_Model_payoff

open MeasureTheory
open scoped NNReal

namespace TechBreakthrough

namespace Model

variable (M : Model)

/-- The stand-alone value `V_R(x) = sup_{τ ∈ T_X} E_x[e^{−rτ} R(X_τ)]`, arXiv:2106.05112v1, (10),
p.10. -/
noncomputable def VR (x : ℝ) : ℝ :=
  sSup ((fun τ : M.Ω → WithTop ℝ≥0 =>
    ∫ ω, discountedAt M.r (fun t => M.R (M.X t ω)) (τ ω) ∂M.P x) '' M.T)

/-- `τ_{X≥y} = inf {t ≥ 0 : X_t ≥ y}`, arXiv:2106.05112v1, p.9. -/
noncomputable def hitUp (ω : M.Ω) (y : ℝ) : WithTop ℝ≥0 := firstTime {t | y ≤ M.X t ω}

/-- The value `J̄(x, τ)` of stopping at `τ`, arXiv:2106.05112v1, (8), p.9: the expectation under
`P_x ⊗ Q` of `1{τ < τ_{X≥Y}} e^{−rτ} R(X_τ) + 1{τ ≥ τ_{X≥Y}} e^{−rτ_{X≥Y}} G(X_{τ_{X≥Y}})`. -/
noncomputable def Jbar (x : ℝ) (τ : M.Ω → WithTop ℝ≥0) : ℝ :=
  ∫ z : M.Ω × ℝ,
    (if τ z.1 < M.hitUp z.1 z.2 then
      discountedAt M.r (fun t => M.R (M.X t z.1)) (τ z.1)
    else
      discountedAt M.r (fun t => M.G (M.X t z.1)) (M.hitUp z.1 z.2)) ∂(M.P x).prod M.Q

/-- `V̄(x) = sup_{τ ∈ T_X} J̄(x, τ)`, arXiv:2106.05112v1, (9), p.9. -/
noncomputable def Vbar (x : ℝ) : ℝ := sSup (M.Jbar x '' M.T)

/-- The set of expected rewards of (19), started at `(x, m)`. -/
noncomputable def valueSet (x m : ℝ) : Set ℝ :=
  (fun τ : M.Ω → WithTop ℝ≥0 => ∫ ω, M.payoff m τ ω ∂M.P x) '' M.T

/-- The value function `V(x, m)` of problem (19), arXiv:2106.05112v1, Proposition 1, p.13.

**Formalization Note** The page takes the supremum over `T_{X,M}` under `P_{x,m}` and observes that
every such time is `P_{x,m}`-a.s. a stopping time in `T_X`. Since `M` is a function of `X` and `m`,
the supremum is taken here over `T_X`, under `P_x`. -/
noncomputable def V (x m : ℝ) : ℝ := sSup (M.valueSet x m)

end Model

end TechBreakthrough


