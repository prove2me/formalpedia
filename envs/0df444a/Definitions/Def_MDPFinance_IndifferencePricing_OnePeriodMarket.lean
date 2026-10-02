-- Prove2me | Definitions.Def_MDPFinance_IndifferencePricing_OnePeriodMarket
-- name    : MDPFinance_IndifferencePricing_OnePeriodMarket
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:09:43.017657+00:00
-- url     : https://prove2.me/theorems/f20d02ba-fd3b-44e5-9023-4eecf78f9145
-- title:
--   Definition 4.9.1 — the one-period market and the indifference price of a contingent claim
-- statement:
--   A one-period market with a zero-interest bond, a traded asset $S$ ($S_1=sR̃$) and a
--   non-traded asset $\hat S$ ($\hat S_1=\hat s\hat R$), where $(R̃,\hat R)$ takes the four
--   values $(u,\hat u),(u,\hat d),(d,\hat u),(d,\hat d)$ with probabilities $p_1,p_2,p_3,p_4>0$,
--   under $0<d<1<u$, $\hat d<\hat u$. For a contingent claim $H=h(S_1,\hat S_1)$ and exponential
--   utility $U(x)=-e^{-\gamma x}$,
--   $$V_0^H(x,s,\hat s) := \sup_{a\in\mathbb{R}} \mathbb{E}\big[-e^{-\gamma x - \gamma
--   a(R̃-1) + \gamma H}\big].$$
--   **Definition 4.9.1.** The indifference price of $H$ is the amount $v_0=v_0(H,s,\hat s)$ such
--   that $V_0^0(x,s,\hat s) = V_0^H(x+v_0,s,\hat s)$ for every $x\in\mathbb{R}$: the price at
--   which selling $H$ short and investing the proceeds leaves the investor exactly as well off as not
--   trading it at all.
--
--   **Formalization Note.** `IsIndifferencePrice` states Definition 4.9.1's *defining equation*
--   verbatim, not the closed-form value Theorem 4.9.2 derives — a formalization that defined the
--   indifference price directly by that formula would make Theorem 4.9.2 trivially true relative to
--   the definition, this chunk's flagged pitfall. The non-traded asset $\hat S$ genuinely cannot be
--   traded (the action space is the single real number invested in $S$ alone); letting the investor
--   trade $\hat S$ too would collapse the problem to ordinary replication pricing.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 135-136, PDF 149-150, Equation (4.37) and Definition 4.9.1

import Mathlib

open MeasureTheory ProbabilityTheory

namespace MDPFinance.IndifferencePricing

/-- The one-period financial market underlying indifference pricing (Bäuerle–Rieder, p. 135,
PDF 149): a bond with zero interest, a traded asset `S` with `S1 = s·R̃`, and a non-traded asset
`Ŝ` with `Ŝ1 = ŝ·R̂`, where `(R̃,R̂)` takes the four values `(u,û), (u,d̂), (d,û), (d,d̂)` with
probabilities `p1,p2,p3,p4 > 0` (matching `Ω := {ω1,ω2,ω3,ω4}`), under Assumption (FM)
`0 < d < 1 < u`, `d̂ < û`. The investor has exponential utility `U(x) = -e^{-γx}`. -/
structure OnePeriodIndifferenceMarket (Ω : Type*) [MeasurableSpace Ω] where
  measIP : Measure Ω
  isProb : IsProbabilityMeasure measIP
  u : ℝ
  d : ℝ
  uhat : ℝ
  dhat : ℝ
  h0d : 0 < d
  hd1 : d < 1
  h1u : 1 < u
  hdhat_uhat : dhat < uhat
  γ : ℝ
  hγ : 0 < γ
  Rtilde : Ω → ℝ
  Rhat : Ω → ℝ
  hRtilde_meas : Measurable Rtilde
  hRhat_meas : Measurable Rhat
  p1 : ℝ
  p2 : ℝ
  p3 : ℝ
  p4 : ℝ
  hp_pos : 0 < p1 ∧ 0 < p2 ∧ 0 < p3 ∧ 0 < p4
  hp_sum : p1 + p2 + p3 + p4 = 1
  hlaw1 : measIP {ω | Rtilde ω = u ∧ Rhat ω = uhat} = ENNReal.ofReal p1
  hlaw2 : measIP {ω | Rtilde ω = u ∧ Rhat ω = dhat} = ENNReal.ofReal p2
  hlaw3 : measIP {ω | Rtilde ω = d ∧ Rhat ω = uhat} = ENNReal.ofReal p3
  hlaw4 : measIP {ω | Rtilde ω = d ∧ Rhat ω = dhat} = ENNReal.ofReal p4

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The risk-neutral up-probability `q := (1-d)/(u-d)` (Bäuerle–Rieder, p. 136, PDF 150). -/
noncomputable def OnePeriodIndifferenceMarket.qrn (M : OnePeriodIndifferenceMarket Ω) : ℝ :=
  (1 - M.d) / (M.u - M.d)

/-- `V_0^H(x,s,ŝ) := sup_a 𝔼[-e^{-γx-γa(R̃-1)+γH}]` for a contingent claim `H = h(S1,Ŝ1)`
(Bäuerle–Rieder, Eq. (4.37), p. 135, PDF 149). -/
noncomputable def OnePeriodIndifferenceMarket.V0 (M : OnePeriodIndifferenceMarket Ω)
    (h : ℝ → ℝ → ℝ) (x s ŝ : ℝ) : ℝ :=
  ⨆ a : ℝ, ∫ ω, -Real.exp (-M.γ * x - M.γ * a * (M.Rtilde ω - 1) +
    M.γ * h (s * M.Rtilde ω) (ŝ * M.Rhat ω)) ∂M.measIP

/-- Definition 4.9.1. The indifference price of the contingent claim `H = h(S1,Ŝ1)` is the amount
`v0 = v0(H,s,ŝ)` such that `V_0^0(x,s,ŝ) = V_0^H(x+v0,s,ŝ)` for all `x ∈ ℝ` (Bäuerle–Rieder,
p. 136, PDF 150). Stated as the defining equation, not the closed-form formula Theorem 4.9.2
derives. -/
def OnePeriodIndifferenceMarket.IsIndifferencePrice (M : OnePeriodIndifferenceMarket Ω)
    (h : ℝ → ℝ → ℝ) (s ŝ v0 : ℝ) : Prop :=
  ∀ x : ℝ, M.V0 (fun _ _ => 0) x s ŝ = M.V0 h (x + v0) s ŝ

/-- `h̃(S1,Ŝ1) := e^{γH}` (Bäuerle–Rieder, p. 136, PDF 150). -/
noncomputable def OnePeriodIndifferenceMarket.htilde (M : OnePeriodIndifferenceMarket Ω)
    (h : ℝ → ℝ → ℝ) (s1 ŝ1 : ℝ) : ℝ :=
  Real.exp (M.γ * h s1 ŝ1)

/-- `h_u(s,ŝ) := p1·h̃(su,ŝû) + p2·h̃(su,ŝd̂)` (Bäuerle–Rieder, p. 136, PDF 150). -/
noncomputable def OnePeriodIndifferenceMarket.hu (M : OnePeriodIndifferenceMarket Ω)
    (h : ℝ → ℝ → ℝ) (s ŝ : ℝ) : ℝ :=
  M.p1 * M.htilde h (s * M.u) (ŝ * M.uhat) + M.p2 * M.htilde h (s * M.u) (ŝ * M.dhat)

/-- `h_d(s,ŝ) := p3·h̃(sd,ŝû) + p4·h̃(sd,ŝd̂)` (Bäuerle–Rieder, p. 136, PDF 150). -/
noncomputable def OnePeriodIndifferenceMarket.hd (M : OnePeriodIndifferenceMarket Ω)
    (h : ℝ → ℝ → ℝ) (s ŝ : ℝ) : ℝ :=
  M.p3 * M.htilde h (s * M.d) (ŝ * M.uhat) + M.p4 * M.htilde h (s * M.d) (ŝ * M.dhat)

end MDPFinance.IndifferencePricing


