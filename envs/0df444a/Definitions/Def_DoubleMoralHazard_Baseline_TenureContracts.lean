-- Prove2me | Definitions.Def_DoubleMoralHazard_Baseline_TenureContracts
-- name    : DoubleMoralHazard_Baseline_TenureContracts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T20:53:27.524083+00:00
-- url     : https://prove2.me/theorems/ba85a5dc-0c4b-47f9-928f-82d63e9e1300
-- title:
--   Definitions 1–3, pp. 15–17 — the tenure-and-termination contracts γ¹(w), γ²(w), γ³(w) driven by (DW1)–(DW3)
-- statement:
--   The three candidate optimal contracts share one structure. The agent's promised utility starts at $W_{0-}=w$. Between observed events it decreases deterministically,
--   $$dW_t=r(W_t-\bar w)\,dt,\qquad W_t=\bar w-(\bar w-W_s)e^{r(t-s)},$$
--   until it reaches $0$, at which time the agent is terminated; if it reaches the tenure threshold $\bar w$ it stays there forever. At an observed event with jump size $j$ the promised utility becomes $\min\{W_{t-}+j,\bar w\}$ and the excess $(W_{t-}+j-\bar w)^+$ is paid to the agent. No other payments are made.
--
--   1. $\gamma^1(w)$ (Definition 1, dynamics (DW1)): threshold $\bar w^1=\mu pR^u/r$, jump $R^u$ at each reported $u$-arrival, no jump at $o$-arrivals, so
--   $$dW_t=\big\{r(W_{t-}-\bar w^1)dt+\min\{R^u,\bar w^1-W_{t-}\}d\hat N^u_t\big\},\qquad dL^1_t=(W_{t-}+R^u-\bar w^1)^+d\hat N^u_t;$$
--   2. $\gamma^2(w)$ (Definition 2, (DW2)): threshold $\bar w^2=c/r$, jumps $R^u$ at reported $u$-arrivals and $\beta^o$ at $o$-arrivals, each capped at $\bar w^2$ with the excess paid;
--   3. $\gamma^3(w)$ (Definition 3, (DW3)): threshold $\bar w^3=c/r$, jump $\beta$ at every observed arrival, capped at $\bar w^3$ with the excess paid.
--
--   In each case $\tau=\min\{t:W_t=0\}$, which is $0$ when $w=0$ and $+\infty$ when $W$ never reaches $0$.
--
--   **Formalization Note** The contracts are written as functions of the principal's observed history (reported $u$-arrivals and $o$-arrivals), not of the true arrivals, so that a hidden $u$-arrival forgoes its jump, exactly as a deviating agent experiences it. The promised utility is computed by folding over the observed events; the hitting time of $0$ from level $W\in(0,\bar w)$ at time $s$ is $s+\tfrac1r\log\frac{\bar w}{\bar w-W}$. The factor $\mathbb 1[W_{t-}\ge 0]$ of (DW1)–(DW3) is immaterial, since nothing after $\tau$ enters any utility. The contracts are defined for every real $w$; the theorems use them for $w\in[0,\bar w^i]$, as the definitions require.
-- source:
--   Tian, Astashkina and Duenyas, Dynamic Contract Design in the Presence of Double Moral Hazard, SSRN 4249177 (preprint, PDF sha256 dfddb801…), pp. 15–17, Definitions 1–3 with (DW1)–(DW3), (2.8), (2.10)

import Mathlib
import Definitions.Def_DoubleMoralHazard_Baseline_Params
import Definitions.Def_DoubleMoralHazard_Baseline_Arrivals
import Definitions.Def_DoubleMoralHazard_Baseline_Contracts

namespace DoubleMoralHazard.Baseline

open scoped ENNReal

/-- Between events the promised utility follows `dW_t = r (W_t - w̄) dt`; starting from `W` at time
`s`, its value at time `t` is `w̄ - (w̄ - W) e^{r (t - s)}`. -/
noncomputable def flow (P : Params) (wbar W s t : ℝ) : ℝ :=
  wbar - (wbar - W) * Real.exp (P.r * (t - s))

/-- The first time the flow from `W` at time `s` reaches `0`: `s` if `W ≤ 0`; never (`⊤`) if
`W ≥ w̄` (tenure); otherwise `s + log (w̄ / (w̄ - W)) / r`. -/
noncomputable def hitZero (P : Params) (wbar W s : ℝ) : ℝ≥0∞ :=
  if W ≤ 0 then ENNReal.ofReal s
  else if wbar ≤ W then ⊤
  else ENNReal.ofReal (s + Real.log (wbar / (wbar - W)) / P.r)

/-- The state of a tenure contract with threshold `w̄`, jump `ju` at each reported `u`-arrival and
jump `jo` at each `o`-arrival, started at `W_{0-} = w`, after the observed history `h`:
`(W right after the last event, time of the last event, cumulative payment)`. At an event at time
`t` with `W_{t-} = flow …` and jump `j`, the promised utility becomes `min (W_{t-} + j) w̄` and the
agent is paid `(W_{t-} + j - w̄)⁺`. -/
noncomputable def tenureState (P : Params) (wbar ju jo w : ℝ) (h : PubHistory) : ℝ × ℝ × ℝ :=
  h.foldl
    (fun st e =>
      let Wm := flow P wbar st.1 st.2.1 e.1
      let j := if e.2 then ju else jo
      (min (Wm + j) wbar, e.1, st.2.2 + max (Wm + j - wbar) 0))
    (w, 0, 0)

/-- The tenure-and-termination contract: payments are made only at observed events (as in the
state above) and the contract terminates when the promised utility first reaches `0`. -/
noncomputable def tenureContract (P : Params) (wbar ju jo w : ℝ) : Contract where
  pay h t := if t < 0 then 0 else (tenureState P wbar ju jo w h).2.2
  stop h := hitZero P wbar (tenureState P wbar ju jo w h).1 (tenureState P wbar ju jo w h).2.1

/-- `γ¹(w)` of Definition 1 (p. 15), driven by (DW1): threshold `w̄¹`, jump `min{Rᵘ, w̄¹ - W_{t-}}`
at each reported `u`-arrival, no jump at `o`-arrivals, payment `(W_{t-} + Rᵘ - w̄¹)⁺ dN̂ᵘ_t`. -/
noncomputable def gamma1 (P : Params) (w : ℝ) : Contract := tenureContract P P.wbar1 P.Ru 0 w

/-- `γ²(w)` of Definition 2 (p. 16), driven by (DW2): threshold `w̄²`, jumps `Rᵘ` (reported
`u`-arrivals) and `βᵒ` (`o`-arrivals), each capped at `w̄²`, the excess paid. -/
noncomputable def gamma2 (P : Params) (w : ℝ) : Contract := tenureContract P P.wbar2 P.Ru P.betaO w

/-- `γ³(w)` of Definition 3 (p. 17), driven by (DW3): threshold `w̄³`, jump `β` at every observed
arrival, capped at `w̄³`, the excess paid. -/
noncomputable def gamma3 (P : Params) (w : ℝ) : Contract := tenureContract P P.wbar3 P.beta P.beta w

end DoubleMoralHazard.Baseline


