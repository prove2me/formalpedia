-- Prove2me | Definitions.Def_AdvSellUpgrade_Online_Setting
-- name    : AdvSellUpgrade_Online_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T20:50:52.274723+00:00
-- url     : https://prove2.me/theorems/682a0e18-3a94-4f93-b8b3-49082a2355b0
-- title:
--   §3, §5.1–§5.2, pp. 8–18 — waiting times, p, c, π, the spot cutoff (5), the AS program (7) and the AUS program (8)
-- statement:
--   This file fixes the model of Wang, Cao, Xie and Zhan for a single server with a non-preemptive **fast-track** (priority) queue and a **regular** queue.
--
--   **Parameters.** A parameter set consists of the service rate $\mu$, the arrival rates $\lambda_h$ (crowded day) and $\lambda_l$ (uncrowded day), the probability $\alpha$ that an arriving customer sees a crowded day, the upper end $\bar c$ of the delay-cost range $[0,\bar c]$, and the exogenous regular-ticket prices $B_a$ (advance) and $B_s$ (spot). The **standing assumptions** are
--   $$0<\lambda_l<\lambda_h<\mu,\qquad \bar c>0,\qquad 0<\alpha<1 .$$
--   No sign is assumed on $B_a$ or $B_s$.
--
--   **Waiting times.** For an arrival rate $\lambda$ and a delay-sensitivity cutoff $c$ (customers with cost at least $c$ join the fast track), the expected waits in the fast-track and regular queues are
--   $$W_F(c)=\frac{\lambda}{\mu\bigl(\mu-(1-c/\bar c)\lambda\bigr)},\qquad W_R(c)=\frac{\mu\,W_F(c)}{\mu-\lambda}.$$
--
--   **The functions $p$, $c$, $\pi$** (p. 14):
--   $$p(\lambda)=\frac{\bigl(\mu-\sqrt{\mu(\mu-\lambda)}\bigr)\lambda\bar c}{(\mu-\lambda)\mu^2},\quad c(\lambda)=\frac{\bigl(\sqrt{\mu(\mu-\lambda)}-(\mu-\lambda)\bigr)\bar c}{\lambda},\quad \pi(\lambda)=\frac{(\sqrt\mu-\sqrt{\mu-\lambda})^2\bar c}{\mu(\mu-\lambda)}.$$
--
--   **Spot-only scheme S** with one deterministic rate $\lambda$. At price gap $d=P_s-B_s$ the equilibrium cutoff (one component of (5)) is
--   $$c^e(d)=\begin{cases}\dfrac{d\,\mu(\mu-\lambda)^2\bar c}{\lambda^2\bar c-d\,\mu(\mu-\lambda)\lambda}, & d<\dfrac{\lambda^2\bar c}{\mu^2(\mu-\lambda)},\\[2mm] \bar c, & \text{otherwise},\end{cases}$$
--   and the revenue per customer is $\Pi^{S}(P_s)=(P_s-B_s)(1-c^e/\bar c)+B_s$. As a function of the cutoff $\hat c$, the revenue net of $B_s$ is $\lambda^2\hat c(\bar c-\hat c)/\bigl(\mu(\mu-\lambda)(\mu\bar c-(\bar c-\hat c)\lambda)\bigr)$. A number $c$ is an **equilibrium cutoff** at gap $d$ if either $0\le c<\bar c$ and $d=c\,(W_R(c)-W_F(c))$ (the marginal customer is indifferent), or $c=\bar c$ and $\bar c\,(W_R(\bar c)-W_F(\bar c))\le d$ (no one buys fast track).
--
--   **The AS program (7).** With $m=\min\{B_a,B_s\}$, $D=\alpha P_s+(1-\alpha)B_s$, $\Delta^h(c_r)=W_R^h(c_r)-W_F^h(c_r)$ at rate $\lambda_h$ and $\Delta^l(c_f)=W_R^l(c_f)-W_F^l(c_f)$ at rate $\lambda_l$, maximise
--   $$\Pi^{AS}=P_a\Bigl(1-\frac{c_f}{\bar c}\Bigr)+D\,\frac{c_f-c_r}{\bar c}+m\,\frac{c_r}{\bar c}$$
--   over $(c_r,c_f,P_a,P_s)$ subject to
--   1. $P_a\le P_s$;
--   2. if $c_r<c_f$, then $D-m=\alpha c_r\Delta^h(c_r)$;
--   3. if $c_f<\bar c$, then $P_a-m=\alpha c_r\Delta^h(c_r)+(1-\alpha)c_f\Delta^l(c_f)$;
--   4. if $c_f=\bar c$, then $P_a-D\ge(1-\alpha)c_f\Delta^l(c_f)$;
--   5. $0<c_r\le c_f\le\bar c$.
--
--   **The AUS program (8).** With in addition an upgrading fee $K$ and $M=\min\{\alpha P_s+(1-\alpha)B_s,\;B_a+\alpha K\}$, maximise
--   $$\Pi^{AUS}=P_a\Bigl(1-\frac{c_f}{\bar c}\Bigr)+M\,\frac{c_f-c_r}{\bar c}+m\,\frac{c_r}{\bar c}$$
--   over $(c_r,c_f,P_a,P_s,K)$ subject to $P_a\le P_s$, $P_a\le B_a+K$, and constraints 2–5 above with $D$ replaced by $M$.
--
--   The sets of attainable objective values of (7) and (8) are recorded, so that their optima can be stated as a least upper bound or a maximum of these sets.
--
--   These objects are shared by every statement of the mission: Theorem 1 compares the optima of (7) and (8), and Propositions 3, 5 and 6 compute them.
--
--   **Formalization Note** Parameters are bundled in the structure `Params`; `Params.Standing` is the conjunction of the standing assumptions. $W_F$, $W_R$ are functions of the rate and the cutoff; in (7) and (8) the crowded-state waits are evaluated at $(\lambda_h,c_r)$ and the uncrowded-state waits at $(\lambda_l,c_f)$, as on p. 16. The three "if" constraints are implications, exactly as printed. The paper's $\pi(\lambda)$ is named `piFn`, and $p$, $c$ are `pFn`, `cFn`. The probability $\alpha=\beta\lambda_h/\bar\lambda$ of p. 8 is taken as a free parameter in $(0,1)$; for given $\lambda_h,\lambda_l$ every such $\alpha$ arises from exactly one $\beta\in(0,1)$. The fourth constraint of (8) is printed with $W^h$; it is read with $W^l$, as in (7): both are described on pp. 17–18 as "no one purchases the advance regular ticket at $P_a$ when $c_f=\bar c$", and with this reading (8) with a large fee $K$ contains (7). The queueing game behind (7) and (8) (Definition 1, Proposition 2, (3)) is not formalized; the programs are taken as stated.
-- source:
--   Wang, Cao, Xie, Zhan, Advance Selling and Upgrading in Priority Queues, MSOM (2025), doi:10.1287/msom.2023.0410, pp. 8–9 (§3), p. 14 (Lemma 1, (5), (6), p, c, π), p. 16 ((7)), p. 18 ((8)); Online Appendix p. 5 ((D.2), proof of Lemma 1), p. 6 (proof of Proposition 3)

import Mathlib

namespace AdvSellUpgrade.Online

/-- The exogenous data of the model (Wang–Cao–Xie–Zhan, MSOM 2025, §3, pp. 8–9): service rate `mu`,
arrival rates `lamH` (crowded day) and `lamL` (uncrowded day), the probability `alpha` that an arriving
customer sees the crowded state, the upper end `cbar` of the delay-cost range `[0, cbar]`, and the regular
ticket prices `Ba` (advance) and `Bs` (spot). -/
structure Params where
  mu : ℝ
  lamH : ℝ
  lamL : ℝ
  alpha : ℝ
  cbar : ℝ
  Ba : ℝ
  Bs : ℝ

/-- The standing assumptions of §3: `0 < λl < λh < µ` (p. 8), `c̄ > 0` (p. 9) and `0 < α < 1`
(`α = βλh/λ̄` with `β ∈ (0,1)`, p. 8). No sign is assumed on `Ba`, `Bs`. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.lamL ∧ P.lamL < P.lamH ∧ P.lamH < P.mu ∧ 0 < P.cbar ∧ 0 < P.alpha ∧ P.alpha < 1

/-- Expected wait in the fast-track (priority) queue at arrival rate `lam` when customers with delay
cost at least `c` buy fast track: `W_F = λ / (µ(µ − (1 − c/c̄)λ))` ((7), p. 16). -/
noncomputable def WF (mu cbar lam c : ℝ) : ℝ :=
  lam / (mu * (mu - (1 - c / cbar) * lam))

/-- Expected wait in the regular queue: `W_R = µ W_F / (µ − λ)` ((7), p. 16). -/
noncomputable def WR (mu cbar lam c : ℝ) : ℝ :=
  mu * WF mu cbar lam c / (mu - lam)

/-- `p(λ) = (µ − √(µ(µ − λ))) λ c̄ / ((µ − λ) µ²)` (p. 14). -/
noncomputable def pFn (mu cbar lam : ℝ) : ℝ :=
  (mu - Real.sqrt (mu * (mu - lam))) * lam * cbar / ((mu - lam) * mu ^ 2)

/-- `c(λ) = (√(µ(µ − λ)) − (µ − λ)) c̄ / λ` (p. 14). -/
noncomputable def cFn (mu cbar lam : ℝ) : ℝ :=
  (Real.sqrt (mu * (mu - lam)) - (mu - lam)) * cbar / lam

/-- The paper's `π(λ) = (√µ − √(µ − λ))² c̄ / (µ(µ − λ))` (p. 14); named `piFn` to avoid `Real.pi`. -/
noncomputable def piFn (mu cbar lam : ℝ) : ℝ :=
  (Real.sqrt mu - Real.sqrt (mu - lam)) ^ 2 * cbar / (mu * (mu - lam))

/-- One component of the spot-only equilibrium cutoff (5) (Lemma 1, p. 14) at rate `lam` and price gap
`d = Ps − Bs`. -/
noncomputable def cS (mu cbar lam d : ℝ) : ℝ :=
  if d < lam ^ 2 * cbar / (mu ^ 2 * (mu - lam)) then
    d * mu * (mu - lam) ^ 2 * cbar / (lam ^ 2 * cbar - d * mu * (mu - lam) * lam)
  else cbar

/-- Revenue per customer of the spot-only scheme S with a deterministic rate `lam` ((6) with
`α ∈ {0, 1}`, p. 14): `Π^S(Ps) = (Ps − Bs)(1 − c^e/c̄) + Bs`. -/
noncomputable def revS (mu cbar lam Bs Ps : ℝ) : ℝ :=
  (Ps - Bs) * (1 - cS mu cbar lam (Ps - Bs) / cbar) + Bs

/-- Revenue per customer as a function of the cutoff `ĉ` (proof of Proposition 3, OA p. 6), without the
constant `Bs`: `λ² ĉ (c̄ − ĉ) / (µ(µ − λ)(µc̄ − (c̄ − ĉ)λ))`. -/
noncomputable def revCut (mu cbar lam ch : ℝ) : ℝ :=
  lam ^ 2 * ch * (cbar - ch) / (mu * (mu - lam) * (mu * cbar - (cbar - ch) * lam))

/-- `c` is an equilibrium delay-sensitivity cutoff of the spot-only game at rate `lam` and price gap `d`
(Definition 1 specialised to cutoffs, proof of Lemma 1, OA p. 5): either an interior indifferent
cutoff `0 ≤ c < c̄` with `d = c(W_R(c) − W_F(c))`, or `c = c̄` with `c̄(W_R(c̄) − W_F(c̄)) ≤ d`. -/
def IsSpotEqCutoff (mu cbar lam d c : ℝ) : Prop :=
  (0 ≤ c ∧ c < cbar ∧ d = c * (WR mu cbar lam c - WF mu cbar lam c)) ∨
  (c = cbar ∧ cbar * (WR mu cbar lam cbar - WF mu cbar lam cbar) ≤ d)

/-- Objective of the AS program (7) (p. 16):
`Pa(1 − cf/c̄) + (αPs + (1 − α)Bs)(cf − cr)/c̄ + min{Ba, Bs} cr/c̄`. -/
noncomputable def objAS (P : Params) (cr cf Pa Ps : ℝ) : ℝ :=
  Pa * (1 - cf / P.cbar) + (P.alpha * Ps + (1 - P.alpha) * P.Bs) * ((cf - cr) / P.cbar)
    + min P.Ba P.Bs * (cr / P.cbar)

/-- Feasible set of the AS program (7) (p. 16). `W^h` is evaluated at `(λh, cr)`, `W^l` at `(λl, cf)`;
the three "if" constraints are implications. -/
def FeasAS (P : Params) (cr cf Pa Ps : ℝ) : Prop :=
  Pa ≤ Ps ∧
  (cr < cf → P.alpha * Ps + (1 - P.alpha) * P.Bs - min P.Ba P.Bs
      = P.alpha * cr * (WR P.mu P.cbar P.lamH cr - WF P.mu P.cbar P.lamH cr)) ∧
  (cf < P.cbar → Pa - min P.Ba P.Bs
      = P.alpha * cr * (WR P.mu P.cbar P.lamH cr - WF P.mu P.cbar P.lamH cr)
        + (1 - P.alpha) * cf * (WR P.mu P.cbar P.lamL cf - WF P.mu P.cbar P.lamL cf)) ∧
  (cf = P.cbar → Pa - (P.alpha * Ps + (1 - P.alpha) * P.Bs)
      ≥ (1 - P.alpha) * cf * (WR P.mu P.cbar P.lamL cf - WF P.mu P.cbar P.lamL cf)) ∧
  0 < cr ∧ cr ≤ cf ∧ cf ≤ P.cbar

/-- The set of objective values of (7) over its feasible set; `Π^{AS⋆}` is its supremum/maximum. -/
def asValues (P : Params) : Set ℝ :=
  {v | ∃ cr cf Pa Ps : ℝ, FeasAS P cr cf Pa Ps ∧ v = objAS P cr cf Pa Ps}

/-- Objective of the AUS program (8) (p. 18):
`Pa(1 − cf/c̄) + min{αPs + (1 − α)Bs, Ba + αK}(cf − cr)/c̄ + min{Ba, Bs} cr/c̄`. -/
noncomputable def objAUS (P : Params) (cr cf Pa Ps K : ℝ) : ℝ :=
  Pa * (1 - cf / P.cbar)
    + min (P.alpha * Ps + (1 - P.alpha) * P.Bs) (P.Ba + P.alpha * K) * ((cf - cr) / P.cbar)
    + min P.Ba P.Bs * (cr / P.cbar)

/-- Feasible set of the AUS program (8) (p. 18). The fourth constraint is read with `W^l` (the page
prints `W^h`; see the Formalization Note). -/
def FeasAUS (P : Params) (cr cf Pa Ps K : ℝ) : Prop :=
  Pa ≤ Ps ∧ Pa ≤ P.Ba + K ∧
  (cr < cf → min (P.alpha * Ps + (1 - P.alpha) * P.Bs) (P.Ba + P.alpha * K) - min P.Ba P.Bs
      = P.alpha * cr * (WR P.mu P.cbar P.lamH cr - WF P.mu P.cbar P.lamH cr)) ∧
  (cf < P.cbar → Pa - min P.Ba P.Bs
      = P.alpha * cr * (WR P.mu P.cbar P.lamH cr - WF P.mu P.cbar P.lamH cr)
        + (1 - P.alpha) * cf * (WR P.mu P.cbar P.lamL cf - WF P.mu P.cbar P.lamL cf)) ∧
  (cf = P.cbar → Pa - min (P.alpha * Ps + (1 - P.alpha) * P.Bs) (P.Ba + P.alpha * K)
      ≥ (1 - P.alpha) * cf * (WR P.mu P.cbar P.lamL cf - WF P.mu P.cbar P.lamL cf)) ∧
  0 < cr ∧ cr ≤ cf ∧ cf ≤ P.cbar

/-- The set of objective values of (8) over its feasible set; `Π^{AUS⋆}` is its maximum. -/
def ausValues (P : Params) : Set ℝ :=
  {v | ∃ cr cf Pa Ps K : ℝ, FeasAUS P cr cf Pa Ps K ∧ v = objAUS P cr cf Pa Ps K}

end AdvSellUpgrade.Online


