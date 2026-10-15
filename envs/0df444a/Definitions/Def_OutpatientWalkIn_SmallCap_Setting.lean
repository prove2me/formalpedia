-- Prove2me | Definitions.Def_OutpatientWalkIn_SmallCap_Setting
-- name    : OutpatientWalkIn_SmallCap_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:45.240472+00:00
-- url     : https://prove2.me/theorems/98d26e3b-b6c1-478f-bcfd-ed8ba97c1b4a
-- title:
--   §3–§4 — parameters, Assumptions 1–2, the observable equilibrium (6)–(10) with cost (Ob.P), and the unobservable equilibrium (Condition 1, (18)–(19)) with cost (Un.P)
-- statement:
--   This module defines the outpatient model of Liu, van Jaarsveld, Wang and Xiao and its two information settings.
--
--   1. **Parameters** (§3). Strategic patients arrive as a Poisson stream of rate $\lambda > 0$, and exogenous walk-ins arrive at rate $\lambda_E \ge 0$. Service is worth $R > 0$, and appointment delay costs $C_D > 0$ per day. In-clinic waiting costs $C_W > 0$. The provider pays $C_L \ge 0$ per lost patient and $C_O \ge 0$ per unit of overtime. Total daily capacity is $\mu > 0$, split into appointment hours $\mu_S$ and walk-in hours $\mu_W = \mu - \mu_S$.
--   2. **Standing assumptions.** Assumption 1 (p. 13): the in-clinic wait function $w$ is convex and strictly increasing on $[0,\infty)$, with $w(0)=0$. Assumption 2 (p. 19): the overtime function $o$ is convex and strictly increasing on $[0,\infty)$.
--   3. **Observable setting** ($C_G = 0$, Lemma 4). Every strategic patient sees the exact delay. A strategy is a triple $(\delta, p_W, p_B)$: schedule when the observed delay is at most $\delta$, and otherwise walk in or balk with probabilities $p_W$, $p_B$. The second-stage utilities are $u^2_S(d) = R - C_D d$ (1) and $u^2_W(p_W) = R - C_W\,w\big((\lambda_E + p_W\lambda)/\mu_W\big)$ ((2) with (5)); balking is worth $u^2_B = 0$. A triple with $\delta, p_W, p_B \ge 0$ and $p_W + p_B > 0$ is an **observable equilibrium** at $\mu_S$ when, with $m = \frac{p_W}{p_W+p_B}u^2_W(p_W) + \frac{p_B}{p_W+p_B}u^2_B$,
--   $$u^2_S(d) \ge m \ \ (0 \le d \le \delta),\qquad u^2_S(d) < m \ \ (d > \delta),\qquad p_W + p_B = \pi(\delta,\mu_S),$$
--   and $p_W = 0$ or $u^2_W(p_W) \ge 0$, and $p_B = 0$ or $u^2_W(p_W) \le 0$ (conditions (6)–(10), p. 14). Its cost is (Ob.P):
--   $$Z^o = C_L\,p_B\,\lambda + C_O\,o\Big(\frac{p_W\lambda + \lambda_E}{\mu_W}\Big).$$
--   4. **Unobservable setting** ($C_G = +\infty$, Lemma 6). Patients see only the expected delay and choose rates $(\lambda_S, \lambda_W, \lambda_B)$ of scheduling, walking in and balking. The expected M/D/1 delay is $\bar d = \lambda_S/(2\mu_S(\mu_S - \lambda_S))$. The utilities are $u^1_S(\lambda_S) = R - C_D\bar d$ (18), $u^1_W(\lambda_W) = R - C_W\,w\big((\lambda_W+\lambda_E)/\mu_W\big)$ (19) and $u^1_B = 0$. An **unobservable equilibrium** at $\mu_S$ is a triple of nonnegative rates with $\lambda_S + \lambda_W + \lambda_B = \lambda$ such that every option used with positive rate has maximal utility (Condition 1, p. 13). The appointment queue must be stable ($\lambda_S < \mu_S$) when $\mu_S > 0$; when $\mu_S = 0$ scheduling is unavailable ($\lambda_S = 0$) and $u^1_S$ takes no part in the comparisons. Its cost is (Un.P):
--   $$Z^u = C_L\,\lambda_B + C_O\,o\Big(\frac{\lambda_W + \lambda_E}{\mu_W}\Big).$$
--
--   These objects carry every comparison between the two settings. The blocking probability $\pi(\delta,\mu_S)$ is the closed form of Corollary C.1.
--
--   **Formalization Note** The disengagement cost $C_G$ is not a parameter. The two settings are defined directly, as the paper reduces them by Lemma 4 ($C_G = 0$, so $\lambda_S = \lambda$, $\lambda_W = 0$) and Lemma 6 ($C_G = +\infty$), and as Appendices D.3 and D.5 state them. The paper states the sign conditions $\lambda > 0$, $\lambda_E \ge 0$, $C_L, C_O \ge 0$ and $\mu > 0$ only implicitly; they are added as hypotheses. The paper's guard $p_W + p_B > 0$ only keeps the weights of (6)–(7) well defined, and it follows from (8) because $\pi > 0$. The stability and availability clauses rule out Lean's junk value of (18) at $\lambda_S \ge \mu_S$ and at $\mu_S = 0$. Walk-in intensities divide by $\mu - \mu_S$, so every theorem restricts the allocation to $0 \le \mu_S < \mu$. The functions $w$ and $o$ are constrained only on $[0,\infty)$, and every argument at which they are evaluated is nonnegative.
-- source:
--   Liu, van Jaarsveld, Wang, Xiao, Managing Outpatient Service with Strategic Walk-ins, SSRN 3558209 (version of 2022-07-05), pp. 9–25: §3.1–§3.2 (1), (2), (4), (5), Assumption 1 (p. 13), Condition 1 (p. 13), (6)–(10) (p. 14), Assumption 2 (p. 19), Lemma 4 and (Ob.P) (pp. 20–22), Lemma 6, (18), (19) (p. 23), (Un.P) (p. 25); Online Appendix pp. 10–11, D.3, D.5

import Mathlib
import Definitions.Def_OutpatientWalkIn_SmallCap_MD1Queue

namespace OutpatientWalkIn.SmallCap

noncomputable section

/-- The model parameters (§3, pp. 9–19): strategic arrival rate `lam` (λ), exogenous walk-in rate
`lamE` (λ_E), reward `R`, delay cost per day `CD`, in-clinic waiting cost `CW`, lost-demand cost `CL`,
overtime cost `CO`, total daily capacity `mu` (μ), in-clinic wait function `w` and overtime function
`o`. -/
structure Model where
  lam : ℝ
  lamE : ℝ
  R : ℝ
  CD : ℝ
  CW : ℝ
  CL : ℝ
  CO : ℝ
  mu : ℝ
  w : ℝ → ℝ
  o : ℝ → ℝ

/-- Standing assumptions: signs of the parameters (pp. 9–12), Assumption 1 (p. 13) on `w` and
Assumption 2 (p. 19) on `o`, both imposed on `[0, ∞)`. -/
structure Model.Standing (M : Model) : Prop where
  lam_pos : 0 < M.lam
  lamE_nonneg : 0 ≤ M.lamE
  R_pos : 0 < M.R
  CD_pos : 0 < M.CD
  CW_pos : 0 < M.CW
  CL_nonneg : 0 ≤ M.CL
  CO_nonneg : 0 ≤ M.CO
  mu_pos : 0 < M.mu
  w_convex : ConvexOn ℝ (Set.Ici 0) M.w
  w_strictMono : StrictMonoOn M.w (Set.Ici 0)
  w_zero : M.w 0 = 0
  o_convex : ConvexOn ℝ (Set.Ici 0) M.o
  o_strictMono : StrictMonoOn M.o (Set.Ici 0)

/-! ### Observable setting (`C_G = 0`, `λ_S = λ`, `λ_W = 0`; Lemma 4, §4.1, App. D.3) -/

/-- A second-stage strategy `(δ, p_W, p_B)`: schedule iff the observed delay is at most `δ`,
otherwise walk in with probability `p_W` or balk with probability `p_B`. -/
structure ObsStrategy where
  delta : ℝ
  pW : ℝ
  pB : ℝ

/-- (1): utility of scheduling with observed delay `d`. -/
def Model.u2S (M : Model) (d : ℝ) : ℝ := M.R - M.CD * d

/-- (2) with (5), `C_G = 0`, `λ_W = 0`, `λ_S = λ`: utility of walking in when a fraction `p_W` of
strategic patients walk in; `μ_W = μ - μ_S`. -/
def Model.u2W (M : Model) (μS pW : ℝ) : ℝ :=
  M.R - M.CW * M.w ((M.lamE + pW * M.lam) / (M.mu - μS))

/-- Utility of balking at the second stage, `u²_B = -C_G = 0`. -/
def u2B : ℝ := 0

/-- Observable equilibrium at allocation `μ_S`: conditions (6)–(10), p. 14, with `C_G = 0`. The
guard `0 < p_W + p_B` keeps the mixture weights of (6)–(7) well defined; it is implied by (8)
because the blocking probability is positive. -/
structure Model.IsObsEq (M : Model) (μS : ℝ) (e : ObsStrategy) : Prop where
  delta_nonneg : 0 ≤ e.delta
  pW_nonneg : 0 ≤ e.pW
  pB_nonneg : 0 ≤ e.pB
  sum_pos : 0 < e.pW + e.pB
  cond6 : ∀ d : ℝ, 0 ≤ d → d ≤ e.delta →
    M.u2S d ≥ e.pW / (e.pW + e.pB) * M.u2W μS e.pW + e.pB / (e.pW + e.pB) * u2B
  cond7 : ∀ d : ℝ, e.delta < d →
    M.u2S d < e.pW / (e.pW + e.pB) * M.u2W μS e.pW + e.pB / (e.pW + e.pB) * u2B
  cond8 : e.pW + e.pB = blockProb M.lam e.delta μS
  cond9 : e.pW = 0 ∨ M.u2W μS e.pW ≥ u2B
  cond10 : e.pB = 0 ∨ M.u2W μS e.pW ≤ u2B

/-- The provider's cost (Ob.P), p. 22: `C_L p_B λ + C_O o((p_W λ + λ_E)/μ_W)`. -/
def Model.obsCost (M : Model) (μS : ℝ) (e : ObsStrategy) : ℝ :=
  M.CL * e.pB * M.lam + M.CO * M.o ((e.pW * M.lam + M.lamE) / (M.mu - μS))

/-! ### Unobservable setting (`C_G = +∞`; Lemma 6, §4.2, App. D.5) -/

/-- A first-stage strategy `(λ_S, λ_W, λ_B)`: the rates of strategic patients who schedule, walk in
and balk. -/
structure UnobsStrategy where
  lamS : ℝ
  lamW : ℝ
  lamB : ℝ

/-- The expected delay of an M/D/1 queue with arrival rate `λ_S` and service rate `μ_S`, the
fraction in (18): `λ_S / (2 μ_S (μ_S - λ_S))`. -/
def dbar (μS lamS : ℝ) : ℝ := lamS / (2 * μS * (μS - lamS))

/-- (18): expected utility of scheduling. -/
def Model.u1S (M : Model) (μS lamS : ℝ) : ℝ := M.R - M.CD * dbar μS lamS

/-- (19): expected utility of walking in. -/
def Model.u1W (M : Model) (μS lamW : ℝ) : ℝ :=
  M.R - M.CW * M.w ((lamW + M.lamE) / (M.mu - μS))

/-- Unobservable equilibrium at allocation `μ_S`: Condition 1 (p. 13) with `u¹_B = 0`, (18), (19).
The appointment queue must be stable (`λ_S < μ_S`) when `μ_S > 0`; when `μ_S = 0` scheduling is not
available (`λ_S = 0`) and `u¹_S` takes no part in the comparisons. -/
structure Model.IsUnobsEq (M : Model) (μS : ℝ) (u : UnobsStrategy) : Prop where
  lamS_nonneg : 0 ≤ u.lamS
  lamW_nonneg : 0 ≤ u.lamW
  lamB_nonneg : 0 ≤ u.lamB
  total : u.lamS + u.lamW + u.lamB = M.lam
  stable : 0 < μS → u.lamS < μS
  unavailable : μS = 0 → u.lamS = 0
  sched_best : 0 < u.lamS → M.u1S μS u.lamS ≥ M.u1W μS u.lamW ∧ M.u1S μS u.lamS ≥ 0
  walk_best : 0 < u.lamW →
    M.u1W μS u.lamW ≥ 0 ∧ (0 < μS → M.u1W μS u.lamW ≥ M.u1S μS u.lamS)
  balk_best : 0 < u.lamB →
    0 ≥ M.u1W μS u.lamW ∧ (0 < μS → 0 ≥ M.u1S μS u.lamS)

/-- The provider's cost (Un.P), p. 25: `C_L λ_B + C_O o((λ_W + λ_E)/μ_W)`. -/
def Model.unobsCost (M : Model) (μS : ℝ) (u : UnobsStrategy) : ℝ :=
  M.CL * u.lamB + M.CO * M.o ((u.lamW + M.lamE) / (M.mu - μS))

end

end OutpatientWalkIn.SmallCap


