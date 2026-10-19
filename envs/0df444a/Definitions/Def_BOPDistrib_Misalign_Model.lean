-- Prove2me | Definitions.Def_BOPDistrib_Misalign_Model
-- name    : BOPDistrib_Misalign_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:15:45.691555+00:00
-- url     : https://prove2.me/theorems/e0dc3c23-d6e6-4752-a6b9-cbb34f1d4132
-- title:
--   §3, Prop. B.1, Thm. 1 — BOP distributor: CARA refund, pricing outcomes (a)/(b), allocation strategies F, M, FR, MR, ATP thresholds
-- statement:
--   The homogeneous-ability-to-pay model of Calmon, Jue-Rajasingh, Romero and Stenson for a distributor of a durable good in the base of the pyramid (BOP).
--
--   **Parameters.** A fraction $\beta\in(0,1)$ of customers values the product at $v_h>0$. The distributor buys at wholesale cost $w$ and salvages a returned unit at $y$. It weighs consumer surplus by $\gamma\ge 0$. It has a budget $b$ per customer, which it splits between a subsidy $x$ that raises the customers' ability to pay (ATP) and customer education, whose level it raises from $\theta_0$ to $\theta$ at marginal cost $c_\theta$. All customers share the ATP $m$, and their CARA risk aversion is $\alpha>0$.
--
--   **Standing assumptions** at ATP $m$:
--   1. $v_h>0$, $0<\beta<1$, $w\le m<v_h$, $0\le m$, $0\le\gamma<1$, $0<\theta_0<1$, $c_\theta>0$;
--   2. Assumption 1 in its homogeneous form, strict: $0<b<c_\theta(1-\theta_0)+\beta(v_h-m)$.
--
--   **Minimum refund** (eq. (3)):
--   $$r_\alpha(m)=\max\Big(0,\ m-\tfrac1\alpha\ln\tfrac{1-\beta e^{-\alpha(v_h-m)}}{1-\beta}\Big).$$
--
--   **Pricing-stage outcomes** (Proposition B.1). Under strategy (a), only informed customers buy and there are no returns:
--   $$CS^a=(v_h-m)\theta\beta,\qquad \Pi^a_D(x,\theta)=(m+x-w)\theta\beta+\gamma CS^a.$$
--   Under strategy (b), all customers are targeted and returns are accepted:
--   $$CS^b=(v_h-m)\beta-(m-r_\alpha(m))(1-\theta)(1-\beta),$$
--   $$\Pi^b_D(x,\theta)=(m+x-w)\beta+(1-\beta)(m+x-r_\alpha(m)-w+y)(1-\theta)+\gamma CS^b.$$
--   An allocation $(x,\theta)$ is feasible for regime (a) if $\theta_0\le\theta\le1$, $0\le x\le v_h-m$ and $c_\theta(\theta-\theta_0)+x\,\theta\beta\le b$. For regime (b) the same holds with the demand $\beta+(1-\theta)(1-\beta)$ in place of $\theta\beta$.
--
--   **Allocation strategies** (Theorem 1 and its proof). Write $(t)^+=\max(t,0)$ and let $1/t^{++}$ be $1/t$ for $t>0$ and $0$ otherwise.
--   $$\theta^F=\theta_0+\frac{(b-\theta_0\beta(v_h-m))^+}{c_\theta+\beta(v_h-m)},\qquad x^F=\min\Big(v_h-m,\frac{b}{\theta_0\beta}\Big),$$
--   $$\theta^M=\theta^{MR}=\min\Big(1,\theta_0+\frac b{c_\theta}\Big),\qquad x^M=x^{MR}=\frac{(b-c_\theta(1-\theta_0))^+}{\beta},$$
--   $$\theta^{FR}=\theta_0+\frac{\big(b-(v_h-m)(\beta+(1-\theta_0)(1-\beta))\big)^+}{\big(c_\theta-(v_h-m)(1-\beta)\big)^{++}}\,\mathbb 1\{y\le y_\theta\},\qquad x^{FR}=\min\Big(v_h-m,\frac{b}{\beta+(1-\theta_0)(1-\beta)}\Big),$$
--   where $y_\theta=w-(1-\gamma)(m-r_\alpha(m))-(v_h-m)$.
--   The strategy values are the pricing outcomes at these allocations: $\Pi^F=\Pi^a_D(x^F,\theta^F)$, $\Pi^M=\Pi^a_D(x^M,\theta^M)$, $\Pi^{FR}=\Pi^b_D(x^{FR},\theta^{FR})$, $\Pi^{MR}=\Pi^b_D(x^{MR},\theta^{MR})$. The surpluses $CS^F,\dots,CS^{MR}$ are defined in the same way.
--
--   **Thresholds**:
--   $$\bar w=\beta v_h+(1-\beta)y,\qquad \bar c_\theta=(1-\beta)(w-y),\qquad m^F=\frac{c_\theta/\beta+w-\gamma v_h}{1-\gamma},$$
--   $$m^{MR}=v_h-\frac{(1-\beta)(w-y)-c_\theta}{(1-\gamma)\beta},\qquad \bar m^{MR}=v_h-\frac{\beta v_h+(1-\beta)y-w}{(1-\gamma)\beta}.$$
--   Strategy F is *optimal* if $\Pi^F\ge\max(\Pi^M,\Pi^{FR},\Pi^{MR})$, and MR is optimal if $\Pi^{MR}\ge\max(\Pi^F,\Pi^M,\Pi^{FR})$. F induces the *smallest consumer surplus* if $CS^F\le\min(CS^{MR},CS^M,CS^{FR})$, and MR the largest if $CS^{MR}\ge\max(CS^F,CS^M,CS^{FR})$.
--
--   These objects are the vocabulary of every statement of the mission: the strategy map in $(m,\alpha)$ and the comparison between profit and consumer surplus.
--
--   **Formalization Note** The retailer–distributor pricing game (eqs. (1)–(2), the IC/IR constraints) is not re-derived: its outcome, Proposition B.1, is taken as the model. $r_\alpha(m)$ keeps its positive part, so $m-r_\alpha(m)$ replaces the proofs' log term wherever Proposition B.1 has it, including in $y_\theta$. FR's tie-break invests the leftover budget iff $y\le y_\theta$, which is the proof's $\mathbb 1\{y\le y_\theta\}$ (p. 39); Theorem 1's text has a strict inequality. The subsidy bound is $x\le v_h-m$, as in Proposition B.1 and the proof of Theorem 1. Profits are evaluated at the allocations, never taken as the closed forms (16)–(17). The low valuation $v_l$ and the heterogeneous-ATP model of §5 do not enter. Added relative to the page: $0\le m$ (ATP is nonnegative, so the refund does not exceed the price), $m<v_h$, $\gamma<1$, $0<\theta_0<1$, $c_\theta>0$, $b>0$, and strictness in Assumption 1. Without these some formulas divide by zero, or the F and M allocations coincide.
-- source:
--   Calmon, Jue-Rajasingh, Romero & Stenson, Operational strategies for distributing durable goods in the base of the pyramid, accepted manuscript (M&SOM 24(4), 2022; TSpace, SSRN 2882402), pp. 6–16, 35–44 (PDF 7–17, 36–45), §3, Assumption 1, eq. (3), Proposition B.1, Theorem 1 and its proof, p. 16 (w̄, c̄θ), proofs of Properties 1 and 5

import Mathlib

namespace BOPDistrib.Misalign

/-- Parameters of the homogeneous-ATP model of Calmon, Jue-Rajasingh, Romero & Stenson (§3–§4):
high valuation `vh`, fraction `β` of high-valuation customers, wholesale cost `w`, salvage value `y`,
marginal cost `cθ` of customer education, budget per customer `b`, initial education level `θ0`,
and the distributor's weight `γ` on consumer surplus. The low valuation `v_l` does not enter once the
pricing stage is Proposition B.1's outcome, so it is not a field. The ATP `m` and the risk aversion
`α` are explicit arguments of every object below. -/
structure Params where
  vh : ℝ
  β : ℝ
  w : ℝ
  y : ℝ
  cθ : ℝ
  b : ℝ
  θ0 : ℝ
  γ : ℝ

variable (P : Params)

/-- Standing assumptions at ATP `m`: `0 < v_h`; `0 < β < 1` (p. 35); `w ≤ m < v_h`
(Prop. B.1 `m ∈ [w, v_h]`, p. 9 `w ≤ m`; `0 ≤ m` and `m < v_h` added); `0 ≤ γ < 1`
(p. 10 `γ ≥ 0`; `γ < 1` added); `0 < θ0 < 1` and `0 < cθ` (added); and Assumption 1 in its
homogeneous form, made strict and with `b > 0`: `0 < b < cθ(1 − θ0) + β(v_h − m)` (p. 11). -/
def Standing (m : ℝ) : Prop :=
  0 < P.vh ∧ 0 < P.β ∧ P.β < 1 ∧ 0 ≤ m ∧ P.w ≤ m ∧ m < P.vh ∧ 0 ≤ P.γ ∧ P.γ < 1 ∧
    0 < P.θ0 ∧ P.θ0 < 1 ∧ 0 < P.cθ ∧ 0 < P.b ∧ P.b < P.cθ * (1 - P.θ0) + P.β * (P.vh - m)

/-- The log term `(1/α) ln((1 − β e^{−α(v_h − m)})/(1 − β))` of eq. (3) (p. 12). -/
noncomputable def logTerm (m α : ℝ) : ℝ :=
  (1 / α) * Real.log ((1 - P.β * Real.exp (-α * (P.vh - m))) / (1 - P.β))

/-- The minimum refund `r_α(m) = max(0, m − (1/α) ln((1 − β e^{−α(v_h−m)})/(1 − β)))`
(eq. (3), p. 12; Proposition B.1(b), p. 35). -/
noncomputable def refund (m α : ℝ) : ℝ :=
  max 0 (m - logTerm P m α)

/-- Consumer surplus under pricing strategy (a) of Proposition B.1: `CS^a = (v_h − m)θβ`. -/
def CSA (m θ : ℝ) : ℝ := (P.vh - m) * θ * P.β

/-- Distributor profit under pricing strategy (a): `Π^a_D(x, θ) = (m + x − w)θβ + γ CS^a`. -/
def PiA (m x θ : ℝ) : ℝ := (m + x - P.w) * θ * P.β + P.γ * CSA P m θ

/-- Consumer surplus under pricing strategy (b): `CS^b = (v_h − m)β − (m − r_α(m))(1 − θ)(1 − β)`. -/
noncomputable def CSB (m α θ : ℝ) : ℝ :=
  (P.vh - m) * P.β - (m - refund P m α) * (1 - θ) * (1 - P.β)

/-- Distributor profit under pricing strategy (b):
`Π^b_D(x, θ) = (m + x − w)β + (1 − β)(m + x − r_α(m) − w + y)(1 − θ) + γ CS^b`. -/
noncomputable def PiB (m α x θ : ℝ) : ℝ :=
  (m + x - P.w) * P.β + (1 - P.β) * (m + x - refund P m α - P.w + P.y) * (1 - θ) +
    P.γ * CSB P m α θ

/-- Feasible allocations of the Allocation Problem (p. 10) under pricing strategy (a), whose demand is
`B = θβ`: `θ0 ≤ θ ≤ 1`, `0 ≤ x ≤ v_h − m`, `cθ(θ − θ0) + xθβ ≤ b`. -/
def FeasA (m x θ : ℝ) : Prop :=
  P.θ0 ≤ θ ∧ θ ≤ 1 ∧ 0 ≤ x ∧ x ≤ P.vh - m ∧ P.cθ * (θ - P.θ0) + x * (θ * P.β) ≤ P.b

/-- Feasible allocations under pricing strategy (b), whose demand is `B = β + (1 − θ)(1 − β)`. -/
def FeasB (m x θ : ℝ) : Prop :=
  P.θ0 ≤ θ ∧ θ ≤ 1 ∧ 0 ≤ x ∧ x ≤ P.vh - m ∧
    P.cθ * (θ - P.θ0) + x * (P.β + (1 - θ) * (1 - P.β)) ≤ P.b

/-- `1/x^{++}`: `0` if `x ≤ 0` and `1/x` if `x > 0` (p. 40). -/
noncomputable def invPP (t : ℝ) : ℝ := if 0 < t then 1 / t else 0

/-- `θ^F = θ0 + (b − θ0β(v_h − m))^+ / (cθ + β(v_h − m))` (proof of Theorem 1, p. 38). -/
noncomputable def thetaF (m : ℝ) : ℝ :=
  P.θ0 + max 0 (P.b - P.θ0 * P.β * (P.vh - m)) / (P.cθ + P.β * (P.vh - m))

/-- `x^F = min(v_h − m, b/(θ0β))` (p. 38). -/
noncomputable def xF (m : ℝ) : ℝ := min (P.vh - m) (P.b / (P.θ0 * P.β))

/-- `θ^M = min(1, θ0 + b/cθ)` (p. 38). -/
noncomputable def thetaM : ℝ := min 1 (P.θ0 + P.b / P.cθ)

/-- `x^M = (b − cθ(1 − θ0))^+ / β` (p. 38). -/
noncomputable def xM : ℝ := max 0 (P.b - P.cθ * (1 - P.θ0)) / P.β

/-- `θ^MR = min(1, θ0 + b/cθ)` (p. 39). -/
noncomputable def thetaMR : ℝ := min 1 (P.θ0 + P.b / P.cθ)

/-- `x^MR = (b − cθ(1 − θ0))^+ / β` (p. 39). -/
noncomputable def xMR : ℝ := max 0 (P.b - P.cθ * (1 - P.θ0)) / P.β

/-- The threshold `y_θ = w − (1 − γ)(m − r_α(m)) − (v_h − m)` (p. 39, with `m − r_α(m)` in place of
the log term, as in Proposition B.1). -/
noncomputable def yθ (m α : ℝ) : ℝ := P.w - (1 - P.γ) * (m - refund P m α) - (P.vh - m)

/-- `θ^FR = θ0 + (b − (v_h − m)(β + (1 − θ0)(1 − β)))^+ · 1/(cθ − (v_h − m)(1 − β))^{++} · 1{y ≤ y_θ}`
(p. 40). -/
noncomputable def thetaFR (m α : ℝ) : ℝ :=
  P.θ0 + max 0 (P.b - (P.vh - m) * (P.β + (1 - P.θ0) * (1 - P.β))) *
    invPP (P.cθ - (P.vh - m) * (1 - P.β)) * (if P.y ≤ yθ P m α then 1 else 0)

/-- `x^FR = min(v_h − m, b/(β + (1 − θ0)(1 − β)))` (p. 40). -/
noncomputable def xFR (m : ℝ) : ℝ := min (P.vh - m) (P.b / (P.β + (1 - P.θ0) * (1 - P.β)))

/-- Strategy profits, evaluated at the allocations (not closed forms): `Π^F = Π^a_D(x^F, θ^F)`. -/
noncomputable def PiF (m : ℝ) : ℝ := PiA P m (xF P m) (thetaF P m)
/-- `Π^M = Π^a_D(x^M, θ^M)`. -/
noncomputable def PiM (m : ℝ) : ℝ := PiA P m (xM P) (thetaM P)
/-- `Π^FR = Π^b_D(x^FR, θ^FR)`. -/
noncomputable def PiFR (m α : ℝ) : ℝ := PiB P m α (xFR P m) (thetaFR P m α)
/-- `Π^MR = Π^b_D(x^MR, θ^MR)`. -/
noncomputable def PiMR (m α : ℝ) : ℝ := PiB P m α (xMR P) (thetaMR P)

/-- Consumer surplus of each strategy: `CS^F = CS^a(θ^F)`. -/
noncomputable def CSF (m : ℝ) : ℝ := CSA P m (thetaF P m)
/-- `CS^M = CS^a(θ^M)`. -/
noncomputable def CSM (m : ℝ) : ℝ := CSA P m (thetaM P)
/-- `CS^FR = CS^b(θ^FR)`. -/
noncomputable def CSFR (m α : ℝ) : ℝ := CSB P m α (thetaFR P m α)
/-- `CS^MR = CS^b(θ^MR)`. -/
noncomputable def CSMR (m α : ℝ) : ℝ := CSB P m α (thetaMR P)

/-- `w̄ = βv_h + (1 − β)y` (p. 16). -/
def wbar : ℝ := P.β * P.vh + (1 - P.β) * P.y
/-- `c̄θ = (1 − β)(w − y)` (p. 16). -/
def cθbar : ℝ := (1 - P.β) * (P.w - P.y)
/-- `m^F = (cθ/β + w − γv_h)/(1 − γ)` (proof of Property 1, p. 41). -/
noncomputable def mF : ℝ := (P.cθ / P.β + P.w - P.γ * P.vh) / (1 - P.γ)
/-- `m^MR = v_h − ((1 − β)(w − y) − cθ)/((1 − γ)β)` (proof of Property 5, p. 44). -/
noncomputable def mMR : ℝ := P.vh - ((1 - P.β) * (P.w - P.y) - P.cθ) / ((1 - P.γ) * P.β)
/-- `m̄^MR = v_h − (βv_h + (1 − β)y − w)/((1 − γ)β)` (p. 44). -/
noncomputable def mMRbar : ℝ := P.vh - (P.β * P.vh + (1 - P.β) * P.y - P.w) / ((1 - P.γ) * P.β)

/-- Strategy F is optimal: `Π^F ≥ max(Π^M, Π^FR, Π^MR)`. -/
def FOpt (m α : ℝ) : Prop := max (PiM P m) (max (PiFR P m α) (PiMR P m α)) ≤ PiF P m
/-- Strategy MR is optimal: `Π^MR ≥ max(Π^F, Π^M, Π^FR)`. -/
def MROpt (m α : ℝ) : Prop := max (PiF P m) (max (PiM P m) (PiFR P m α)) ≤ PiMR P m α
/-- Strategy F induces the smallest consumer surplus: `CS^F ≤ min(CS^MR, CS^M, CS^FR)`. -/
def FMinCS (m α : ℝ) : Prop := CSF P m ≤ min (CSMR P m α) (min (CSM P m) (CSFR P m α))
/-- Strategy MR induces the largest consumer surplus: `CS^MR ≥ max(CS^F, CS^M, CS^FR)`. -/
def MRMaxCS (m α : ℝ) : Prop := max (CSF P m) (max (CSM P m) (CSFR P m α)) ≤ CSMR P m α

end BOPDistrib.Misalign


