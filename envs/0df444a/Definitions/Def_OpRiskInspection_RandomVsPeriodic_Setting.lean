-- Prove2me | Definitions.Def_OpRiskInspection_RandomVsPeriodic_Setting
-- name    : OpRiskInspection_RandomVsPeriodic_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T02:31:15.691711+00:00
-- url     : https://prove2.me/theorems/82eac5a2-28be-48aa-be99-9bd810e5a6f6
-- title:
--   §3, pp. 7–10, and (21), p. 19 — model parameters, Assumption 1, inspection-interval laws, payoffs (1), (3), (6), best response (2), achievable payoffs (4)–(5)
-- statement:
--   This file sets up the continuous-time principal–agent model of operational-risk inspection of Kim and Xu.
--
--   **Parameters.** A firm (the principal) earns base profit $\mu>0$ per unit time and discounts at rate $r>0$. Its employee (the agent) exerts effort $a_t\ge 0$ at unit cost $c>0$. Errors arrive at rate $\lambda e^{-a_t}$, where $\lambda>0$ is the aggregate base error rate, and each error costs the firm $L>0$ per unit time until an inspection finds it. The agent's reservation payoff is $\bar\pi>0$, and $\bar\mu:=\mu-r\bar\pi$. The standing assumptions are the positivity of $r,c,\lambda,L,\mu,\bar\pi$ and Assumption 1:
--   $$c<\frac{L\lambda}{r}<\bar\mu .$$
--   The inspection cost $K>0$ is not part of the parameter record, since the results vary it.
--
--   **Effort and errors.** An effort path $a$ assigns an effort $a_t\ge0$ to each time $t$ since the last inspection; it is the same in every inspection cycle, and it is required to be measurable and bounded. The expected number of errors made by time $t$ is
--   $$\mathbb E[N^a_t]=\lambda\int_0^t e^{-a_s}\,ds .$$
--
--   **Inspection intervals.** With frequency $v>0$, the interval $\tau$ between two inspections has law
--   1. random policy $R$: $\tau\sim\mathrm{Exp}(v)$;
--   2. periodic policy $D$: $\tau=1/v$;
--   3. hybrid policy $H(q)$, $q\in[0,1]$: $\tau=q/v$ with probability $q$, and otherwise $\tau=q/v+\mathrm{Exp}(v)$, which is the CDF (21).
--
--   **Payoffs.** For a law of $\tau$, penalty $P$ per error found and wage $w$, the agent's payoff (1), the principal's payoff (3) and the reduced payoff (6) are
--   $$\pi_I(a;v,P,w)=\frac wr-c\,\frac{\mathbb E_I[\int_0^\tau a_te^{-rt}dt]}{1-\mathbb E_I[e^{-r\tau}]}-P\,\frac{\mathbb E_I[N^a_\tau e^{-r\tau}]}{1-\mathbb E_I[e^{-r\tau}]},$$
--   $$\Pi_I(v,P,w)=\frac{\mu-w}r-L\,\frac{\mathbb E_I[\int_0^\tau N^{a}_te^{-rt}dt]}{1-\mathbb E_I[e^{-r\tau}]}+P\,\frac{\mathbb E_I[N^a_\tau e^{-r\tau}]}{1-\mathbb E_I[e^{-r\tau}]}-\frac{K}{e^{r/v}-1},$$
--   $$V_I(v,P)=\frac{\bar\mu}r-c\,\frac{\mathbb E_I[\int_0^\tau a_te^{-rt}dt]}{1-\mathbb E_I[e^{-r\tau}]}-L\,\frac{\mathbb E_I[\int_0^\tau N^{a}_te^{-rt}dt]}{1-\mathbb E_I[e^{-r\tau}]}-\frac{K}{e^{r/v}-1},$$
--   where every expectation of an error count is the mean above.
--
--   **Best response and feasibility.** An effort path is an optimal response to $P$ (problem (2)) if it is admissible and its agent payoff is at least that of every admissible path. A number $x$ is an achievable payoff of a policy family if there are $v>0$, $P\ge0$, $w\ge0$ and an optimal response $a$ that meets the participation constraint (5), $\pi_I(a;v,P,w)\ge\bar\pi$, with $x=\Pi_I(v,P,w)$; for the hybrid family, $q\in[0,1]$ may also be chosen.
--
--   Every theorem of the two missions on this paper, the random-versus-periodic comparison and the hybrid dominance result, is stated on these objects.
--
--   **Formalization Note**
--   1. The model starts from the reformulated cycle payoffs (1) and (3); their derivation from the cycle sums (pp. 8–9, EC.4.1) is not formalized. The expected error count is the Poisson mean, taken independent of $\tau$; the Brownian noise has mean zero and drops out.
--   2. The $\mathcal M$ error classes are aggregated into $\lambda=\sum_m\lambda_m$ and $L=\sum_m(\lambda_m/\lambda)L_m$ (7), as the paper does from p. 10 on; the class sums in (1) and (3) collapse to these by linearity.
--   3. Effort paths are bounded and measurable, so every integral is finite; the paper writes only $a\ge0$.
--   4. The frequency is $v>0$ (the paper's (4) writes $v\ge0$, but (3) and (6) contain $1/v$ and $e^{r/v}$).
--   5. Optimality of the agent compares payoffs at wage $0$: the wage enters (1) additively, so the comparison does not depend on it.
--   6. Optimal values are not formed as suprema. A result about "the optimal payoff of policy $I$" is stated through the set of achievable payoffs, which avoids default values of a supremum over an empty or unbounded set. When the agent has several best responses, an achievable payoff may use any of them.
-- source:
--   Kim & Xu, Operational Risk Management: Optimal Inspection Policy, SSRN 3491006 (version of July 2023), pp. 7–10 and 19, (1)–(7), (21)

import Mathlib

namespace OpRiskInspection.RandomVsPeriodic

/-- Parameters of the aggregate inspection model in §3. -/
structure Params where
  r : ℝ
  c : ℝ
  lam : ℝ
  L : ℝ
  mu : ℝ
  pibar : ℝ

/-- The adjusted profit `μ̄ = μ - r π̄`. -/
def mubar (p : Params) : ℝ := p.mu - p.r * p.pibar

/-- Positivity in §3 and Assumption 1 on p. 10. -/
structure Standing (p : Params) : Prop where
  hr : 0 < p.r
  hc : 0 < p.c
  hlam : 0 < p.lam
  hL : 0 < p.L
  hmu : 0 < p.mu
  hpibar : 0 < p.pibar
  asm1a : p.c < p.L * p.lam / p.r
  asm1b : p.L * p.lam / p.r < mubar p

abbrev Effort := ℝ → ℝ

/-- Effort is a bounded measurable nonnegative function of time since the last inspection. -/
def Admissible (a : Effort) : Prop :=
  Measurable a ∧ (∀ t, 0 ≤ a t) ∧ ∃ B, ∀ t, a t ≤ B

/-- An exponential inspection interval of rate `v`. -/
noncomputable def randomLaw (v : ℝ) : MeasureTheory.Measure ℝ :=
  ProbabilityTheory.expMeasure v

/-- A deterministic inspection interval of length `1/v`. -/
noncomputable def periodicLaw (v : ℝ) : MeasureTheory.Measure ℝ :=
  MeasureTheory.Measure.dirac (1 / v)

/-- The mixture law of (21), included for the common model of the two missions. -/
noncomputable def hybridLaw (q v : ℝ) : MeasureTheory.Measure ℝ :=
  ENNReal.ofReal q • MeasureTheory.Measure.dirac (q / v) +
    ENNReal.ofReal (1 - q) •
      (ProbabilityTheory.expMeasure v).map (fun t => t + q / v)

/-- Mean number of errors up to time `t` at effort path `a`. -/
noncomputable def expCount (p : Params) (a : Effort) (t : ℝ) : ℝ :=
  p.lam * ∫ s in (0 : ℝ)..t, Real.exp (-(a s))

/-- Expected discount factor at the next inspection. -/
noncomputable def discF (p : Params) (F : MeasureTheory.Measure ℝ) : ℝ :=
  ∫ τ, Real.exp (-(p.r * τ)) ∂F

/-- Expected discounted effort spent in a cycle. -/
noncomputable def effortInt (p : Params) (F : MeasureTheory.Measure ℝ)
    (a : Effort) : ℝ :=
  ∫ τ, (∫ t in (0 : ℝ)..τ, a t * Real.exp (-(p.r * t))) ∂F

/-- Expected discounted penalty count at an inspection. -/
noncomputable def penaltyInt (p : Params) (F : MeasureTheory.Measure ℝ)
    (a : Effort) : ℝ :=
  ∫ τ, expCount p a τ * Real.exp (-(p.r * τ)) ∂F

/-- Expected discounted number of unresolved errors over a cycle. -/
noncomputable def lossInt (p : Params) (F : MeasureTheory.Measure ℝ)
    (a : Effort) : ℝ :=
  ∫ τ, (∫ t in (0 : ℝ)..τ,
    expCount p a t * Real.exp (-(p.r * t))) ∂F

/-- The agent's discounted payoff, equation (1). -/
noncomputable def agentPayoff (p : Params) (F : MeasureTheory.Measure ℝ)
    (a : Effort) (P w : ℝ) : ℝ :=
  w / p.r - p.c * effortInt p F a / (1 - discF p F) -
    P * penaltyInt p F a / (1 - discF p F)

/-- The principal's discounted payoff, equation (3). -/
noncomputable def principalPayoff (p : Params) (K v : ℝ)
    (F : MeasureTheory.Measure ℝ) (a : Effort) (P w : ℝ) : ℝ :=
  (p.mu - w) / p.r - p.L * lossInt p F a / (1 - discF p F) +
    P * penaltyInt p F a / (1 - discF p F) -
    K / (Real.exp (p.r / v) - 1)

/-- The reduced principal payoff under binding participation, equation (6). -/
noncomputable def reducedPayoff (p : Params) (K v : ℝ)
    (F : MeasureTheory.Measure ℝ) (a : Effort) : ℝ :=
  mubar p / p.r - p.c * effortInt p F a / (1 - discF p F) -
    p.L * lossInt p F a / (1 - discF p F) -
    K / (Real.exp (p.r / v) - 1)

/-- A best response to the penalty. Wage cancels in comparisons of the agent's payoff. -/
def AgentOptimal (p : Params) (F : MeasureTheory.Measure ℝ)
    (P : ℝ) (a : Effort) : Prop :=
  Admissible a ∧ ∀ a', Admissible a' →
    agentPayoff p F a' P 0 ≤ agentPayoff p F a P 0

/-- Payoffs of feasible principal strategies, equations (4)–(5). -/
def Achievable (p : Params) (K : ℝ)
    (law : ℝ → MeasureTheory.Measure ℝ) (x : ℝ) : Prop :=
  ∃ v P w a, 0 < v ∧ 0 ≤ P ∧ 0 ≤ w ∧
    AgentOptimal p (law v) P a ∧
    p.pibar ≤ agentPayoff p (law v) a P w ∧
    x = principalPayoff p K v (law v) a P w

/-- Feasible payoffs from a hybrid inspection law. -/
def AchievableHybrid (p : Params) (K x : ℝ) : Prop :=
  ∃ q, 0 ≤ q ∧ q ≤ 1 ∧ Achievable p K (hybridLaw q) x

end OpRiskInspection.RandomVsPeriodic


