-- Prove2me | Definitions.Def_FlexApproval_Statics_Model
-- name    : FlexApproval_Statics_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:35:53.296892+00:00
-- url     : https://prove2.me/theorems/73b843ba-7f4a-4522-b4eb-1a14448a9a1a
-- title:
--   §3.2, §4.1, pp. 9–12 — drug-approval model: Gaussian power curve, thinned approval rates, M/M/1/1 market means, expected net benefit V(α), optimal policies
-- statement:
--   This file fixes the model of Bravo, Corcoran and Long, in which a regulator chooses the significance level $\alpha$ of the efficacy test applied to candidate drugs.
--
--   **Parameters.** A parameter vector consists of the prior probability $p$ that a candidate drug is effective; the treatment effect $\delta$, the outcome standard deviation $\sigma$ and the number $n$ of patients per trial arm; the arrival rate $\lambda$ of drugs into clinical trials, the trial completion rate $\mu_{CT}$ and the abandonment rate $\mu_{AB}$; the market exit rates $\mu_E$ (effective drugs) and $\mu_I$ (ineffective drugs); the number $K\ge1$ of therapeutic classes; the health benefit $Q_E$ per effective and the health cost $Q_I$ per ineffective drug on the market; the monetary gain $C_{AE}$ of approving an effective drug and the losses $C_{AI}$, $C_{RE}$ of approving an ineffective and rejecting an effective drug; and the willingness to pay $\mathrm{WTP}$ per QALY.
--
--   **Approval probabilities** (1). With the information $I_n=n/(2\sigma^2)$ and the standard normal CDF $\Phi$,
--   $$\pi_{AE}(\alpha)=\big[1-\Phi(\Phi^{-1}(1-\alpha)-\delta\sqrt{I_n})\big]p,\quad \pi_{AI}(\alpha)=\alpha(1-p),\quad \pi_{RE}(\alpha)=\Phi(\Phi^{-1}(1-\alpha)-\delta\sqrt{I_n})\,p,\quad \pi_{RI}(\alpha)=(1-\alpha)(1-p).$$
--
--   **Rates** (2). Drugs reach FDA review at rate $\tilde\lambda=\lambda\mu_{CT}/(\mu_{CT}+\mu_{AB})$, and $\lambda_{XY}(\alpha)=\tilde\lambda\,\pi_{XY}(\alpha)$ for $XY\in\{AE,AI,RE,RI\}$.
--
--   **Market** (4). With $\psi_E(\alpha)=\lambda_{AE}(\alpha)/(K\mu_E)$ and $\psi_I(\alpha)=\lambda_{AI}(\alpha)/\mu_I$, the expected numbers of effective and ineffective drugs on the market are
--   $$\mathbb E[N_E(\alpha)]=\frac{K\psi_E(\alpha)}{1+\psi_E(\alpha)},\qquad \mathbb E[N_I(\alpha)]=\psi_I(\alpha).$$
--
--   **Objective** (3). The expected net benefit is
--   $$V(\alpha)=\big(Q_E\,\mathbb E[N_E(\alpha)]-Q_I\,\mathbb E[N_I(\alpha)]\big)\mathrm{WTP}+C_{AE}\lambda_{AE}(\alpha)-C_{AI}\lambda_{AI}(\alpha)-C_{RE}\lambda_{RE}(\alpha),$$
--   and $a$ is an **optimal approval policy** when $a\in[0,1]$ and $V(b)\le V(a)$ for every $b\in[0,1]$.
--
--   **Standing assumptions.** $0<p<1$, $\delta>0$, $\sigma>0$, $n\ge1$, $\lambda,\mu_{CT},\mu_{AB},\mu_E,\mu_I>0$, $K\ge1$, $\mathrm{WTP}>0$, $Q_E>0$, $Q_I,C_{AE},C_{AI},C_{RE}\ge0$ and $C_{AI}+\mathrm{WTP}\,Q_I/\mu_I>0$.
--
--   These are the objects of Theorem 1 and Proposition 1 of the paper.
--
--   **Formalization Note** $\Phi$ and $\Phi^{-1}$ (on $(0,1)$) are the published `Cohen2019.Robust.Phi` and `PhiInvReal`. The power curve $\alpha\mapsto 1-\Phi(\Phi^{-1}(1-\alpha)-\delta\sqrt{I_n})$ is defined piecewise: the printed formula for $0<\alpha<1$, and its limits $0$ at $\alpha=0$ and $1$ at $\alpha=1$ (the page's $\Phi^{-1}(1)=+\infty$, $\Phi^{-1}(0)=-\infty$), so that $V$ is the continuous extension to $[0,1]$. The auxiliary function `gp` is the factor $e^{\Phi^{-1}(1-\alpha)\delta\sqrt{I_n}-\delta^2 I_n/2}$ printed in (A.19)–(A.20), the derivative of the power curve on $(0,1)$. The formulas (4) are the paper's steady-state means of $K$ preemptive M/M/1/1 queues and an M/M/∞ queue; they are taken as definitions and the queueing derivation is not formalized. The paper lists no standing assumptions; the list above collects the ranges of Table 1 and the sign conditions its proofs use (concavity of $C_{AE}\lambda_{AE}$ and $-C_{RE}\lambda_{RE}$ needs $C_{AE},C_{RE}\ge0$; without $C_{AI}+\mathrm{WTP}\,Q_I/\mu_I>0$ the optimum is $\alpha=1$ and the logarithm in (5) is $\log 0$). The optimal policy is a predicate, not defined by the first-order condition (5). $n$ and $K$ are natural numbers; everything else is real.
-- source:
--   Bravo, Corcoran & Long, Flexible Drug Approval Policies, SSRN working paper 3027263 (version of 17 Jul 2019), pp. 9–12, §3.2, §4.1, Eqs. (1)–(4), Table 1 (p. 11); factor of (A.19)–(A.20), pp. 33–34

import Mathlib
import Definitions.Def_Cohen2019_Robust_Phi

namespace FlexApproval.Statics

open Cohen2019.Robust

/-! # The drug-approval model of Bravo, Corcoran and Long

F. Bravo, T. C. Corcoran, E. F. Long, *Flexible Drug Approval Policies*, SSRN working paper 3027263
(version of 17 Jul 2019): the joint probabilities (1) of §3.2, p. 9, the thinned approval rates (2)
of §4.1, p. 10, the steady-state market means (4) and the expected net benefit `V(α)` of (3),
p. 12. `Phi` is the standard normal CDF and `PhiInvReal` its inverse on `(0, 1)`, both from the
published `Cohen2019.Robust.Phi`. -/

/-- The power curve `α ↦ 1 − Φ(Φ⁻¹(1 − α) − θ)` of (1), p. 9, with `θ = δ√I_n`: the probability that
an effective drug is approved at significance level `α`. On `0 < α < 1` it is the printed formula.
At the endpoints the page's `Φ⁻¹(1) = +∞` and `Φ⁻¹(0) = −∞` give the limits `0` (at `α = 0`) and
`1` (at `α = 1`); the definition takes these values there (and outside `[0, 1]`, where it is never
used), instead of the junk real value of `PhiInvReal` at `0` and `1`. -/
noncomputable def pw (θ α : ℝ) : ℝ :=
  if α ≤ 0 then 0 else if 1 ≤ α then 1 else 1 - Phi (PhiInvReal (1 - α) - θ)

/-- The factor `e^{Φ⁻¹(1−α)θ − θ²/2}` printed in (A.19)–(A.20), p. 33–34, with `θ = δ√I_n`; on
`0 < α < 1` it is the derivative of the power curve `pw θ` in `α`. Only used for `0 < α < 1`. -/
noncomputable def gp (θ α : ℝ) : ℝ :=
  Real.exp (θ * PhiInvReal (1 - α) - θ ^ 2 / 2)

/-- The parameters of the model (Table 1, p. 11): the prior probability `p` that a candidate drug
is effective; the treatment effect `delta` (δ), the standard deviation `sigma` (σ) and the number
`n` of patients per arm of the trial (§3.2); the arrival rate `lam` (λ) of candidate drugs, the
trial completion rate `muCT` and the trial abandonment rate `muAB`; the market exit rates `muE` of
effective and `muI` of ineffective drugs; the number `K` of therapeutic classes; the health benefit
`QE` per effective and health cost `QI` per ineffective drug on the market; the monetary gain `CAE`
of approving an effective drug and the losses `CAI` (approving an ineffective drug) and `CRE`
(rejecting an effective drug); the willingness to pay `WTP` per QALY. -/
structure Params where
  p : ℝ
  delta : ℝ
  sigma : ℝ
  n : ℕ
  lam : ℝ
  muCT : ℝ
  muAB : ℝ
  muE : ℝ
  muI : ℝ
  K : ℕ
  QE : ℝ
  QI : ℝ
  CAE : ℝ
  CAI : ℝ
  CRE : ℝ
  WTP : ℝ

/-- Standing assumptions. The paper does not list them; they are the ranges of Table 1 (p. 11) and
§3.2 (p. 9, `H₁ : δ > 0`), together with the sign conditions its proofs use:
`0 < p < 1`, `δ > 0`, `σ > 0`, `n ≥ 1`, all rates positive, `K ≥ 1`, `WTP > 0`, `QE > 0`,
`QI, CAE, CAI, CRE ≥ 0` and `CAI + WTP·QI/µI > 0` (the numerator inside the logarithm of (5)). -/
def Params.Standing (P : Params) : Prop :=
  0 < P.p ∧ P.p < 1 ∧ 0 < P.delta ∧ 0 < P.sigma ∧ 1 ≤ P.n ∧
  0 < P.lam ∧ 0 < P.muCT ∧ 0 < P.muAB ∧ 0 < P.muE ∧ 0 < P.muI ∧ 1 ≤ P.K ∧
  0 < P.WTP ∧ 0 < P.QE ∧ 0 ≤ P.QI ∧ 0 ≤ P.CAE ∧ 0 ≤ P.CAI ∧ 0 ≤ P.CRE ∧
  0 < P.CAI + P.WTP * P.QI / P.muI

/-- The information of the sample, `I_n = n / (2σ²)` (§3.2, p. 9). -/
noncomputable def In (P : Params) : ℝ := (P.n : ℝ) / (2 * P.sigma ^ 2)

/-- `θ = δ√I_n`, the mean of the Wald statistic under `H₁` (§3.2, p. 9). -/
noncomputable def theta (P : Params) : ℝ := P.delta * Real.sqrt (In P)

/-- Joint probabilities (1), p. 9: approved effective, approved ineffective, rejected effective,
rejected ineffective. -/
noncomputable def piAE (P : Params) (α : ℝ) : ℝ := pw (theta P) α * P.p
noncomputable def piAI (P : Params) (α : ℝ) : ℝ := α * (1 - P.p)
noncomputable def piRE (P : Params) (α : ℝ) : ℝ := (1 - pw (theta P) α) * P.p
noncomputable def piRI (P : Params) (α : ℝ) : ℝ := (1 - α) * (1 - P.p)

/-- The net rate `λ̃ = λ µ_CT / (µ_CT + µ_AB)` at which drugs enter FDA review (§4.1, p. 10). -/
noncomputable def lamTilde (P : Params) : ℝ := P.lam * P.muCT / (P.muCT + P.muAB)

/-- The thinned rates (2), p. 10: `λ_XY(α) = λ̃ π_XY(α)`. -/
noncomputable def lamAE (P : Params) (α : ℝ) : ℝ := lamTilde P * piAE P α
noncomputable def lamAI (P : Params) (α : ℝ) : ℝ := lamTilde P * piAI P α
noncomputable def lamRE (P : Params) (α : ℝ) : ℝ := lamTilde P * piRE P α
noncomputable def lamRI (P : Params) (α : ℝ) : ℝ := lamTilde P * piRI P α

/-- `ψ_E(α) = λ_AE(α) / (K µ_E)` and `ψ_I(α) = λ_AI(α) / µ_I` (p. 12). -/
noncomputable def psiE (P : Params) (α : ℝ) : ℝ := lamAE P α / ((P.K : ℝ) * P.muE)
noncomputable def psiI (P : Params) (α : ℝ) : ℝ := lamAI P α / P.muI

/-- The expected numbers of effective and ineffective drugs on the market, (4), p. 12:
`E[N_E(α)] = K ψ_E(α) / (1 + ψ_E(α))` and `E[N_I(α)] = ψ_I(α)`. The paper states these as the
steady-state means of `K` parallel preemptive M/M/1/1 queues and of an M/M/∞ queue; they are taken
here as definitions. -/
noncomputable def ENE (P : Params) (α : ℝ) : ℝ := (P.K : ℝ) * psiE P α / (1 + psiE P α)
noncomputable def ENI (P : Params) (α : ℝ) : ℝ := psiI P α

/-- The expected net benefit (p. 12):
`V(α) = (Q_E E[N_E(α)] − Q_I E[N_I(α)]) WTP + (C_AE λ_AE(α) − C_AI λ_AI(α) − C_RE λ_RE(α))`. -/
noncomputable def V (P : Params) (α : ℝ) : ℝ :=
  (P.QE * ENE P α - P.QI * ENI P α) * P.WTP +
    (P.CAE * lamAE P α - P.CAI * lamAI P α - P.CRE * lamRE P α)

/-- `a` is an optimal approval policy (3), p. 12: `a ∈ [0, 1]` maximizes `V` over `[0, 1]`. -/
def IsOptimal (P : Params) (a : ℝ) : Prop :=
  a ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ b ∈ Set.Icc (0 : ℝ) 1, V P b ≤ V P a

end FlexApproval.Statics


