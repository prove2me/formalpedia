-- Prove2me | Definitions.Def_PrivacyQueue_Control_Model
-- name    : PrivacyQueue_Control_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:24.094629+00:00
-- url     : https://prove2.me/theorems/c8020914-6d1f-445d-9b43-155c20fbae60
-- title:
--   §3 and Online Appendix A.1 — disclosure-dependent three-class priority queue and customer surplus
-- statement:
--   Customers arrive at rate $\lambda>0$ to a single server. A request is type $H$ with probability $\alpha\in[0,1]$ and has exponential mean service time $1/\mu$; otherwise it is type $L$ with mean $1/(\sigma\mu)$. The server ranks disclosed $H$ requests above undisclosed $N$ requests above disclosed $L$ requests. The disclosure probability is $\gamma\in[0,1]$, and the mixed-service capacity is
--
--   $$\bar\mu=\frac{\sigma\mu}{1+\alpha(\sigma-1)}.$$
--
--   The model uses the service-time, residual-time, and load table of Online Appendix A.1 to instantiate the three-class waiting-time formulas. Disclosure and withholding utilities and total customer surplus are
--
--   $$U_d(\gamma,\lambda)=R-c\bigl(\alpha W_H+(1-\alpha)W_L\bigr),\quad U_w(\gamma,\lambda)=R-cW_N,$$
--   $$CS(\gamma)=\lambda\bigl(\gamma U_d(\gamma,\lambda)+(1-\gamma)U_w(\gamma,\lambda)\bigr).$$
--
--   Customer control uses $CS_{\rm control}=CS(\gamma^*)$ at an equilibrium $\gamma^*$; compulsory disclosure uses $CS_{\rm discl}=\lambda U_d(1,\lambda)$. An endpoint equilibrium follows the paper's strict utility comparison at $0$ or $1$. An interior equilibrium has equal utilities and a locally decreasing utility difference.
--
--   **Formalization Note** All quantities are real. The standing assumptions include $\mu>0$, $\sigma>0$, $\sigma\ne1$, $\lambda>0$, $\lambda<\bar\mu$, $c>0$, and $R\ge c/\bar\mu$. Strict positivity of $\mu$, $\lambda$, and $c$ makes the rate, fraction, and strict comparison conventions explicit. Waiting times are supplied by the paper's formulas; no stochastic process is represented.
-- source:
--   Hu, Momot & Wang, Privacy Management in Service Systems, submitted manuscript (draft of 12 Feb 2022; SSRN 3628751), pp. 8–12 (PDF 9–13), §3.2–§3.4, Eq. (1); Online Appendix p. 1 (PDF 35), A.1; Online Appendix p. 3 (PDF 37), Eq. (9)

import Mathlib
import Definitions.Def_PrivacyQueue_Control_PriorityQueue3

namespace PrivacyQueue.Control

/-- Parameters of the two-type disclosure and single-server priority model. -/
structure Params where
  mu : ℝ
  σ : ℝ
  α : ℝ
  lam : ℝ
  c : ℝ
  R : ℝ

/-- Effective capacity of the mixed service population. -/
noncomputable def Params.mubar (P : Params) : ℝ :=
  P.σ * P.mu / (1 + P.α * (P.σ - 1))

/-- Standing assumptions from §3.2, with strictly positive rates and cost. -/
noncomputable def Params.Standing (P : Params) : Prop :=
  0 < P.mu ∧ 0 < P.σ ∧ P.σ ≠ 1 ∧ 0 ≤ P.α ∧ P.α ≤ 1 ∧
  0 < P.lam ∧ P.lam < P.mubar ∧ 0 < P.c ∧ P.c / P.mubar ≤ P.R

/-- Expected service time of a disclosed type-H request. -/
noncomputable def BH (P : Params) : ℝ := 1 / P.mu
/-- Expected service time of an undisclosed request. -/
noncomputable def BN (P : Params) : ℝ :=
  (1 + P.α * (P.σ - 1)) / (P.σ * P.mu)
/-- Expected service time of a disclosed type-L request. -/
noncomputable def BL (P : Params) : ℝ := 1 / (P.σ * P.mu)
/-- Expected residual time of a type-H request. -/
noncomputable def RH (P : Params) : ℝ := 1 / P.mu
/-- Expected residual time of a type-N hyperexponential request. -/
noncomputable def RN (P : Params) : ℝ :=
  (P.α * (1 / P.mu ^ 2) + (1 - P.α) * (1 / (P.σ * P.mu) ^ 2)) /
    (P.α * (1 / P.mu) + (1 - P.α) * (1 / (P.σ * P.mu)))
/-- Expected residual time of a type-L request. -/
noncomputable def RL (P : Params) : ℝ := 1 / (P.σ * P.mu)

/-- Workload of disclosed H requests. -/
noncomputable def rhoH (P : Params) (γ : ℝ) : ℝ :=
  P.α * γ * P.lam / P.mu
/-- Workload of undisclosed N requests. -/
noncomputable def rhoN (P : Params) (γ : ℝ) : ℝ :=
  (1 + P.α * (P.σ - 1)) * (1 - γ) * P.lam / (P.σ * P.mu)
/-- Workload of disclosed L requests. -/
noncomputable def rhoL (P : Params) (γ : ℝ) : ℝ :=
  (1 - P.α) * γ * P.lam / (P.σ * P.mu)

/-- The paper's three classes as an instance of the priority queue formula. -/
noncomputable def Params.queue (P : Params) (γ : ℝ) : PriorityQueue3 where
  BH := BH P
  BN := BN P
  BL := BL P
  RH := RH P
  RN := RN P
  RL := RL P
  rhoH := rhoH P γ
  rhoN := rhoN P γ
  rhoL := rhoL P γ

/-- Type-H expected time in the system. -/
noncomputable def WH (P : Params) (γ : ℝ) : ℝ := (P.queue γ).waitH
/-- Type-N expected time in the system. -/
noncomputable def WN (P : Params) (γ : ℝ) : ℝ := (P.queue γ).waitN
/-- Type-L expected time in the system. -/
noncomputable def WL (P : Params) (γ : ℝ) : ℝ := (P.queue γ).waitL

/-- Utility of disclosing before the customer's type is known. -/
noncomputable def Ud (P : Params) (γ : ℝ) : ℝ :=
  P.R - P.c * (P.α * WH P γ + (1 - P.α) * WL P γ)
/-- Utility of withholding the customer's type. -/
noncomputable def Uw (P : Params) (γ : ℝ) : ℝ :=
  P.R - P.c * WN P γ
/-- Total customer surplus at disclosure probability γ. -/
noncomputable def CS (P : Params) (γ : ℝ) : ℝ :=
  P.lam * (γ * Ud P γ + (1 - γ) * Uw P γ)
/-- Surplus under customer control at an equilibrium disclosure probability. -/
noncomputable def CScontrol (P : Params) (γs : ℝ) : ℝ :=
  P.lam * (γs * Ud P γs + (1 - γs) * Uw P γs)
/-- Surplus under mandatory full disclosure. -/
noncomputable def CSdiscl (P : Params) : ℝ := P.lam * Ud P 1

/-- The paper's endpoint and stable interior disclosure equilibria. -/
noncomputable def IsEquilibrium (P : Params) (γs : ℝ) : Prop :=
  (γs = 0 ∧ Ud P 0 < Uw P 0) ∨
  (γs = 1 ∧ Uw P 1 < Ud P 1) ∨
  (0 < γs ∧ γs < 1 ∧ Ud P γs = Uw P γs ∧
    ∃ ε : ℝ, 0 < ε ∧
      StrictAntiOn (fun γ => Ud P γ - Uw P γ) (Set.Ioo (γs - ε) (γs + ε)))

/-- Auxiliary rational function Γ from the proof of Lemma 4. -/
noncomputable def Gam (P : Params) (γ : ℝ) : ℝ :=
  γ * P.lam * (1 - P.α * (1 + P.σ)) +
    (P.σ * P.mu - (1 - P.α) * P.lam) +
    P.σ ^ 2 * (P.mu - P.α * P.lam) ^ 2 /
      (γ * P.lam * (1 - P.α - P.α * P.σ) +
       (P.σ * P.mu - (1 - P.α) * P.lam))

end PrivacyQueue.Control


