-- Prove2me | Definitions.Def_BIInsurance_Screening_Model
-- name    : BIInsurance_Screening_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:43:48.834084+00:00
-- url     : https://prove2.me/theorems/21dcd402-f8d7-43ba-836e-525759af71f3
-- title:
--   §3–§5.1, pp. 6–19 — BI insurance: recovery effort, firm profits (4.4)–(4.17), the insurer's two-type screening program (5.1), (5.3)–(5.7)
-- statement:
--   This file fixes the business-interruption (BI) insurance model of Kao, Keskin and Shang (§3–§5).
--
--   **Data.** A firm has capacity $K$ and sells over $T$ periods at unit price $p$. Its early demand forecast is $\mu\in\{\mu_H,\mu_L\}$ (probability $\alpha$ of $\mu_H$), privately known; the forecast update is $\delta\in\{\delta_H,\delta_L\}$ (probability $\beta$ of $\delta_H$); demand in each period is logistic with location $\mu+\delta$ and scale $\gamma$. In period $\tau$ a disruption occurs with probability $\rho$; the firm then chooses a recovery effort $e\in[0,1]$ at cost $ceK$ and sells from capacity $eK$. An insurance contract $(y,s)$ has premium $y$ and coverage $s$; from period $\tau+w$ on, the insurer reimburses the fraction $s$ of the revenue loss. A penalty $\lambda>0$ is charged per unit of the disruption loss (net of reimbursement). The coverage set is $[0,\bar s]$.
--
--   **Standing assumptions** (`Params.Standing`): $\tau\ge1$; $K>0$; $\mu_H>\mu_L>0$; $\delta_H>0>\delta_L$ with $\beta\delta_H+(1-\beta)\delta_L=0$ and $0<\beta<1$; $0<\alpha<1$; $\gamma>0$; $0<\rho\le1$; $\lambda>0$; $p>0$, $c>0$, $(T-\tau)p\ge c$; $w<T-\tau$; $\bar s>0$ and
--   $$\bar s<1-\frac{c}{(T-\tau)p}\Big[1+\exp\!\Big(-\frac{\mu_L+\delta_L}{\gamma}\Big)\Big].$$
--
--   **Firm.** With $S(x)=E[\min(D,x)]$ the logistic expected sales for location $m=\mu+\delta$, $\xi(K,\mu,\delta)=\ln[\exp(K/\gamma)+\exp((\mu+\delta)/\gamma)]$ (4.2) and $A(s)=wp+(T-\tau-w)p(1-s)$:
--   1. $\pi^N_{0}=TpS(K)$ and $\pi^N_{1}(e)=\tau pS(K)-ceK+(T-\tau)pS(eK)-\lambda\{ceK+(T-\tau)p[S(K)-S(eK)]\}$ (4.4)–(4.6);
--   2. $\hat e=\frac1K[m+\gamma\ln\frac{(T-\tau)p-c}{c}]$ if this bracket is $<K$, else $1$ (4.7);
--   3. $\pi^I_{0}(y)=-y+TpS(K)$ and $\pi^I_{1}(e,y,s)=-y+\tau pS(K)-ceK+(T-\tau)pS(eK)+(T-\tau-w)sp[S(K)-S(eK)]-\lambda\{ceK+(T-\tau)p[S(K)-S(eK)]-(T-\tau-w)sp[S(K)-S(eK)]\}$ (4.10)–(4.12);
--   4. $e^*(s)=\frac1K[m+\gamma\ln\frac{A(s)-c}{c}]$ if this bracket is $<K$, else $1$ (4.13)–(4.14);
--   5. $E_{\delta,Z}[\pi^N_i(K)]$ and $E_{\delta,Z}[\pi^I_i(K,y,s)]$: the $\beta$/$\rho$ mixtures (4.9), (4.16), using $\hat e$ and $e^*(s)$ under disruption.
--
--   **Insurer.** A menu is $(y_H,s_H,y_L,s_L)$. The insurer maximizes
--   $$\alpha\{y_H-\rho(T-\tau-w)p\,s_H\,E_\delta[S(K)-S(e^*(s_H)K)]_{\mu_H}\}+(1-\alpha)\{y_L-\rho(T-\tau-w)p\,s_L\,E_\delta[S(K)-S(e^*(s_L)K)]_{\mu_L}\}$$
--   subject to (IC-HL), (IC-LH), (IR-H), (IR-L) and $s_H,s_L\in[0,\bar s]$ (program (5.1)); `IsOptimalMenu` is a maximizer. Further: $g_H$, $g_L$ (5.3)–(5.4); $R(s_H,s_L)$, the objective of (5.1) at $y_H=g_H(s_H)$, $y_L=g_L(s_H,s_L)$; the condition $K>\mu_H+\delta_H+\gamma\ln\frac{(T-\tau)p-c}{c}$ (`KCond`); condition (5.5) (`Cond55`, with left side `cond55LHS`); and the left sides of the first-order conditions (5.6), (5.7) (`foc56`, `foc57`), written with $[(T-\tau)(1-s)+sw]$.
--
--   **Formalization Note** Periods $T,\tau,w$ are natural numbers cast to $\mathbb R$ in every formula. The firm's functions take a general location $m=\mu+\delta$ and a general early forecast $\mu$ (Proposition 2 differentiates in $\mu$). Two hypotheses are added to the page's: $\rho>0$ (at $\rho=0$ insurance pays nothing and every coverage is optimal) and the strict $w<T-\tau$ (the page has $\bar w\le T-\tau$, p. 10); the coverage set is $[0,\bar s]$, i.e. $\underline s=0$, as in every result of the paper. One waiting period $w=w_H=w_L$ is used throughout (§3.3, p. 10). The conditions `KCond` and (5.5) are separate predicates, assumed where the paper assumes them (p. 19). The expected revenue loss $E[\min(D,K)-\min(D,eK)]$ is written as $S(K)-S(eK)$ (linearity of expectation).
-- source:
--   Kao, Keskin & Shang, Impact of information asymmetry and limited production capacity on business interruption insurance, SSRN 3184530 (version of May 13, 2020), pp. 6–19, §3, §4.1–4.2, §5.1–5.2, eqs. (3.2)–(3.4), (4.2)–(4.17), (5.1), (5.3)–(5.7)

import Mathlib
import Definitions.Def_BIInsurance_Screening_Logistic

namespace BIInsurance.Screening

/-- The data of the business-interruption insurance model (§3, pp. 6–10).
Periods `T, τ, w` are natural numbers (cast to `ℝ` in every formula); `lam` is the unit
penalty cost λ; `sbar` is the upper bound s̄ of the coverage percentage. -/
structure Params where
  T : ℕ
  τ : ℕ
  w : ℕ
  K : ℝ
  muH : ℝ
  muL : ℝ
  dH : ℝ
  dL : ℝ
  α : ℝ
  β : ℝ
  γ : ℝ
  ρ : ℝ
  lam : ℝ
  p : ℝ
  c : ℝ
  sbar : ℝ

/-- The standing assumptions of §3 (pp. 6–10, 12, 13), with `0 < ρ` and `w < T - τ` strict. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.τ ∧
  0 < P.K ∧
  0 < P.muL ∧ P.muL < P.muH ∧
  P.dL < 0 ∧ 0 < P.dH ∧
  0 < P.β ∧ P.β < 1 ∧ P.β * P.dH + (1 - P.β) * P.dL = 0 ∧
  0 < P.α ∧ P.α < 1 ∧
  0 < P.γ ∧
  0 < P.ρ ∧ P.ρ ≤ 1 ∧
  0 < P.lam ∧
  0 < P.p ∧ 0 < P.c ∧ P.c ≤ ((P.T : ℝ) - P.τ) * P.p ∧
  (P.w : ℝ) < (P.T : ℝ) - P.τ ∧
  0 < P.sbar ∧
  P.sbar < 1 - P.c / (((P.T : ℝ) - P.τ) * P.p) * (1 + Real.exp (-(P.muL + P.dL) / P.γ))

/-- `ξ(x, μ, δ) = ln[exp(x/γ) + exp((μ + δ)/γ)]`, eq. (4.2). -/
noncomputable def xi (P : Params) (x mu d : ℝ) : ℝ :=
  Real.log (Real.exp (x / P.γ) + Real.exp ((mu + d) / P.γ))

/-- `E_δ[ξ(K, μ, δ)] = β ξ(K, μ, δ_H) + (1 - β) ξ(K, μ, δ_L)`. -/
noncomputable def Exi (P : Params) (mu : ℝ) : ℝ :=
  P.β * xi P P.K mu P.dH + (1 - P.β) * xi P P.K mu P.dL

/-- Per-period expected sales `E_ε[min(D, x)]` for demand `D = m + ε`, `m = μ + δ`. -/
noncomputable def sales (P : Params) (m x : ℝ) : ℝ :=
  expSales P.γ m x

/-- Expected lost sales `E[min(D, K)] - E[min(D, eK)]` at effort `e`. -/
noncomputable def lostSales (P : Params) (m e : ℝ) : ℝ :=
  sales P m P.K - sales P m (e * P.K)

/-- `π^N_{ij0}(K) = T p E[min(D, K)]`, eq. (4.4). -/
noncomputable def piN0 (P : Params) (m : ℝ) : ℝ :=
  (P.T : ℝ) * P.p * sales P m P.K

/-- `π^N_{ij1}(K, e)`, eqs. (4.5)–(4.6). -/
noncomputable def piN1e (P : Params) (m e : ℝ) : ℝ :=
  (P.τ : ℝ) * P.p * sales P m P.K - P.c * e * P.K
    + ((P.T : ℝ) - P.τ) * P.p * sales P m (e * P.K)
    - P.lam * (P.c * e * P.K + ((P.T : ℝ) - P.τ) * P.p * lostSales P m e)

/-- The optimal effort without insurance `ê`, eq. (4.7). -/
noncomputable def eHat (P : Params) (m : ℝ) : ℝ :=
  if m + P.γ * Real.log ((((P.T : ℝ) - P.τ) * P.p - P.c) / P.c) < P.K then
    (m + P.γ * Real.log ((((P.T : ℝ) - P.τ) * P.p - P.c) / P.c)) / P.K
  else 1

/-- `A(s) = w p + (T - τ - w) p (1 - s)`, the quantity in (4.13)–(4.14). -/
noncomputable def Aeff (P : Params) (s : ℝ) : ℝ :=
  (P.w : ℝ) * P.p + ((P.T : ℝ) - P.τ - P.w) * P.p * (1 - s)

/-- `π^I_{ij0}(K, y, s) = -y + T p E[min(D, K)]`, eq. (4.10). -/
noncomputable def piI0 (P : Params) (m y : ℝ) : ℝ :=
  -y + (P.T : ℝ) * P.p * sales P m P.K

/-- `π^I_{ij1}(K, e, y, s)`, eqs. (4.11)–(4.12). -/
noncomputable def piI1e (P : Params) (m e y s : ℝ) : ℝ :=
  -y + (P.τ : ℝ) * P.p * sales P m P.K - P.c * e * P.K
    + ((P.T : ℝ) - P.τ) * P.p * sales P m (e * P.K)
    + ((P.T : ℝ) - P.τ - P.w) * s * P.p * lostSales P m e
    - P.lam * (P.c * e * P.K + ((P.T : ℝ) - P.τ) * P.p * lostSales P m e
        - ((P.T : ℝ) - P.τ - P.w) * s * P.p * lostSales P m e)

/-- The optimal effort with insurance `e*(s)`, eqs. (4.13)–(4.14). -/
noncomputable def eStar (P : Params) (m s : ℝ) : ℝ :=
  if m + P.γ * Real.log ((Aeff P s - P.c) / P.c) < P.K then
    (m + P.γ * Real.log ((Aeff P s - P.c) / P.c)) / P.K
  else 1

/-- `E_{δ,Z}[π^N_i(K)]`, eq. (4.9), for early forecast `μ`. -/
noncomputable def EpiN (P : Params) (mu : ℝ) : ℝ :=
  P.β * (P.ρ * piN1e P (mu + P.dH) (eHat P (mu + P.dH)) + (1 - P.ρ) * piN0 P (mu + P.dH))
    + (1 - P.β) * (P.ρ * piN1e P (mu + P.dL) (eHat P (mu + P.dL))
        + (1 - P.ρ) * piN0 P (mu + P.dL))

/-- `E_{δ,Z}[π^I_i(K, y, s)]`, eqs. (4.15)–(4.16), for early forecast `μ`. -/
noncomputable def EpiI (P : Params) (mu y s : ℝ) : ℝ :=
  P.β * (P.ρ * piI1e P (mu + P.dH) (eStar P (mu + P.dH) s) y s
      + (1 - P.ρ) * piI0 P (mu + P.dH) y)
    + (1 - P.β) * (P.ρ * piI1e P (mu + P.dL) (eStar P (mu + P.dL) s) y s
      + (1 - P.ρ) * piI0 P (mu + P.dL) y)

/-- The insurer's expected claim payment to a firm of early forecast `μ` holding coverage `s`:
`ρ (T - τ - w) (β s p E[min(D_{iH}, K) - min(D_{iH}, e*_{iH}(s) K)]
 + (1 - β) s p E[min(D_{iL}, K) - min(D_{iL}, e*_{iL}(s) K)])`, as in (5.1). -/
noncomputable def claimCost (P : Params) (mu s : ℝ) : ℝ :=
  P.ρ * ((P.T : ℝ) - P.τ - P.w) *
    (P.β * s * P.p * lostSales P (mu + P.dH) (eStar P (mu + P.dH) s)
      + (1 - P.β) * s * P.p * lostSales P (mu + P.dL) (eStar P (mu + P.dL) s))

/-- A menu of two contracts `(y_H, s_H)` and `(y_L, s_L)`. -/
structure Menu where
  yH : ℝ
  sH : ℝ
  yL : ℝ
  sL : ℝ

/-- The insurer's objective in (5.1). -/
noncomputable def insurerProfit (P : Params) (M : Menu) : ℝ :=
  P.α * (M.yH - claimCost P P.muH M.sH) + (1 - P.α) * (M.yL - claimCost P P.muL M.sL)

/-- (IC-HL) -/
def IC_HL (P : Params) (M : Menu) : Prop := EpiI P P.muH M.yL M.sL ≤ EpiI P P.muH M.yH M.sH

/-- (IC-LH) -/
def IC_LH (P : Params) (M : Menu) : Prop := EpiI P P.muL M.yH M.sH ≤ EpiI P P.muL M.yL M.sL

/-- (IR-H) -/
def IR_H (P : Params) (M : Menu) : Prop := EpiN P P.muH ≤ EpiI P P.muH M.yH M.sH

/-- (IR-L) -/
def IR_L (P : Params) (M : Menu) : Prop := EpiN P P.muL ≤ EpiI P P.muL M.yL M.sL

/-- Feasible menus of (5.1): coverages in `[0, s̄]` and the four IC/IR constraints. -/
def Feasible (P : Params) (M : Menu) : Prop :=
  M.sH ∈ Set.Icc 0 P.sbar ∧ M.sL ∈ Set.Icc 0 P.sbar ∧
    IC_HL P M ∧ IC_LH P M ∧ IR_H P M ∧ IR_L P M

/-- An optimal menu of the insurer's problem (5.1). -/
def IsOptimalMenu (P : Params) (M : Menu) : Prop :=
  Feasible P M ∧ ∀ M' : Menu, Feasible P M' → insurerProfit P M' ≤ insurerProfit P M

/-- `g_H(s_H) = E[π^I_H(K, s_H)] - E[π^N_H(K)]`, eq. (5.3). -/
noncomputable def gH (P : Params) (sH : ℝ) : ℝ :=
  EpiI P P.muH 0 sH - EpiN P P.muH

/-- `g_L(s_H, s_L) = g_H(s_H) + E[π^I_L(K, s_L)] - E[π^I_L(K, s_H)]`, eq. (5.4). -/
noncomputable def gL (P : Params) (sH sL : ℝ) : ℝ :=
  gH P sH + EpiI P P.muL 0 sL - EpiI P P.muL 0 sH

/-- `R(s_H, s_L)`: the objective of (5.1) with `y_H = g_H(s_H)`, `y_L = g_L(s_H, s_L)`. -/
noncomputable def R (P : Params) (sH sL : ℝ) : ℝ :=
  insurerProfit P ⟨gH P sH, sH, gL P sH sL, sL⟩

/-- The condition `K > μ_H + δ_H + γ ln(((T - τ)p - c)/c)` (p. 19). -/
def KCond (P : Params) : Prop :=
  P.muH + P.dH + P.γ * Real.log ((((P.T : ℝ) - P.τ) * P.p - P.c) / P.c) < P.K

/-- The left-hand side of (5.5). -/
noncomputable def cond55LHS (P : Params) : ℝ :=
  (1 - P.α) * (1 + P.lam) * P.γ * (Exi P P.muL - Exi P P.muH)
    + P.α * P.lam * (P.K + P.γ * Real.log (((P.T : ℝ) - P.τ) * P.p
        / (((P.T : ℝ) - P.τ) * P.p - P.c)) - P.γ * Exi P P.muH)

/-- Condition (5.5). -/
def Cond55 (P : Params) : Prop := 0 ≤ cond55LHS P

/-- The bracket `[(T - τ)(1 - s) + s w]` of (5.6)–(5.7). -/
noncomputable def effPeriods (P : Params) (s : ℝ) : ℝ :=
  ((P.T : ℝ) - P.τ) * (1 - s) + s * P.w

/-- The left-hand side of (5.6) at `s'_H = s` (with `w_H = w`). -/
noncomputable def foc56 (P : Params) (s : ℝ) : ℝ :=
  (1 - P.α) * (1 + P.lam) * P.γ * (Exi P P.muL - Exi P P.muH)
    - P.α * (((P.T : ℝ) - P.τ - P.w) * P.c * P.γ * s
        / ((effPeriods P s * P.p - P.c) * effPeriods P s))
    + P.α * P.lam * (P.K + P.γ * Real.log (effPeriods P s * P.p
        / (effPeriods P s * P.p - P.c)) - P.γ * Exi P P.muH)

/-- The left-hand side of (5.7) at `s'_L = s` (with `w_L = w`). -/
noncomputable def foc57 (P : Params) (s : ℝ) : ℝ :=
  P.lam * (P.K + P.γ * Real.log (effPeriods P s * P.p / (effPeriods P s * P.p - P.c))
      - P.γ * Exi P P.muL)
    - ((P.T : ℝ) - P.τ - P.w) * P.c * P.γ * s
        / ((effPeriods P s * P.p - P.c) * effPeriods P s)

end BIInsurance.Screening


