-- Prove2me | Definitions.Def_ToneAtTop_Diversion_Model
-- name    : ToneAtTop_Diversion_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T05:52:26.250952+00:00
-- url     : https://prove2.me/theorems/1d608302-fd96-4935-adb3-85c52787b3cb
-- title:
--   §3, (1)–(7b), pp. 6–10 — CEO diversion model
-- statement:
--   An authority chooses formal control $c$ before a CEO observes a uniformly distributed temptation $x\in[0,\bar x]$. A low CEO type has reputation value $0$; a high type has value $\eta_H>0$ and occurs with probability $p$. The CEO diverts precisely when her diversion utility exceeds her compliance utility. If she diverts, the authority loses $(1-c)x$.
--
--   The model defines the cost and expected loss by
--
--   $$
--   K(c)=\frac{\lambda}{1-c},\qquad
--   L(c)=\int_0^{\bar x}\frac{pD(c,x,\eta_H)+(1-p)D(c,x,0)}{\bar x}\,dx+K(c),
--   $$
--
--   where $D(c,x,\eta)$ is the resources diverted by type $\eta$ under her utility choice. It also defines $\tau=(1-\beta)\eta_H/\gamma$ and $x_T(c)=\tau/(1-c)$. The standing assumptions are $\bar x,\lambda,\eta_H>0$, $0<p<1$, $\beta<1$, $0<\gamma<1$, and $\tau<\bar x$.
--
--   These definitions retain the CEO's incentive decision inside the loss that the authority minimizes.
--
--   **Formalization Note** The cost and tipping-point formulas are used only at admissible controls $c\in[0,1)$; Lean's real division at $c=1$ does not represent the paper's $K(1)=\infty$.
-- source:
--   Penno, A Theory of Assurance: Balancing Costly Formal Control with Tone at the Top, SSRN working paper 2876700 (revision of May 2019), pp. 6–10 (PDF 8–12), §3, (1)–(7b)

import Mathlib

namespace ToneAtTop.Diversion

/-- Parameters of the diversion model in §3. -/
structure Params where
  xbar : ℝ
  lam : ℝ
  p : ℝ
  β : ℝ
  γ : ℝ
  ηH : ℝ

/-- The high CEO type's index of resistance to diversion, (4). -/
noncomputable def Params.tau (P : Params) : ℝ := (1 - P.β) * P.ηH / P.γ

/-- Standing assumptions of §3, including (6). -/
def Params.Standing (P : Params) : Prop :=
  0 < P.xbar ∧ 0 < P.lam ∧ 0 < P.p ∧ P.p < 1 ∧ P.β < 1 ∧
    0 < P.γ ∧ P.γ < 1 ∧ 0 < P.ηH ∧ P.tau < P.xbar

/-- Direct administrative cost, (2), for controls below one. -/
noncomputable def costK (lam c : ℝ) : ℝ := lam / (1 - c)

/-- CEO utility if she diverts, (3a). -/
def utilNoncompliant (P : Params) (c x η : ℝ) : ℝ :=
  P.β * η + P.γ * (1 - c) * x

/-- CEO utility if she complies, (3b). -/
def utilCompliant (η : ℝ) : ℝ := η

/-- The CEO diverts exactly when (3a) exceeds (3b). -/
def Noncompliant (P : Params) (c x η : ℝ) : Prop :=
  utilCompliant η < utilNoncompliant P c x η

/-- Resources lost to diversion under the CEO's choice. -/
noncomputable def diverted (P : Params) (c x η : ℝ) : ℝ :=
  by
    classical
    exact if Noncompliant P c x η then (1 - c) * x else 0

/-- Expected diversion of both CEO types under uniform temptation, plus (2). -/
noncomputable def expectedLoss (P : Params) (c : ℝ) : ℝ :=
  (∫ x in (0 : ℝ)..P.xbar,
    (P.p * diverted P c x P.ηH + (1 - P.p) * diverted P c x 0) / P.xbar) +
    costK P.lam c

/-- The high CEO type's tipping point, (5), for controls below one. -/
noncomputable def tippingPoint (P : Params) (c : ℝ) : ℝ := P.tau / (1 - c)

end ToneAtTop.Diversion


