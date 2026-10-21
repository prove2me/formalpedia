-- Prove2me | Definitions.Def_PharmaEPR_Welfare_Model
-- name    : PharmaEPR_Welfare_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:32:40.048179+00:00
-- url     : https://prove2.me/theorems/589399aa-43f9-487e-9513-a1fa29781bff
-- title:
--   §3, pp. 8–14 — prescription, producer profit, EC and SR policies, and equilibrium welfare
-- statement:
--   This module defines the pharmaceutical extended-producer-responsibility game of Alev, Atasu, Toktay and Zhang.
--
--   The primitive parameters are health benefit $u_p$, reputational cost $o_d$, promotion cost coefficients $\alpha,\beta$, collection cost $k$, and environmental and social disutilities $\epsilon_e,\epsilon_s$. A producer chooses price $p\in\mathbb R$ and promotion levels $\eta_d,\eta_p\in[0,1]$. Independent need and preferred-use levels $\theta_n,\theta_u$ are uniform on $[0,1]$. The doctor's utility at prescription $q$ is
--
--   $$U_d(q)=u_p\theta_n-pq+\eta_dq-o_d(1-\eta_p)(q-\theta_n).$$
--
--   The prescribed quantity is $q_p=1$ when $\eta_d\ge p+o_d(1-\eta_p)$, and $q_p=\theta_n$ otherwise; the used quantity is $q_u=\min\{\theta_u,q_p\}$. Producer profit is expected price revenue minus $\alpha\eta_d^2+\beta\eta_p^2$ and the policy's compliance cost. EC charges the producer $kr_{EC}(q_p-q_u)$; SR charges $tq_p$, while the planner receives that fee and pays $kr_{SR}(q_p-q_u)$.
--
--   Total welfare is expected doctor utility plus producer profit plus planner surplus, less $\epsilon_e[q_u+(1-r)(q_p-q_u)]$ and $\epsilon_s(1-r)(q_p-q_u)$. An achievable value comes from a producer profit maximum with pointwise nonnegative doctor utility and nonnegative producer profit, a collection rate in $[0,1]$, a nonnegative SR fee, and nonnegative planner surplus. The planner may select among producer optima; its welfare value is the supremum of achievable values.
--
--   The appendix thresholds are $\bar u_p^{EC}=(4\alpha-2\beta-1)/3$, $\bar u_p^{SR}=\alpha-\beta$, $\bar k=3(1-2\beta-u_p)/2$, $\bar r_{EC}=3(1-2\beta-u_p)/(2k)$, and $\bar t=1-2\beta-u_p$. These definitions serve all milestone and goal statements.
--
--   **Formalization Note** Expectations are iterated interval integrals over $[0,1]^2$. At the doctor's indifference point the response is over-prescription. EC ignores the fee field of the common policy record, and price has no nonnegativity restriction. The regime predicate records $u_p\ge0$, $0<\alpha<1/4$, $0<\beta<o_d/2$, $\alpha+\beta\le1$, $k>0$, and $\epsilon_e,\epsilon_s\ge0$.
-- source:
--   Alev, Atasu, Toktay & Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020-09-05 posting), pp. 8–14, §3; Online Appendix p. 2, threshold displays

import Mathlib

namespace PharmaEPR.Welfare

structure Params where
  up : ℝ
  od : ℝ
  alpha : ℝ
  beta : ℝ
  k : ℝ
  epsE : ℝ
  epsS : ℝ

def Regime (P : Params) : Prop :=
  0 ≤ P.up ∧ 0 < P.alpha ∧ P.alpha < 1 / 4 ∧
  0 < P.beta ∧ 2 * P.beta < P.od ∧ P.alpha + P.beta ≤ 1 ∧
  0 < P.k ∧ 0 ≤ P.epsE ∧ 0 ≤ P.epsS

inductive EPRModel
  | EC | SR
  deriving DecidableEq

structure Action where
  p : ℝ
  etaD : ℝ
  etaP : ℝ

structure Policy where
  r : ℝ
  t : ℝ

def docUtil (P : Params) (a : Action) (thetaN q : ℝ) : ℝ :=
  P.up * thetaN - a.p * q + a.etaD * q -
    P.od * (1 - a.etaP) * (q - thetaN)

def OverPrescribes (P : Params) (a : Action) : Prop :=
  a.p + P.od * (1 - a.etaP) ≤ a.etaD

noncomputable def presc (P : Params) (a : Action) (thetaN : ℝ) : ℝ :=
  by classical exact if OverPrescribes P a then 1 else thetaN

noncomputable def used (P : Params) (a : Action) (thetaN thetaU : ℝ) : ℝ :=
  min thetaU (presc P a thetaN)

noncomputable def E2 (f : ℝ → ℝ → ℝ) : ℝ :=
  ∫ thetaN in (0 : ℝ)..1, ∫ thetaU in (0 : ℝ)..1, f thetaN thetaU

noncomputable def complianceCost (P : Params) (m : EPRModel)
    (y : Policy) (a : Action) : ℝ :=
  match m with
  | .EC => E2 (fun thetaN thetaU =>
      P.k * y.r * (presc P a thetaN - used P a thetaN thetaU))
  | .SR => E2 (fun thetaN _ => y.t * presc P a thetaN)

noncomputable def prodProfit (P : Params) (m : EPRModel)
    (y : Policy) (a : Action) : ℝ :=
  E2 (fun thetaN _ => a.p * presc P a thetaN) -
    P.alpha * a.etaD ^ 2 - P.beta * a.etaP ^ 2 -
    complianceCost P m y a

def ProdFeasible (P : Params) (a : Action) : Prop :=
  0 ≤ a.etaD ∧ a.etaD ≤ 1 ∧ 0 ≤ a.etaP ∧ a.etaP ≤ 1 ∧
    ∀ thetaN ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ docUtil P a thetaN (presc P a thetaN)

def ProdOptimal (P : Params) (m : EPRModel) (y : Policy)
    (a : Action) : Prop :=
  ProdFeasible P a ∧
    ∀ a', ProdFeasible P a' → prodProfit P m y a' ≤ prodProfit P m y a

noncomputable def plannerSurplus (P : Params) (m : EPRModel)
    (y : Policy) (a : Action) : ℝ :=
  match m with
  | .EC => 0
  | .SR => E2 (fun thetaN thetaU =>
      y.t * presc P a thetaN -
        P.k * y.r * (presc P a thetaN - used P a thetaN thetaU))

noncomputable def envDisutil (P : Params) (y : Policy) (a : Action)
    (thetaN thetaU : ℝ) : ℝ :=
  P.epsE * (used P a thetaN thetaU +
    (1 - y.r) * (presc P a thetaN - used P a thetaN thetaU))

noncomputable def socDisutil (P : Params) (y : Policy) (a : Action)
    (thetaN thetaU : ℝ) : ℝ :=
  P.epsS * (1 - y.r) *
    (presc P a thetaN - used P a thetaN thetaU)

noncomputable def welfare (P : Params) (m : EPRModel)
    (y : Policy) (a : Action) : ℝ :=
  E2 (fun thetaN _ => docUtil P a thetaN (presc P a thetaN)) +
    prodProfit P m y a + plannerSurplus P m y a -
    E2 (envDisutil P y a) - E2 (socDisutil P y a)

def Outcome (P : Params) (m : EPRModel) (y : Policy)
    (a : Action) : Prop :=
  0 ≤ y.r ∧ y.r ≤ 1 ∧ (m = .SR → 0 ≤ y.t) ∧
    ProdOptimal P m y a ∧
    0 ≤ prodProfit P m y a ∧ 0 ≤ plannerSurplus P m y a

def achievable (P : Params) (m : EPRModel) : Set ℝ :=
  {w | ∃ y a, Outcome P m y a ∧ welfare P m y a = w}

def achievableNoOP (P : Params) (m : EPRModel) : Set ℝ :=
  {w | ∃ y a, Outcome P m y a ∧ ¬ OverPrescribes P a ∧
    welfare P m y a = w}

noncomputable def optW (P : Params) (m : EPRModel) : ℝ :=
  sSup (achievable P m)

noncomputable def uEC (P : Params) : ℝ :=
  (4 * P.alpha - 2 * P.beta - 1) / 3

def uSR (P : Params) : ℝ :=
  P.alpha - P.beta

noncomputable def kBar (P : Params) : ℝ :=
  3 * (1 - 2 * P.beta - P.up) / 2

noncomputable def rBarEC (P : Params) : ℝ :=
  3 * (1 - 2 * P.beta - P.up) / (2 * P.k)

noncomputable def tBar (P : Params) : ℝ :=
  1 - 2 * P.beta - P.up

end PharmaEPR.Welfare


