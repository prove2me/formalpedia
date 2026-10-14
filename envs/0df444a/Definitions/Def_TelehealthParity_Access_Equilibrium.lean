-- Prove2me | Definitions.Def_TelehealthParity_Access_Equilibrium
-- name    : TelehealthParity_Access_Equilibrium
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T04:09:03.518031+00:00
-- url     : https://prove2.me/theorems/43c6041e-a4c3-49af-8f0b-fc6952bd4466
-- title:
--   §3–§4.1, pp. 9–15 — sojourn times (Lemma 1), the patients' utilities (1) and their equilibrium
-- statement:
--   This definition states what it means for a split of patients among balking, the office and telehealth to be an equilibrium, for the model of the definition `TelehealthParity.Access.Setting`.
--
--   A strategy is $\pi=(\pi^B,\pi^O,\pi^T)$ with $\pi^B,\pi^O,\pi^T\ge 0$ and $\pi^B+\pi^O+\pi^T=1$: the proportions of arriving patients who balk, go to the office, and use telehealth. By the paper's Lemma 1 (p. 12), with exponential service and the provider serving the telehealth queue with probability $\theta$, the expected sojourn times are
--   $$W^O=\frac{1}{(1-\theta)\mu-(\pi^O+q\pi^T)\lambda}\quad(4),\qquad W^T=\frac{1}{\theta\mu-\pi^T\lambda}\quad(5);$$
--   the office queue also receives the duplicate visits of telehealth patients. Call the denominators the office and telehealth *loads*. A channel is *available* when its queue is stable: the office when its load is positive, telehealth when both its own load and the office load are positive (its duplicate visits go to the office). The expected utilities (display (1), p. 9) are
--   $$u^O=V-c_O-\tau-hW^O,\qquad u^T=V-c_T-hW^T-q\,(c_O+\tau+hW^O),$$
--   and balking pays $0$.
--
--   $\pi$ is an **equilibrium** at the commitment $\theta$ when every action used with positive probability is a best response among the available ones:
--   1. if $\pi^B>0$, then $u^O\le 0$ when the office is available and $u^T\le 0$ when telehealth is available;
--   2. if $\pi^O>0$, then the office is available, $u^O\ge 0$, and $u^T\le u^O$ when telehealth is available;
--   3. if $\pi^T>0$, then telehealth is available, $u^T\ge 0$, and $u^O\le u^T$ when the office is available.
--
--   The equilibrium types of Figure 3 (p. 13) are: **BOT** (some equilibrium with $\pi^B,\pi^O,\pi^T>0$), **BO** (some equilibrium with $\pi^B,\pi^O>0$, $\pi^T=0$), **BT** (some equilibrium with $\pi^B,\pi^T>0$, $\pi^O=0$) and **B** ($\pi=(1,0,0)$ is an equilibrium).
--
--   These are the objects of Theorems 1–3, which locate each equilibrium type on the range of $\theta$.
--
--   **Formalization Note** Lemma 1 is not formalized: (4)–(5) are taken as the model, as in the paper, which derives them from M/M/1 sojourn times under Bernoulli splitting. An unstable channel (load $\le 0$, infinite sojourn time) cannot be used and imposes no constraint on the others; this is how the paper discards the $(+)$ root of (16) ("Only the (−) root leads to a stable queue in telehealth"), and it makes $\pi=(1,0,0)$ an equilibrium at $\theta=1$, where the office has no capacity. The utilities are only read when the corresponding channel is available, so Lean's convention $x/0=0$ never enters.
-- source:
--   Çakıcı and Mills, Telehealth in Acute Care: Pay Parity and Patient Access, SSRN working paper (version of August 19, 2024), p. 9, display (1); p. 12, Lemma 1, eqs. (4)–(5); pp. 13–15, equilibria BOT, BO, BT, B (Figure 3, conditions (7), (13), (16))

import Mathlib
import Definitions.Def_TelehealthParity_Access_Setting

namespace TelehealthParity.Access

/-- The office load `(1 − θ)μ − (π^O + qπ^T)λ`, the denominator of the office sojourn time
`W^O` of eq. (4), Lemma 1, p. 12 (duplicate visits also join the office queue). -/
def loadO (p : Params) (q θ πO πT : ℝ) : ℝ :=
  (1 - θ) * p.μ - (πO + q * πT) * p.lam

/-- The telehealth load `θμ − π^Tλ`, the denominator of the telehealth sojourn time `W^T` of
eq. (5), Lemma 1, p. 12. -/
def loadT (p : Params) (θ πT : ℝ) : ℝ :=
  θ * p.μ - πT * p.lam

/-- The office channel is available (its queue is stable, `W^O < ∞`) iff its load is positive. -/
def AvailO (p : Params) (q θ πO πT : ℝ) : Prop :=
  0 < loadO p q θ πO πT

/-- The telehealth channel is available iff both its own queue and the office queue (which serves
its duplicate visits) are stable. -/
def AvailT (p : Params) (q θ πO πT : ℝ) : Prop :=
  0 < loadT p θ πT ∧ 0 < loadO p q θ πO πT

/-- Expected utility of an office visit, `V − cO − τ − hW^O` (display (1), p. 9), with
`W^O = 1/loadO`. Meaningful only when `AvailO` holds. -/
noncomputable def utilO (p : Params) (q θ πO πT : ℝ) : ℝ :=
  p.V - p.cO - p.τ - p.h / loadO p q θ πO πT

/-- Expected utility of a telehealth visit, `V − cT − hW^T − q(cO + τ + hW^O)` (display (1),
p. 9), with `W^T = 1/loadT`, `W^O = 1/loadO`. Meaningful only when `AvailT` holds. -/
noncomputable def utilT (p : Params) (q θ πO πT : ℝ) : ℝ :=
  p.V - p.cT - p.h / loadT p θ πT - q * (p.cO + p.τ + p.h / loadO p q θ πO πT)

/-- The patients' (homogeneous, symmetric) equilibrium of §4, p. 12–15, at telehealth commitment
`θ`: `π = (π^B, π^O, π^T)` lies in the probability simplex and every action used with positive
probability is a best response, where balking pays `0` and is always available, and a channel
whose queue is unstable (`AvailO`/`AvailT` fails: infinite sojourn time) is not available — it
cannot be used, and it constrains nothing. -/
def IsEquilibrium (p : Params) (q θ πB πO πT : ℝ) : Prop :=
  0 ≤ πB ∧ 0 ≤ πO ∧ 0 ≤ πT ∧ πB + πO + πT = 1 ∧
    (0 < πB →
      (AvailO p q θ πO πT → utilO p q θ πO πT ≤ 0) ∧
      (AvailT p q θ πO πT → utilT p q θ πO πT ≤ 0)) ∧
    (0 < πO →
      AvailO p q θ πO πT ∧ 0 ≤ utilO p q θ πO πT ∧
      (AvailT p q θ πO πT → utilT p q θ πO πT ≤ utilO p q θ πO πT)) ∧
    (0 < πT →
      AvailT p q θ πO πT ∧ 0 ≤ utilT p q θ πO πT ∧
      (AvailO p q θ πO πT → utilO p q θ πO πT ≤ utilT p q θ πO πT))

/-- "BOT is an equilibrium": an equilibrium mixing balking, office and telehealth exists. -/
def IsBOT (p : Params) (q θ : ℝ) : Prop :=
  ∃ πB πO πT : ℝ, 0 < πB ∧ 0 < πO ∧ 0 < πT ∧ IsEquilibrium p q θ πB πO πT

/-- "BO is an equilibrium": an equilibrium mixing balking and office (`π^T = 0`) exists. -/
def IsBO (p : Params) (q θ : ℝ) : Prop :=
  ∃ πB πO : ℝ, 0 < πB ∧ 0 < πO ∧ IsEquilibrium p q θ πB πO 0

/-- "BT is an equilibrium": an equilibrium mixing balking and telehealth (`π^O = 0`) exists. -/
def IsBT (p : Params) (q θ : ℝ) : Prop :=
  ∃ πB πT : ℝ, 0 < πB ∧ 0 < πT ∧ IsEquilibrium p q θ πB 0 πT

/-- "B is an equilibrium": all patients balk, `π = (1, 0, 0)`. -/
def IsB (p : Params) (q θ : ℝ) : Prop :=
  IsEquilibrium p q θ 1 0 0

end TelehealthParity.Access


