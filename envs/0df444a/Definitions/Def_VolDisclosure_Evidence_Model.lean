-- Prove2me | Definitions.Def_VolDisclosure_Evidence_Model
-- name    : VolDisclosure_Evidence_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:39:28.89296+00:00
-- url     : https://prove2.me/theorems/e7783d71-2830-4701-8abe-df0a8cff511f
-- title:
--   §3, §5.1, App. (2), pp. 9–15, 37 — dynamic agency with evidence: policies, (ICg), (ICb), (ICn), (PK), (LL), Bellman operator (T), value function
-- statement:
--   This file fixes the infinite-horizon dynamic agency model with voluntary disclosure of evidence of Fu and Trigilia.
--
--   **Parameters (§3, p. 9).** A firm produces i.i.d. cash flows $x_t \in \{h, l\}$ with $h > l > 0$ and $P(x_t = h) = p \in (0,1)$. Both parties discount at rate $r \in (0,1)$. By reporting a high cash flow as low, the manager diverts $\Delta := h - l$ and obtains the private benefit $\delta := \lambda\Delta$ with $\lambda \in (0,1]$. Write $\mu := ph + (1-p)l$. The derived constants are
--   $$
--   s^* = \frac{(1+r)\mu}{r},\qquad \bar v = \frac{(1+r)p\delta}{r},\qquad \hat r(\pi) = \frac{r}{1-(1-p)\pi},\qquad v^1(\pi) = \frac{\hat r\,\bar v}{1+\hat r},
--   $$
--   the first-best firm value (p. 10), the cash payout boundary ((4), p. 16), the adjusted rate of p. 17 and the first termination threshold (Proposition 3, p. 19, and p. 41). Here $\pi$ is the per-period probability that evidence of the cash flow arrives; $\pi = 0$ is the benchmark without evidence.
--
--   **Policies and constraints (§5.1, pp. 13–14).** At a promised utility $v$, a one-period contract chooses the termination probability $\theta \in [0,1]$, cash payments $u_{dh}, u_{dl}, u_{nh}, u_{nl} \ge 0$ (LL) and continuation utilities $w_{dh}, w_{dl}, w_{nh}, w_{nl} \ge 0$, indexed by disclosure ($d$) or no disclosure ($n$) and by the reported cash flow. It must satisfy
--   $$
--   \begin{aligned}
--   u_{dh} + \tfrac{w_{dh}}{1+r} &\ge u_{nh} + \tfrac{w_{nh}}{1+r} &&(IC_g)\\
--   u_{dl} + \tfrac{w_{dl}}{1+r} &\ge u_{nl} + \tfrac{w_{nl}}{1+r} &&(IC_b)\\
--   u_{nh} + \tfrac{w_{nh}}{1+r} &\ge \delta + u_{nl} + \tfrac{w_{nl}}{1+r} &&(IC_n)\\
--   v &= (1-\theta)\Big[\pi E_d\big(u_d + \tfrac{w_d}{1+r}\big) + (1-\pi)E_n\big(u_n + \tfrac{w_n}{1+r}\big)\Big] &&(PK)
--   \end{aligned}
--   $$
--   where $E_a(u_a + \frac{w_a}{1+r}) = p(u_{ah} + \frac{w_{ah}}{1+r}) + (1-p)(u_{al} + \frac{w_{al}}{1+r})$.
--
--   **Bellman operator (T), p. 37.** For a function $q$ on $\mathbb R_+$,
--   $$
--   Tq(v) = \sup\Big\{(1-\theta)\mu + \frac{1-\theta}{1+r}\Big(\pi[pq(w_{dh}) + (1-p)q(w_{dl})] + (1-\pi)[pq(w_{nh}) + (1-p)q(w_{nl})]\Big)\Big\},
--   $$
--   the supremum taken over all feasible policies at $v$. The class $\mathcal F$ consists of the functions continuous on $\mathbb R_+$ with $0 \le q \le s^*$ there. A **firm value** for evidence probability $\pi$ is an $s \in \mathcal F$ with $s(v) = Ts(v)$ for every $v \ge 0$: the value function of problem (S), p. 15. A policy is **optimal** at $v$ if it is feasible and attains $s(v)$. The **credit spread** is $1 - s/s^*$ ((7), p. 20).
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** The paper writes "max" in (T); here it is the supremum over feasible policies (attainment is a separate claim, Proposition 3). On p. 37 $\pi$ appears among the maximisation variables; it is a parameter, as in (S), and is a parameter here. Nonnegativity of the $w$'s comes from p. 10 ("$w_t \ge 0$") and from $\mathcal F$ being a class of functions on $\mathbb R_+$; (LL) itself lists only the $u$'s. Membership in $\mathcal F$ and the fixed-point equation are imposed on $v \ge 0$ only, since feasibility never evaluates $q$ at a negative argument. The parameter $\lambda$ is called `lam`.
-- source:
--   Fu & Trigilia, Voluntary Disclosure, Moral Hazard and Default Risk, working paper (August 28, 2019), pp. 9–10 (§3), pp. 13–15 (§5.1, (ICg), (ICb), (ICn), (PK), (LL), (S)), p. 16 ((4)), p. 17 (r̂), p. 20 ((7)), p. 37 ((T), F)

import Mathlib

namespace VolDisclosure.Evidence

/-- Primitive parameters of the model (§3, p. 9): cash flows `h > l > 0`, probability `p` of the
high cash flow, discount rate `r`, and the severity `lam` (the paper's λ) of the moral hazard
problem. -/
structure Params where
  h : ℝ
  l : ℝ
  p : ℝ
  r : ℝ
  lam : ℝ

/-- Standing assumptions of §3 (p. 9): `h > l > 0`, `p ∈ (0,1)`, `r ∈ (0,1)`, `λ ∈ (0,1]`. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.l ∧ P.l < P.h ∧ 0 < P.p ∧ P.p < 1 ∧ 0 < P.r ∧ P.r < 1 ∧ 0 < P.lam ∧ P.lam ≤ 1

/-- `Δ := h − l` (p. 9). -/
def Params.Δ (P : Params) : ℝ := P.h - P.l

/-- `µ := E(x_t) = p h + (1 − p) l` (p. 9). -/
def Params.μ (P : Params) : ℝ := P.p * P.h + (1 - P.p) * P.l

/-- The private benefit of diversion `δ := λΔ` (p. 9). -/
def Params.δ (P : Params) : ℝ := P.lam * P.Δ

/-- First-best firm value `s* := (1 + r)µ / r` (p. 10). -/
noncomputable def Params.sStar (P : Params) : ℝ := (1 + P.r) * P.μ / P.r

/-- The cash payout boundary `v̄ = r⁻¹(1 + r)pδ` (Proposition 2, (4), p. 16). -/
noncomputable def Params.vBar (P : Params) : ℝ := (1 + P.r) * P.p * P.δ / P.r

/-- `r̂ := r / (1 − (1 − p)π)` (p. 17). -/
noncomputable def Params.rHat (P : Params) (π : ℝ) : ℝ := P.r / (1 - (1 - P.p) * π)

/-- The first termination threshold `v¹(π) = [1 − 1/(1 + r̂)] v̄ = r̂ v̄ / (1 + r̂)`
(Proposition 3, third bullet with `n = 1`, p. 19; p. 41). -/
noncomputable def Params.v1 (P : Params) (π : ℝ) : ℝ :=
  P.rHat π * P.vBar / (1 + P.rHat π)

/-- One period of the contract at a state `v` (§5.1, p. 13): termination probability `θ`, cash
payments `u_dh, u_dl, u_nh, u_nl` and continuation utilities `w_dh, w_dl, w_nh, w_nl`, indexed
by disclosure (`d`) or no disclosure (`n`) and by the reported cash flow (`h` or `l`). -/
structure Policy where
  θ : ℝ
  udh : ℝ
  udl : ℝ
  unh : ℝ
  unl : ℝ
  wdh : ℝ
  wdl : ℝ
  wnh : ℝ
  wnl : ℝ

/-- Feasibility of a policy at promised utility `v` with evidence probability `π`:
`θ ∈ [0,1]`, (LL) `u ≥ 0`, `w ≥ 0` (p. 10), (ICg), (ICb), (ICn) and (PK) (p. 14). -/
def Feasible (P : Params) (π v : ℝ) (a : Policy) : Prop :=
  0 ≤ a.θ ∧ a.θ ≤ 1 ∧
  0 ≤ a.udh ∧ 0 ≤ a.udl ∧ 0 ≤ a.unh ∧ 0 ≤ a.unl ∧
  0 ≤ a.wdh ∧ 0 ≤ a.wdl ∧ 0 ≤ a.wnh ∧ 0 ≤ a.wnl ∧
  a.udh + a.wdh / (1 + P.r) ≥ a.unh + a.wnh / (1 + P.r) ∧
  a.udl + a.wdl / (1 + P.r) ≥ a.unl + a.wnl / (1 + P.r) ∧
  a.unh + a.wnh / (1 + P.r) ≥ P.δ + a.unl + a.wnl / (1 + P.r) ∧
  v = (1 - a.θ) *
    (π * (P.p * (a.udh + a.wdh / (1 + P.r)) + (1 - P.p) * (a.udl + a.wdl / (1 + P.r)))
      + (1 - π) * (P.p * (a.unh + a.wnh / (1 + P.r)) + (1 - P.p) * (a.unl + a.wnl / (1 + P.r))))

/-- The objective of the Bellman operator (T) (p. 37) for a continuation-value function `q`. -/
noncomputable def objective (P : Params) (π : ℝ) (q : ℝ → ℝ) (a : Policy) : ℝ :=
  (1 - a.θ) * P.μ + (1 - a.θ) / (1 + P.r) *
    (π * (P.p * q a.wdh + (1 - P.p) * q a.wdl) + (1 - π) * (P.p * q a.wnh + (1 - P.p) * q a.wnl))

/-- The Bellman operator (T) (p. 37), with the evidence probability `π` a parameter and the
maximum read as the supremum over all feasible policies. -/
noncomputable def T (P : Params) (π : ℝ) (q : ℝ → ℝ) (v : ℝ) : ℝ :=
  sSup (objective P π q '' {a | Feasible P π v a})

/-- The class `F` of p. 37 on `R₊`: continuous with `0 ≤ q ≤ s*`. -/
def InF (P : Params) (q : ℝ → ℝ) : Prop :=
  ContinuousOn q (Set.Ici 0) ∧ ∀ v, 0 ≤ v → 0 ≤ q v ∧ q v ≤ P.sStar

/-- `s` is the firm value of problem (S) for evidence probability `π`: a fixed point of (T) in `F`
(on `R₊`). -/
def IsValue (P : Params) (π : ℝ) (s : ℝ → ℝ) : Prop :=
  InF P s ∧ ∀ v, 0 ≤ v → s v = T P π s v

/-- `a` is an optimal policy at `v` for the firm value `s`: feasible and attaining `s v`. -/
def IsOptimal (P : Params) (π v : ℝ) (s : ℝ → ℝ) (a : Policy) : Prop :=
  Feasible P π v a ∧ objective P π s a = s v

/-- The credit (CDS) spread `1 − s/s*` ((7), p. 20). -/
noncomputable def creditSpread (P : Params) (s : ℝ → ℝ) (v : ℝ) : ℝ := 1 - s v / P.sStar

end VolDisclosure.Evidence


