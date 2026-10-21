-- Prove2me | Definitions.Def_VWAPContract_Optimal_Model
-- name    : VWAPContract_Optimal_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T05:48:10.479669+00:00
-- url     : https://prove2.me/theorems/00242777-b53e-4ca7-b239-1394200c5a14
-- title:
--   §3.1–§3.2, §4.1, §5.1, pp. 8–21 — client–dealer execution contracting: specialized model, static policies, contracts, (IR), (IC), optimality, $x^{FB}$, $\tau^{VWAP}$
-- statement:
--   A client commissions a dealer to buy one share of a security over $T\ge1$ trading periods. This definition fixes the specialized model of §4.1 together with the contracting problem of §3.2 and the first-best notion of §5.1.
--
--   **Primitives.** On a probability space $(\Omega,\mathcal F,\mathbb P)$ there are random vectors $\eta=(\eta_t)_{t=1}^T$ (market conditions, observed by the dealer after contracting and before trading) and $\varepsilon=(\varepsilon_t)_{t=1}^T$ (price shocks, observed by nobody), a constant $\mu$, a price-impact function $h$, a volume function $v(x,\eta)$ with its profile $V$, and the dealer's utility over money $u$.
--
--   **Standing assumptions.**
--   1. Every $\eta_t$ is strictly positive, and $\mathbb E[\varepsilon_t\mid\eta]=\mu$ almost surely for every $t$.
--   2. $h$ is strictly increasing on $[0,\infty)$ and $y\mapsto y\,h(y)$ is strictly convex on $[0,\infty)$.
--   3. $v(x,\eta)>0$ for $x\ge0,\ \eta>0$, and $v(x,\eta)=x\,V(x/\eta)$ for $x>0$, with $V$ strictly decreasing on $(0,\infty)$.
--   4. $u$ is strictly increasing and (weakly) concave.
--
--   **Schedules, policies and outcomes.** A trading schedule is a vector $x\in\mathbb R^T$ with $x_t\ge0$ and $\sum_t x_t=1$. A static trading policy is a measurable map $x(\cdot)$ assigning a schedule to every positive market-condition vector. Under the policy $x(\cdot)$, prices, market volumes and the dealer's trading cost are
--
--   $$p_t=h\!\left(\frac{x_t(\eta)}{\eta_t}\right)+\varepsilon_t,\qquad v_t=v(x_t(\eta),\eta_t),\qquad p\cdot x(\eta)=\sum_{t=1}^T p_t\,x_t(\eta).$$
--
--   **Contracts and the client's problem.** A contract is a measurable function $\tau(p,v)$; the client pays $\tau(p,v)$ to the dealer, whose expected utility is $\mathbb E[u(\tau(p,v)-p\cdot x(\eta))]$. A pair $(\tau,x(\cdot))$ is feasible if the payment, the trading cost and the dealer's utility are integrable and
--
--   $$\mathbb E\big[u(\tau-p\cdot x)\big]\ge u(0)\ \ \text{(IR)},\qquad \mathbb E\big[u(\tau-p\cdot x)\big]\ge \mathbb E\big[u(\tau-p\cdot\hat x)\big]\ \text{for every static policy }\hat x(\cdot)\ \ \text{(IC)}.$$
--
--   A contract $\tau$ is optimal if it is part of a feasible pair $(\tau,x(\cdot))$ whose expected payment $\mathbb E[\tau(p,v)]$ is no larger than that of any other feasible pair.
--
--   **Benchmarks.** A policy is first best if its expected trading cost conditional on $\eta$ is almost surely no larger than that of any other policy. The volume-participation policy and the guaranteed VWAP contract are
--
--   $$x^{FB}_t(\eta)=\frac{\eta_t}{\sum_{s=1}^T\eta_s},\qquad \tau^{VWAP}(p,v)=\frac{\sum_{t=1}^T p_t v_t}{\sum_{s=1}^T v_s}.$$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Periods are indexed by `Fin T` (index $t-1$ is period $t$), and $T\ge1$ is assumed. Added to the paper's assumptions, as Lean needs them to make expectations meaningful: measurability of $\eta,\varepsilon,h,v$; integrability of each $\varepsilon_t$ and of $h(1/\sum_t\eta_t)$ (the first-best cost of Lemma 3 is finite); integrability of payment, cost and utility inside feasibility; and (IC) quantifies over static deviations whose dealer utility is integrable (under $\tau^{VWAP}$ every other deviation has expected utility $-\infty$, and for other contracts the restriction only enlarges the feasible set). Policies need to be schedules only at positive $\eta$, since $\eta$ is positive; contracts are measurable on all of $\mathbb R^T\times\mathbb R^T$, which loses nothing because realized volumes are positive. The domain of $v$ is all of $[0,\infty)\times(0,\infty)$. "First best" compares conditional expected costs against every policy with integrable cost, which is equivalent to the page's pointwise $\arg\min$ over schedules (FB). The paper's $\eta$ and $\varepsilon$ need no further distributional assumption, and none is made.
-- source:
--   Baldauf, Frei & Mollner, Principal trading arrangements: When are common contracts optimal?, working paper of August 8, 2020 (published Management Science 2022, DOI 10.1287/mnsc.2021.4022), pp. 8–21 (PDF 9–22), §3.1, §3.2, §4.1, §5.1 (constraints (IR), (IC), (FB))

import Mathlib

open MeasureTheory

namespace VWAPContract.Optimal

noncomputable section

structure Model (T : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  P : Measure Ω
  eta : Ω → Fin T → ℝ
  eps : Ω → Fin T → ℝ
  mu : ℝ
  h : ℝ → ℝ
  vol : ℝ → ℝ → ℝ
  V : ℝ → ℝ
  u : ℝ → ℝ

def IsSchedule {T : ℕ} (x : Fin T → ℝ) : Prop :=
  (∀ t, 0 ≤ x t) ∧ ∑ t, x t = 1

def IsPolicy {T : ℕ} (X : (Fin T → ℝ) → (Fin T → ℝ)) : Prop :=
  Measurable X ∧ ∀ e : Fin T → ℝ, (∀ t, 0 < e t) → IsSchedule (X e)

def IsContract {T : ℕ} (τ : (Fin T → ℝ) → (Fin T → ℝ) → ℝ) : Prop :=
  Measurable (Function.uncurry τ)

abbrev etaAlg {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Model T Ω) : MeasurableSpace Ω :=
  MeasurableSpace.comap M.eta inferInstance

def Model.Standing {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Model T Ω) : Prop :=
  IsProbabilityMeasure M.P ∧
  0 < T ∧
  Measurable M.eta ∧
  Measurable M.eps ∧
  (∀ ω t, 0 < M.eta ω t) ∧
  (∀ t, Integrable (fun ω => M.eps ω t) M.P) ∧
  (∀ t, M.P[fun ω => M.eps ω t | etaAlg M] =ᵐ[M.P] fun _ => M.mu) ∧
  Measurable M.h ∧
  StrictMonoOn M.h (Set.Ici 0) ∧
  StrictConvexOn ℝ (Set.Ici 0) (fun y => y * M.h y) ∧
  Measurable (Function.uncurry M.vol) ∧
  (∀ x e, 0 ≤ x → 0 < e → 0 < M.vol x e) ∧
  (∀ x e, 0 < x → 0 < e → M.vol x e = x * M.V (x / e)) ∧
  StrictAntiOn M.V (Set.Ioi 0) ∧
  StrictMono M.u ∧
  ConcaveOn ℝ Set.univ M.u ∧
  Integrable (fun ω => M.h (1 / ∑ t, M.eta ω t)) M.P

def price {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Model T Ω) (X : (Fin T → ℝ) → (Fin T → ℝ)) (ω : Ω) : Fin T → ℝ :=
  fun t => M.h (X (M.eta ω) t / M.eta ω t) + M.eps ω t

def mktVol {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Model T Ω) (X : (Fin T → ℝ) → (Fin T → ℝ)) (ω : Ω) : Fin T → ℝ :=
  fun t => M.vol (X (M.eta ω) t) (M.eta ω t)

def cost {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Model T Ω) (X : (Fin T → ℝ) → (Fin T → ℝ)) (ω : Ω) : ℝ :=
  ∑ t, price M X ω t * X (M.eta ω) t

def pay {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Model T Ω) (τ : (Fin T → ℝ) → (Fin T → ℝ) → ℝ)
    (X : (Fin T → ℝ) → (Fin T → ℝ)) (ω : Ω) : ℝ :=
  τ (price M X ω) (mktVol M X ω)

def dealerUtil {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Model T Ω) (τ : (Fin T → ℝ) → (Fin T → ℝ) → ℝ)
    (X : (Fin T → ℝ) → (Fin T → ℝ)) (ω : Ω) : ℝ :=
  M.u (pay M τ X ω - cost M X ω)

noncomputable def dealerEU {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Model T Ω) (τ : (Fin T → ℝ) → (Fin T → ℝ) → ℝ)
    (X : (Fin T → ℝ) → (Fin T → ℝ)) : ℝ :=
  ∫ ω, dealerUtil M τ X ω ∂M.P

def IR {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Model T Ω) (τ : (Fin T → ℝ) → (Fin T → ℝ) → ℝ)
    (X : (Fin T → ℝ) → (Fin T → ℝ)) : Prop :=
  M.u 0 ≤ dealerEU M τ X

def IC {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Model T Ω) (τ : (Fin T → ℝ) → (Fin T → ℝ) → ℝ)
    (X : (Fin T → ℝ) → (Fin T → ℝ)) : Prop :=
  ∀ Y, IsPolicy Y → Integrable (dealerUtil M τ Y) M.P →
    dealerEU M τ Y ≤ dealerEU M τ X

def Feasible {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Model T Ω) (τ : (Fin T → ℝ) → (Fin T → ℝ) → ℝ)
    (X : (Fin T → ℝ) → (Fin T → ℝ)) : Prop :=
  IsContract τ ∧ IsPolicy X ∧
  Integrable (pay M τ X) M.P ∧
  Integrable (cost M X) M.P ∧
  Integrable (dealerUtil M τ X) M.P ∧
  IR M τ X ∧ IC M τ X

def IsOptimal {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Model T Ω) (τ : (Fin T → ℝ) → (Fin T → ℝ) → ℝ) : Prop :=
  ∃ X, Feasible M τ X ∧
    ∀ τ' X', Feasible M τ' X' →
      (∫ ω, pay M τ X ω ∂M.P) ≤ (∫ ω, pay M τ' X' ω ∂M.P)

def IsFirstBest {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Model T Ω) (X : (Fin T → ℝ) → (Fin T → ℝ)) : Prop :=
  IsPolicy X ∧ Integrable (cost M X) M.P ∧
    ∀ Y, IsPolicy Y → Integrable (cost M Y) M.P →
      M.P[cost M X | etaAlg M] ≤ᵐ[M.P] M.P[cost M Y | etaAlg M]

noncomputable def xFB {T : ℕ} (e : Fin T → ℝ) : Fin T → ℝ :=
  fun t => e t / ∑ s, e s

noncomputable def tauVWAP {T : ℕ} (p v : Fin T → ℝ) : ℝ :=
  (∑ t, p t * v t) / ∑ s, v s

end

end VWAPContract.Optimal


