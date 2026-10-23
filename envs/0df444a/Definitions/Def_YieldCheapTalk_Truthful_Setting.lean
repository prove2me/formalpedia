-- Prove2me | Definitions.Def_YieldCheapTalk_Truthful_Setting
-- name    : YieldCheapTalk_Truthful_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:29:58.421263+00:00
-- url     : https://prove2.me/theorems/2fb7ae3f-80f7-4462-874a-c42e73344e2c
-- title:
--   §3, pp. 5–10 — two-type random-yield cheap-talk model, profits (1)–(2), perfect Bayesian equilibrium, Qʳ (3) and the IC condition (5)
-- statement:
--   This file fixes the model of Lu's cheap-talk game between a supplier with random production yield and a buyer who orders from her.
--
--   **Types and states.** The supplier's type and the market state both range over $T = M = \{H, L\}$. A type-$t$ supplier delivers $\xi_t Q$ effective units when $Q$ units are ordered, where the yield $\xi_t$ is a random variable on $[0,1]$ with mean $\theta_t$ and coefficient of variation $\delta$, i.e. variance $\sigma_t^2 = \delta^2\theta_t^2$. The buyer faces the inverse demand $P(x\mid m) = a_m - bx$ in market state $m$. Type and state are drawn from a joint distribution $(p_{tm})$, with
--   $$\mu(m\mid t) = \frac{p_{tm}}{\sum_{m'\in M} p_{tm'}}, \qquad \lambda(t\mid m) = \frac{p_{tm}}{\sum_{\hat t\in T} p_{\hat t m}}.$$
--   Under the contract $(w,\eta)$ the buyer pays $\eta w$ per unit ordered and $(1-\eta)w$ per effective unit delivered; the supplier pays $c$ per unit of input.
--
--   **Profits.** With posterior belief $\beta(t\mid t', m)$ after the message $t'$ in state $m$, the buyer's expected profit (1) is
--   $$\Pi_B(Q\mid t', m) = \sum_{t\in T}\beta(t\mid t', m)\, E_{\xi_t}\big[\xi_t Q\,P(\xi_t Q\mid m) - \eta w Q - (1-\eta) w \xi_t Q\big],$$
--   and, given an ordering strategy $Q^*(t', m)$, the type-$t$ supplier's expected profit (2) from sending $t'$ is
--   $$\Pi_S(t'\mid t) = \sum_{m\in M}\mu(m\mid t)\, E_{\xi_t}\big[(\eta w + (1-\eta)w\xi_t - c)\,Q^*(t', m)\big].$$
--
--   **Standing assumptions** (§3 and p. 12): $\theta_H > \theta_L$; each $\xi_t$ is a probability law carried by $[0,1]$ with the stated mean and variance; $0 \le \eta \le 1$; $p_{tm} > 0$ and $\sum_{t,m} p_{tm} = 1$; $a_m\theta_t > \eta w + (1-\eta)w\theta_t > c$ for all $m, t$; and $a_H > a_L$. In addition $b > 0$ and $w > 0$.
--
--   **Equilibrium** (pp. 8–9). A messaging strategy $r : T \to T$, an ordering strategy $Q^*$ and beliefs $\beta$ form a perfect Bayesian equilibrium (PBE) if (i) $r(t) \in \arg\max_{t'} \Pi_S(t'\mid t)$ for each $t$; (ii) $Q^*(t', m) \in \arg\max_{Q\ge 0}\Pi_B(Q\mid t', m)$ for all $t', m$; and (iii) whenever $\sum_{\hat t}\mathbf 1(r(\hat t) = t')\lambda(\hat t\mid m) > 0$,
--   $$\beta(t\mid t', m) = \frac{\mathbf 1(r(t)=t')\,\lambda(t\mid m)}{\sum_{\hat t\in T}\mathbf 1(r(\hat t)=t')\,\lambda(\hat t\mid m)},$$
--   with no restriction off the equilibrium path. A PBE is *truth-revealing* if $r(t) = t$ for all $t$.
--
--   **Closed forms.** The file also defines the expression (3),
--   $$Q^r(\theta, a) = \frac{[a - (1-\eta)w]\theta - \eta w}{2b(1+\delta^2)\theta^2},$$
--   and the IC condition (5): for all $t \ne t'$,
--   $$Q^r(\theta_t, a_H)\mu(H\mid t) + Q^r(\theta_t, a_L)\mu(L\mid t) \ge Q^r(\theta_{t'}, a_H)\mu(H\mid t) + Q^r(\theta_{t'}, a_L)\mu(L\mid t).$$
--   $Q^r$ is only a formula here; that it is the buyer's optimal order is Proposition 1, a separate statement.
--
--   These objects are shared by every statement of the mission: the goal (Proposition 2) and its milestones are all about this model.
--
--   **Formalization Note.** `Level` encodes both $T$ and $M$. Yields are given by their laws `xi t : Measure ℝ` and expectations are integrals against them. The coefficient of variation $\delta$ is encoded as on p. 6 by the variance $\delta^2\theta_t^2$ ($\delta = 0$, a deterministic yield, is allowed). The cost in (2) is the base model's single $c$ (the page writes $c_t$ for the type-dependent extension). `Standing` adds $b > 0$ and $w > 0$, which the paper uses tacitly; with $w > 0$ the assumption $a_m\theta_t > \eta w + (1-\eta)w\theta_t$ forces $\theta_t > 0$, so every reciprocal is a genuine one. Beliefs in `IsPBE` are required to be probability distributions on $T$; condition (ii) ranges over every $Q' \ge 0$. `profitYield ν a Q` is the expectation inside (1) for a yield law $\nu$ and potential $a$.
-- source:
--   Lu, Can a Supplier’s Yield Risk Be Truthfully Communicated via Cheap Talk?, author manuscript of 14 July 2024 (MSOM, doi:10.1287/msom.2023.0089), pp. 6–11, (1)–(3), (5), PBE (i)–(iii) on pp. 8–9, standing assumption a_H > a_L on p. 12

import Mathlib

namespace YieldCheapTalk.Truthful
open MeasureTheory

/-- `T = M = {H, L}`: the supplier's types and the market states (§3, p. 6). -/
inductive Level
  | H
  | L
  deriving DecidableEq

instance : Fintype Level where
  elems := {Level.H, Level.L}
  complete := fun x => by cases x <;> simp

/-- §3, pp. 6–7: the primitives of the model. `a m` is the market potential `a_m`, `b` the slope of
the inverse demand `P(x|m) = a_m − b x`, `theta t` the mean yield `θ_t`, `delta` the common
coefficient of variation `δ`, `c` the unit production cost, `(w, eta)` the contract `(w, η)`,
`p t m` the joint probability `p_tm` of type `t` and state `m`, and `xi t` the law of the yield
`ξ_t`. -/
structure Model where
  a : Level → ℝ
  b : ℝ
  theta : Level → ℝ
  delta : ℝ
  c : ℝ
  w : ℝ
  eta : ℝ
  p : Level → Level → ℝ
  xi : Level → Measure ℝ

namespace Model
variable (M : Model)

/-- `µ(m|t) = p_tm / Σ_{m'} p_tm'`, the probability of state `m` given type `t` (p. 8). -/
noncomputable def mu (m t : Level) : ℝ := M.p t m / ∑ m', M.p t m'

/-- `λ(t|m) = p_tm / Σ_{t̂} p_t̂m`, the buyer's prior on type `t` given state `m` (p. 9). -/
noncomputable def lam (t m : Level) : ℝ := M.p t m / ∑ t', M.p t' m

/-- The standing assumptions of §3 (pp. 6–8) together with `a_H > a_L` (p. 12, "henceforth").
`b > 0` and `w > 0` are added (disclosed). The coefficient of variation `δ` of `ξ_t` is encoded,
as on p. 6, by the variance `σ_t² = δ² θ_t²`. -/
structure Standing : Prop where
  b_pos : 0 < M.b
  w_pos : 0 < M.w
  theta_lt : M.theta .L < M.theta .H
  isProb : ∀ t, IsProbabilityMeasure (M.xi t)
  support : ∀ t, ∀ᵐ x ∂(M.xi t), x ∈ Set.Icc (0 : ℝ) 1
  mean : ∀ t, ∫ x, x ∂(M.xi t) = M.theta t
  var : ∀ t, ∫ x, (x - M.theta t) ^ 2 ∂(M.xi t) = M.delta ^ 2 * M.theta t ^ 2
  eta_mem : M.eta ∈ Set.Icc (0 : ℝ) 1
  p_pos : ∀ t m, 0 < M.p t m
  p_sum : ∑ t, ∑ m, M.p t m = 1
  buyer_pos : ∀ m t, M.eta * M.w + (1 - M.eta) * M.w * M.theta t < M.a m * M.theta t
  supplier_pos : ∀ t, M.c < M.eta * M.w + (1 - M.eta) * M.w * M.theta t
  a_lt : M.a .L < M.a .H

/-- The buyer's expected profit from ordering `Q` when the yield has law `ν` and the market
potential is `a`: `E[ξQ(a − bξQ) − ηwQ − (1 − η)wξQ]`, the expectation inside (1). -/
noncomputable def profitYield (ν : Measure ℝ) (a Q : ℝ) : ℝ :=
  ∫ x, (x * Q * (a - M.b * (x * Q)) - M.eta * M.w * Q - (1 - M.eta) * M.w * x * Q) ∂ν

/-- (1), p. 7: `Π_B(Q|t', m) = Σ_t β(t|t', m) E_{ξ_t}[…]`, where `beta t t' m = β(t|t', m)`. -/
noncomputable def profitB (beta : Level → Level → Level → ℝ) (Q : ℝ) (t' m : Level) : ℝ :=
  ∑ t, beta t t' m * M.profitYield (M.xi t) (M.a m) Q

/-- (2), p. 8, with the base model's single unit cost `c`:
`Π_S(t'|t) = Σ_m µ(m|t) E_{ξ_t}[(ηw + (1 − η)wξ_t − c) Q*(t', m)]`, where `Q t' m = Q*(t', m)`. -/
noncomputable def profitS (Q : Level → Level → ℝ) (t' t : Level) : ℝ :=
  ∑ m, M.mu m t * ∫ x, (M.eta * M.w + (1 - M.eta) * M.w * x - M.c) * Q t' m ∂(M.xi t)

/-- The perfect Bayesian equilibrium of pp. 8–9: messaging strategy `r`, ordering strategy
`Q t' m = Q*(t', m)` and beliefs `beta t t' m = β(t|t', m)` satisfy (i) the supplier's
optimality, (ii) the buyer's optimality over all `Q ≥ 0`, and (iii) Bayes' rule on the
equilibrium path, with no restriction off path; beliefs are probability distributions on `T`. -/
def IsPBE (r : Level → Level) (Q : Level → Level → ℝ) (beta : Level → Level → Level → ℝ) :
    Prop :=
  (∀ t t', M.profitS Q t' t ≤ M.profitS Q (r t) t) ∧
  (∀ t' m, 0 ≤ Q t' m ∧ ∀ Q', 0 ≤ Q' → M.profitB beta Q' t' m ≤ M.profitB beta (Q t' m) t' m) ∧
  (∀ t t' m, 0 ≤ beta t t' m) ∧ (∀ t' m, ∑ t, beta t t' m = 1) ∧
  (∀ t' m, 0 < ∑ s, (if r s = t' then (1 : ℝ) else 0) * M.lam s m →
    ∀ t, beta t t' m = (if r t = t' then (1 : ℝ) else 0) * M.lam t m /
      ∑ s, (if r s = t' then (1 : ℝ) else 0) * M.lam s m)

/-- (3), p. 10, as a closed form:
`Qʳ(θ, a) = ([a − (1 − η)w]θ − ηw) / (2b(1 + δ²)θ²)`. -/
noncomputable def Qr (θ a : ℝ) : ℝ :=
  ((a - (1 - M.eta) * M.w) * θ - M.eta * M.w) / (2 * M.b * (1 + M.delta ^ 2) * θ ^ 2)

/-- The IC condition (5), p. 11: for all `t ≠ t'`,
`Qʳ(θ_t, a_H)µ(H|t) + Qʳ(θ_t, a_L)µ(L|t) ≥ Qʳ(θ_t', a_H)µ(H|t) + Qʳ(θ_t', a_L)µ(L|t)`. -/
def IC5 : Prop := ∀ t t' : Level, t ≠ t' →
  M.Qr (M.theta t') (M.a .H) * M.mu .H t + M.Qr (M.theta t') (M.a .L) * M.mu .L t ≤
    M.Qr (M.theta t) (M.a .H) * M.mu .H t + M.Qr (M.theta t) (M.a .L) * M.mu .L t

end Model
end YieldCheapTalk.Truthful


