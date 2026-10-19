-- Prove2me | Definitions.Def_AddictivePlatforms_Costly_Model
-- name    : AddictivePlatforms_Costly_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T14:37:44.860114+00:00
-- url     : https://prove2.me/theorems/210b26ac-304e-4dae-a41c-e07e87559643
-- title:
--   §2, Assumptions 1–3, (1)–(3), Definition 1, App. D (A.6), (A.9)–(A.11) — the attention game with costly addictiveness, SPE, joint-profit outcome, A(D), d¹, d¹_J, d²_J
-- statement:
--   The model of Section 5 of Ichihashi and Kim. There are $K$ platforms and one consumer. Each platform $k$ chooses an **addictiveness** $d_k \ge 0$ at cost $\kappa\gamma(d_k)$; the consumer observes $d = (d_1,\dots,d_K)$, joins a set $J$ of platforms and allocates attention $a_k \ge 0$ to each $k \in J$. Her payoff is $0$ if $J = \emptyset$ and otherwise
--   $$\sum_{k\in J} u(a_k, d_k) - C\Big(\sum_{k\in J} a_k\Big), \qquad (1)$$
--   subject to the attention cap $\sum_{k\in J} a_k \le \overline{A}$ with $\overline{A} \in \mathbb{R}_+ \cup \{\infty\}$ (problem (2)). Platform $k$ earns $a_k - \kappa\gamma(d_k)$, where $a_k$ counts only if the consumer joins $k$.
--
--   **Assumption 1** (on $u : \mathbb{R}_+^2 \to \mathbb{R}$, twice differentiable): (a) $u(\cdot,d)$ is strictly increasing and concave for every $d \ge 0$, and $u(0,0) \ge 0$; (b) $u(a,\cdot)$ is strictly decreasing for every $a \ge 0$, and $\max_{a\ge0}[u(a,d)-C(a)] < 0$ for some $d \ge 0$; (c) $u_1(a,d) = \partial u/\partial a$ is strictly increasing in $d$. **Assumption 2** (on $C : \mathbb{R}_+ \to \mathbb{R}_+$): $C$ is strictly increasing, convex, twice differentiable, and $\lim_{a\to0}[u_1(a,0) - C'(a)] > 0$ (possibly $+\infty$). **Assumption 3**: $u(a,d) = v(a-d)$; $\gamma : \mathbb{R}_+ \to \mathbb{R}_+$ is increasing, strictly convex and differentiable with $\lim_{d\to0}\gamma'(d) = 0$ and $\lim_{d\to\infty}\gamma'(d) = \infty$; $g$ is the inverse of $v'$, and $g'(C'(x))\,C''(x)$ is weakly decreasing in $x$. The cost scale is $\kappa > 0$.
--
--   The file defines:
--   1. the consumer's payoff (1), feasibility and optimality for (2), consumer strategies (a choice at every profile) and the platforms' payoffs;
--   2. **pure-strategy subgame perfect equilibrium** $(d,\sigma)$: $d \ge 0$, the consumer solves (2) at every profile $d' \ge 0$, and no platform gains by deviating to any $x \ge 0$; consumer surplus is the payoff (1) of $\sigma(d)$ at $d$;
--   3. **the joint-profit maximizing outcome** (Definition 1): the consumer chooses only between joining all platforms (with an optimal feasible attention profile) and joining none, at every profile; $d$ maximizes the sum of the platforms' profits over all $d' \ge 0$; and among maximizers the platforms break ties for the consumer;
--   4. the maximizers $A_K(d)$ of $K u(A/K,d) - C(A)$ over $A \in [0,\overline{A}]$ and the indifference equation (3) between joining $K$ and $K-1$ platforms;
--   5. the objects of Appendix D: $\min\{A,\overline{A}\}$ as a real number, the characterization $A(D) - D = K g(C'(A(D)))$ of $A(\cdot)$, the attention profile (A.6) $a_k = \frac1K[\min\{A(D),\overline{A}\} - D] + d_k$ with $D = \sum_k d_k$, optimality of an attention profile on all $K$ platforms, the function $\Pi(x,d)$ of (A.10), the fixed-point condition (A.9) defining $d^1$, the problem (A.11) defining $d^1_J$, and the level $d^2_J$ at which the consumer's best payoff from joining all platforms is zero.
--
--   These are the objects of every statement in the mission.
--
--   **Formalization Note.** Platforms are `Fin K`, with the paper's platform 1 the index `0`. The cap is an extended nonnegative real `ℝ≥0∞`, compared with real totals through `ENNReal.ofReal`; $\min\{A,\overline{A}\}$ is computed in `ℝ≥0∞` and converted back (it is $A$ when $\overline{A} = \infty$). Derivatives of $u$, $C$, $\gamma$ on $\mathbb{R}_+$ are one-sided (`derivWithin … (Ici 0)`); $v$ lives on $\mathbb{R}$ and $v'$ is the two-sided derivative. The standing bundle adds disclosed pins to Assumptions 1–3: $u(\cdot,d)$ is *strictly* concave; $C(0) = 0$; the uncapped consumer problem has an optimal attention profile for every profile and every nonempty $J$ (the paper assumes this on p. 6 for $\overline{A} = \infty$); "$g$ is the inverse of $v'$" is read as $g(v'(x)) = x$ for all $x$ and $v'(g(C'(x))) = C'(x)$ for $x \ge 0$, with $g$ differentiable at each $C'(x)$. The platform's cost $\kappa\gamma(d_k)$ is paid whether or not the consumer joins it. $\kappa > 0$ is a hypothesis of each statement rather than part of the bundle.
-- source:
--   Ichihashi & Kim, Addictive Platforms, Bank of Canada SWP 2022-16 (Apr. 1, 2022), pp. 4–7 (Assumptions 1–2, (1)–(2), solution concept), p. 11 (A_K(d), (3)), p. 14 (Definition 1), p. 16 (Assumption 3), pp. 33–36 (platform payoff, (A.6), (A.9)–(A.11))

import Mathlib
import Definitions.Def_AddictivePlatforms_Compete_Model

open Set Filter Topology
open scoped ENNReal

namespace AddictivePlatforms.Costly

/-! # The attention-competition game with costly addictiveness

Ichihashi & Kim, *Addictive Platforms*, Bank of Canada Staff Working Paper 2022-16 (Apr. 1, 2022):
§2 (pp. 4–7), (3) (p. 11), Definition 1 (p. 14), §5 and Assumption 3 (p. 16), Appendix D (pp. 33–37).

Conventions.
* `K` platforms are `Fin K`; the paper's "platform 1" is the index `0`.
* `u a d` is the paper's `u(a, d)` (attention first, addictiveness second); in this section
  `u(a, d) = v(a − d)` (Assumption 3), written `uOf v`. `C` is the attention cost, `γ` the cost of
  addictiveness and `κ` its scale. Only values on `ℝ₊` (resp. `ℝ₊²`) matter for `u`, `C`, `γ`.
* The attention cap `Ā ∈ ℝ₊ ∪ {∞}` is `Abar : ℝ≥0∞`; real totals are compared with it through
  `ENNReal.ofReal`.
* Derivatives on `ℝ₊` are one-sided: `derivWithin … (Ici 0)`. `v` is defined on all of `ℝ`
  (`a − d` can be negative) and its derivative is the two-sided `deriv v`.
-/

/-- The second derivative `C″(a)`, one-sided on `ℝ₊`. -/
noncomputable def Cderiv2 (C : ℝ → ℝ) (a : ℝ) : ℝ :=
  derivWithin (AddictivePlatforms.Compete.Cderiv C) (Ici 0) a

/-- The utility of Assumption 3 (p. 16): `u(a, d) = v(a − d)`. -/
def uOf (v : ℝ → ℝ) : ℝ → ℝ → ℝ := fun a d => v (a - d)

/-- **Assumption 3** (p. 16), apart from `κ > 0` (which the statements carry as a hypothesis on the
cost scale `κ`) and `u(a, d) = v(a − d)` (which the statements impose by using `uOf v`).
`γ : ℝ₊ → ℝ₊` is increasing (weakly), strictly convex and differentiable, with
`lim_{d→0} γ′(d) = 0` and `lim_{d→∞} γ′(d) = ∞`; `g` is the inverse of `v′`, and
`g′(C′(x)) C″(x)` is weakly decreasing in `x ≥ 0`.

Pin (disclosed): "`g` is the inverse of `v′`" is encoded as `g (v′ x) = x` for every `x` and
`v′ (g (C′ x)) = C′ x` for every `x ≥ 0` (so `g` is defined at the values `C′(x)` it is applied to),
and `g` is differentiable at each `C′(x)`, `x ≥ 0` (so that `g′(C′(x))` is meaningful). -/
structure Assumption3 (v : ℝ → ℝ) (C : ℝ → ℝ) (γ : ℝ → ℝ) (g : ℝ → ℝ) : Prop where
  /-- `γ : ℝ₊ → ℝ₊`. -/
  γ_nonneg : ∀ d : ℝ, 0 ≤ d → 0 ≤ γ d
  /-- `γ` is increasing (weakly). -/
  γ_monotoneOn : MonotoneOn γ (Ici 0)
  γ_strictConvexOn : StrictConvexOn ℝ (Ici 0) γ
  γ_differentiableOn : DifferentiableOn ℝ γ (Ici 0)
  /-- `lim_{d → 0⁺} γ′(d) = 0`. -/
  γ_deriv_zero : Tendsto (derivWithin γ (Ici 0)) (𝓝[>] 0) (𝓝 0)
  /-- `lim_{d → ∞} γ′(d) = ∞`. -/
  γ_deriv_atTop : Tendsto (derivWithin γ (Ici 0)) atTop atTop
  /-- `g` is a left inverse of `v′`. -/
  g_leftInv : ∀ x : ℝ, g (deriv v x) = x
  /-- `g` inverts `v′` at every value `C′(x)`, `x ≥ 0`. -/
  g_rightInv : ∀ x : ℝ, 0 ≤ x → deriv v (g (AddictivePlatforms.Compete.Cderiv C x)) = AddictivePlatforms.Compete.Cderiv C x
  /-- `g` is differentiable at every `C′(x)`, `x ≥ 0`. -/
  g_differentiableAt : ∀ x : ℝ, 0 ≤ x → DifferentiableAt ℝ g (AddictivePlatforms.Compete.Cderiv C x)
  /-- `g′(C′(x)) C″(x)` is weakly decreasing in `x ≥ 0`. -/
  antitoneOn : AntitoneOn (fun x => deriv g (AddictivePlatforms.Compete.Cderiv C x) * Cderiv2 C x) (Ici 0)

/-- The standing hypotheses of §5 for `K` platforms: Assumptions 1 and 2 for `u = uOf v`,
Assumption 3, and three disclosed pins: `u(·, d)` is *strictly* concave on `ℝ₊` for every `d ≥ 0`,
`C(0) = 0`, and the consumer's unconstrained problem has an optimum (`UncOptExists`). -/
structure Standing (v : ℝ → ℝ) (C : ℝ → ℝ) (γ : ℝ → ℝ) (g : ℝ → ℝ) (K : ℕ) : Prop where
  assumption1 : AddictivePlatforms.Compete.Assumption1 (uOf v) C
  assumption2 : AddictivePlatforms.Compete.Assumption2 (uOf v) C
  assumption3 : Assumption3 v C γ g
  /-- Pin: strict concavity of `u(·, d)` on `ℝ₊` for every `d ≥ 0`. -/
  strictConcaveOn_a : ∀ d : ℝ, 0 ≤ d → StrictConcaveOn ℝ (Ici 0) (fun a => uOf v a d)
  /-- Pin: `C(0) = 0`. -/
  C_zero : C 0 = 0
  /-- Pin: existence of the consumer's unconstrained optimum (p. 6). -/
  uncOptExists : AddictivePlatforms.Compete.UncOptExists (uOf v) C K

/-- Platform `k`'s payoff in §5 (p. 33, with `r = 1`): `a_k − κ γ(d_k)`, where the attention `a_k`
counts only if the consumer joins `k`. Pin (disclosed): the cost `κ γ(d_k)` is incurred whether
or not the consumer joins `k`. -/
noncomputable def platformPayoff {K : ℕ} (γ : ℝ → ℝ) (κ : ℝ) (d : Fin K → ℝ) (k : Fin K)
    (x : AddictivePlatforms.Compete.Choice K) : ℝ :=
  (if k ∈ x.1 then x.2 k else 0) - κ * γ (d k)

/-- Pure-strategy subgame perfect equilibrium (p. 7) of the game with cost `κ γ(d)`, with platform
profile `d` and consumer strategy `σ`: every `d_k ≥ 0`; the consumer solves (2) at **every** profile
of nonnegative addictiveness (on and off the path); and no platform `k` has a profitable unilateral
deviation to any `x ≥ 0`. -/
def IsSPE {K : ℕ} (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (γ : ℝ → ℝ) (κ : ℝ) (Abar : ℝ≥0∞)
    (d : Fin K → ℝ) (σ : AddictivePlatforms.Compete.ConsumerStrategy K) : Prop :=
  (∀ k, 0 ≤ d k) ∧
    (∀ d' : Fin K → ℝ, (∀ k, 0 ≤ d' k) → AddictivePlatforms.Compete.ConsumerOpt u C Abar d' (σ d')) ∧
    ∀ (k : Fin K) (x : ℝ), 0 ≤ x →
      platformPayoff γ κ (Function.update d k x) k (σ (Function.update d k x)) ≤
        platformPayoff γ κ d k (σ d)

/-- A choice in the consumer's restricted problem of Definition 1 (p. 14): she joins all platforms
or none, with a feasible attention profile. -/
def RestrictedFeasible {K : ℕ} (Abar : ℝ≥0∞) (x : AddictivePlatforms.Compete.Choice K) : Prop :=
  AddictivePlatforms.Compete.Feasible Abar x ∧ (x.1 = ∅ ∨ x.1 = Finset.univ)

/-- The choice `x` solves the consumer's restricted problem of Definition 1 at the profile `d`:
the best choice among "join all platforms" (with any feasible attention profile) and "join none". -/
def RestrictedOpt {K : ℕ} (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (Abar : ℝ≥0∞) (d : Fin K → ℝ)
    (x : AddictivePlatforms.Compete.Choice K) : Prop :=
  RestrictedFeasible Abar x ∧
    ∀ y : AddictivePlatforms.Compete.Choice K, RestrictedFeasible Abar y → AddictivePlatforms.Compete.payoff u C d y ≤ AddictivePlatforms.Compete.payoff u C d x

/-- The platforms' joint profit at the profile `d` when the consumer chooses `x`. -/
noncomputable def jointProfit {K : ℕ} (γ : ℝ → ℝ) (κ : ℝ) (d : Fin K → ℝ) (x : AddictivePlatforms.Compete.Choice K) : ℝ :=
  ∑ k, platformPayoff γ κ d k x

/-- **Definition 1** (p. 14), the joint-profit maximizing outcome `(d, σ)`: every `d_k ≥ 0`; at every
profile of nonnegative addictiveness the consumer solves the restricted problem (join all or none);
`d` maximizes the sum of the platforms' profits over all profiles of nonnegative addictiveness;
and the platforms break ties for the consumer: every maximizer gives the consumer at most her
payoff at `d`. -/
def IsJPM {K : ℕ} (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (γ : ℝ → ℝ) (κ : ℝ) (Abar : ℝ≥0∞)
    (d : Fin K → ℝ) (σ : AddictivePlatforms.Compete.ConsumerStrategy K) : Prop :=
  (∀ k, 0 ≤ d k) ∧
    (∀ d' : Fin K → ℝ, (∀ k, 0 ≤ d' k) → RestrictedOpt u C Abar d' (σ d')) ∧
    (∀ d' : Fin K → ℝ, (∀ k, 0 ≤ d' k) →
      jointProfit γ κ d' (σ d') ≤ jointProfit γ κ d (σ d)) ∧
    ∀ d' : Fin K → ℝ, (∀ k, 0 ≤ d' k) →
      jointProfit γ κ d' (σ d') = jointProfit γ κ d (σ d) →
      AddictivePlatforms.Compete.consumerSurplus u C d' σ ≤ AddictivePlatforms.Compete.consumerSurplus u C d σ

/-- `min{A, Ā}` as a real number, for `A ≥ 0` and `Ā ∈ ℝ₊ ∪ {∞}` (equal to `A` when `Ā = ∞`). -/
noncomputable def capMin (Abar : ℝ≥0∞) (A : ℝ) : ℝ :=
  (min (ENNReal.ofReal A) Abar).toReal

/-- `AD` is the function `A(·)` of Lemma D.1 (p. 34): for every `D ≥ 0`, `A(D) ≥ 0` solves
`A(D) − D = K g(C′(A(D)))`. -/
def IsAD (C : ℝ → ℝ) (g : ℝ → ℝ) (K : ℕ) (AD : ℝ → ℝ) : Prop :=
  ∀ D : ℝ, 0 ≤ D → 0 ≤ AD D ∧ AD D - D = (K : ℝ) * g (AddictivePlatforms.Compete.Cderiv C (AD D))

/-- The attention profile (A.6) (p. 34) on `K` joined platforms with addictiveness `d`:
`a_k = (1/K) [min{A(D), Ā} − D] + d_k`, where `D = ∑_k d_k`. -/
noncomputable def allocA6 {K : ℕ} (AD : ℝ → ℝ) (Abar : ℝ≥0∞) (d : Fin K → ℝ) (k : Fin K) : ℝ :=
  (1 / (K : ℝ)) * (capMin Abar (AD (∑ j, d j)) - ∑ j, d j) + d k

/-- The attention profile `a` is optimal for the consumer who has joined all `K` platforms with
addictiveness `d` (p. 34): it is feasible (`a ≥ 0`, `∑ a_k ≤ Ā`) and maximizes
`∑_k u(a_k, d_k) − C(∑_k a_k)` among feasible profiles. -/
def IsAllocOpt {K : ℕ} (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (Abar : ℝ≥0∞) (d : Fin K → ℝ)
    (a : Fin K → ℝ) : Prop :=
  AddictivePlatforms.Compete.Feasible Abar ((Finset.univ, a) : AddictivePlatforms.Compete.Choice K) ∧
    ∀ a' : Fin K → ℝ, AddictivePlatforms.Compete.Feasible Abar ((Finset.univ, a') : AddictivePlatforms.Compete.Choice K) →
      AddictivePlatforms.Compete.payoff u C d ((Finset.univ, a') : AddictivePlatforms.Compete.Choice K) ≤ AddictivePlatforms.Compete.payoff u C d ((Finset.univ, a) : AddictivePlatforms.Compete.Choice K)

/-- The function `Π(x, d)` of (A.10) (p. 35):
`(1/K) [min{A(x + (K − 1)d), Ā} − x − (K − 1)d] + x − κ γ(x)`. -/
noncomputable def PiA10 (AD : ℝ → ℝ) (γ : ℝ → ℝ) (κ : ℝ) (Abar : ℝ≥0∞) (K : ℕ) (x d : ℝ) : ℝ :=
  (1 / (K : ℝ)) * (capMin Abar (AD (x + ((K : ℝ) - 1) * d)) - x - ((K : ℝ) - 1) * d) + x -
    κ * γ x

/-- `d¹` satisfies (A.9) (p. 35): `d¹ ≥ 0` and `d¹ ∈ argmax_{x ≥ 0} Π(x, d¹)`. -/
def IsD1 (AD : ℝ → ℝ) (γ : ℝ → ℝ) (κ : ℝ) (Abar : ℝ≥0∞) (K : ℕ) (d1 : ℝ) : Prop :=
  0 ≤ d1 ∧ ∀ x : ℝ, 0 ≤ x → PiA10 AD γ κ Abar K x d1 ≤ PiA10 AD γ κ Abar K d1 d1

/-- `d¹_J` solves (A.11) (p. 36): `d¹_J ≥ 0` maximizes `min{A(K d), Ā} − K κ γ(d)` over `d ≥ 0`. -/
def IsD1J (AD : ℝ → ℝ) (γ : ℝ → ℝ) (κ : ℝ) (Abar : ℝ≥0∞) (K : ℕ) (d1J : ℝ) : Prop :=
  0 ≤ d1J ∧ ∀ d : ℝ, 0 ≤ d →
    capMin Abar (AD ((K : ℝ) * d)) - (K : ℝ) * κ * γ d ≤
      capMin Abar (AD ((K : ℝ) * d1J)) - (K : ℝ) * κ * γ d1J

/-- `d²_J` (p. 36): `d²_J ≥ 0`, and the consumer's best payoff from joining all `K` platforms, all of
addictiveness `d²_J`, is attained and equals `0`. -/
def IsD2J (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (Abar : ℝ≥0∞) (K : ℕ) (d2J : ℝ) : Prop :=
  0 ≤ d2J ∧
    (∃ a : Fin K → ℝ, AddictivePlatforms.Compete.Feasible Abar ((Finset.univ, a) : AddictivePlatforms.Compete.Choice K) ∧
      AddictivePlatforms.Compete.payoff u C (fun _ => d2J) ((Finset.univ, a) : AddictivePlatforms.Compete.Choice K) = 0) ∧
    ∀ a : Fin K → ℝ, AddictivePlatforms.Compete.Feasible Abar ((Finset.univ, a) : AddictivePlatforms.Compete.Choice K) →
      AddictivePlatforms.Compete.payoff u C (fun _ => d2J) ((Finset.univ, a) : AddictivePlatforms.Compete.Choice K) ≤ 0

end AddictivePlatforms.Costly


