-- Prove2me | Definitions.Def_AddictivePlatforms_Compete_Model
-- name    : AddictivePlatforms_Compete_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T12:57:43.516074+00:00
-- url     : https://prove2.me/theorems/44f152f5-709e-4b4a-9f1a-82a529f957c5
-- title:
--   §2, Assumptions 1–2, (1)–(3), §3.1–3.2, (A.1), (A.3), (A.4) — the attention-competition game, consumer optimality, SPE, the monopoly tie-break, A(d), d^A, d^P, Ā^M, A_K(d)
-- statement:
--   The model of Ichihashi and Kim. There are $K$ platforms and one consumer. Each platform $k$ chooses an **addictiveness** $d_k \ge 0$; the consumer observes $d = (d_1,\dots,d_K)$, joins a set $J$ of platforms and allocates attention $a_k \ge 0$ to each $k \in J$. Her payoff is $0$ if $J = \emptyset$ and otherwise
--   $$\sum_{k\in J} u(a_k, d_k) - C\Big(\sum_{k\in J} a_k\Big), \qquad (1)$$
--   and she must respect the attention cap $\sum_{k\in J} a_k \le \overline{A}$ with $\overline{A} \in \mathbb{R}_+ \cup \{\infty\}$, problem (2). Platform $k$ earns $a_k$ if she joins it and $0$ otherwise.
--
--   **Assumption 1** (on $u : \mathbb{R}_+^2 \to \mathbb{R}$, twice differentiable): (a) $u(\cdot, d)$ is strictly increasing and concave for every $d \ge 0$, and $u(0,0) \ge 0$; (b) $u(a, \cdot)$ is strictly decreasing for every $a \ge 0$, and $\max_{a\ge0}[u(a,d) - C(a)] < 0$ for some $d \ge 0$; (c) the marginal utility $u_1(a, d) = \partial u/\partial a$ is strictly increasing in $d$. **Assumption 2** (on $C : \mathbb{R}_+ \to \mathbb{R}_+$): $C$ is strictly increasing, convex and twice differentiable, and $\lim_{a\to 0}[u_1(a,0) - C'(a)] > 0$ (possibly $+\infty$).
--
--   The file defines:
--   1. the consumer's payoff (1), feasibility and optimality for (2), consumer strategies (a choice at every profile $d$) and platform payoffs;
--   2. **pure-strategy subgame perfect equilibrium**: platform profile $d \ge 0$ and consumer strategy $\sigma$ such that $\sigma(d')$ solves (2) at every profile $d' \ge 0$ and no platform gains by a unilateral deviation to any $x \ge 0$; consumer surplus is the payoff (1) of $\sigma(d)$ at $d$;
--   3. **monopoly equilibrium** ($K = 1$): an equilibrium in which the platform breaks ties in favour of the consumer, i.e. every $x \ge 0$ giving the platform its equilibrium payoff gives the consumer at most her equilibrium payoff;
--   4. $A(d) := \arg\max_{A\ge0} u(A,d) - C(A)$, $d^A(\overline{A}) := \min\{d \in [0,\infty] : A(d) \ge \overline{A}\}$, $d^P(\overline{A})$ (the $d$ at which $\max_{A\in[0,\overline{A}]} u(A,d) - C(A) = 0$), and $\overline{A}^M$, the least cap from which on monopoly consumer surplus is zero;
--   5. the problems $\max_{A\in[0,\overline{A}]} y\,u(A/y, d) - C(A)$ of (A.1), whose maximizer at $y = K$ is $A_K(d)$, the indifference equation (3), and the problems (A.3) and (A.4) of Appendix B.
--
--   These are the objects of every statement in the mission.
--
--   **Formalization Note.** Platforms are `Fin K`, with the paper's platform 1 the index `0`. The cap is an extended nonnegative real `ℝ≥0∞`, compared with real totals through `ENNReal.ofReal`. Partial derivatives on $\mathbb{R}_+$ are one-sided (`derivWithin … (Ici 0)`). The standing bundle adds two disclosed pins to Assumptions 1–2: $u(\cdot,d)$ is *strictly* concave (Lemma B.1 needs it and Lemma B.2 applies Lemma B.1 to $u(\cdot,d)$), and $C(0) = 0$ (without it $d^P$ need not exist). A further pin, `UncOptExists`, states the paper's assumption (p. 6) that the uncapped problem has an optimal attention profile for every profile and every nonempty $J$. $A(d)$ is passed to theorems as a function with its maximizing property; $d^A$ and $\overline{A}^M$ are infima in `ℝ≥0∞`, equal to $\infty$ on the empty set (the page's $d = \infty$). Assumption 1(b)'s "$\max_{a\ge0}[u(a,d)-C(a)] < 0$" is written as $u(a,d) - C(a) < 0$ for all $a \ge 0$; the two agree whenever the maximum exists, which the existence pin provides. The objectives of (A.1), (A.3) and (A.4) are defined for all arguments, but the page poses them only for $y > 0$ (resp. $x, y > 0$, and $S \subseteq \{2,\dots,K\}$, i.e. platform 1 not in $S$); every theorem using them carries these restrictions, as well as $K \ge 2$ for (3) and $\overline{A} > 0$ where the page needs it.
-- source:
--   Ichihashi & Kim, Addictive Platforms, Bank of Canada SWP 2022-16 (Apr. 1, 2022), pp. 4–7 (Assumptions 1–2, (1)–(2), solution concept), pp. 10–12 (d^P, A(d), d^A, A_K, (3), Ā^M), pp. 28–30 ((A.1), (A.3), (A.4))

import Mathlib

open Set Filter Topology
open scoped ENNReal

namespace AddictivePlatforms.Compete

/-! # The attention-competition game of Ichihashi & Kim, *Addictive Platforms*

Bank of Canada Staff Working Paper 2022-16 (Apr. 1, 2022), §2 (pp. 4–7), §3.1–3.2 (pp. 10–11)
and Appendix B (pp. 28–30).

Conventions.
* `K` platforms are `Fin K`; the paper's "platform 1" is the index `0`.
* `u a d` is the paper's `u(a, d)` (attention first, addictiveness second); `C` is the attention cost.
  Only their values on `ℝ₊` (resp. `ℝ₊²`) matter.
* The attention cap `Ā ∈ ℝ₊ ∪ {∞}` is `Abar : ℝ≥0∞`; real totals are compared with it through
  `ENNReal.ofReal`.
* Partial derivatives on `ℝ₊` are one-sided: `derivWithin … (Ici 0)`.
-/

/-- The nonnegative quadrant `ℝ₊²`, the domain of `u`. -/
def quadrant : Set (ℝ × ℝ) := Ici (0 : ℝ) ×ˢ Ici (0 : ℝ)

/-- The marginal utility of attention `u₁(a, d) = ∂u/∂a (a, d)`, one-sided on `ℝ₊`. -/
noncomputable def u1 (u : ℝ → ℝ → ℝ) (a d : ℝ) : ℝ :=
  derivWithin (fun x => u x d) (Ici 0) a

/-- The marginal attention cost `C′(a)`, one-sided on `ℝ₊`. -/
noncomputable def Cderiv (C : ℝ → ℝ) (a : ℝ) : ℝ :=
  derivWithin C (Ici 0) a

/-- **Assumption 1** (p. 5), as printed. -/
structure Assumption1 (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) : Prop where
  /-- `u` is (twice) differentiable on `ℝ₊²`: first derivative. -/
  differentiableOn : DifferentiableOn ℝ (Function.uncurry u) quadrant
  /-- `u` is twice differentiable on `ℝ₊²`: the derivative is differentiable. -/
  differentiableOn_fderivWithin :
    DifferentiableOn ℝ (fderivWithin ℝ (Function.uncurry u) quadrant) quadrant
  /-- (a) for every `d ≥ 0`, `u(·, d)` is strictly increasing on `ℝ₊` … -/
  strictMonoOn_a : ∀ d : ℝ, 0 ≤ d → StrictMonoOn (fun a => u a d) (Ici 0)
  /-- (a) … and concave on `ℝ₊` … -/
  concaveOn_a : ∀ d : ℝ, 0 ≤ d → ConcaveOn ℝ (Ici 0) (fun a => u a d)
  /-- (a) … and `u(0, 0) ≥ 0`. -/
  u_zero_zero_nonneg : 0 ≤ u 0 0
  /-- (b) for every `a ≥ 0`, `u(a, ·)` is strictly decreasing on `ℝ₊` … -/
  strictAntiOn_d : ∀ a : ℝ, 0 ≤ a → StrictAntiOn (fun d => u a d) (Ici 0)
  /-- (b) … and `max_{a ≥ 0} [u(a, d) − C(a)] < 0` for some `d ≥ 0`. -/
  exists_neg : ∃ d : ℝ, 0 ≤ d ∧ ∀ a : ℝ, 0 ≤ a → u a d - C a < 0
  /-- (c) for every `a ≥ 0`, `u₁(a, ·)` is strictly increasing on `ℝ₊`. -/
  strictMonoOn_u1 : ∀ a : ℝ, 0 ≤ a → StrictMonoOn (fun d => u1 u a d) (Ici 0)

/-- **Assumption 2** (p. 5), as printed. The limit `lim_{a→0} [u₁(a, 0) − C′(a)] > 0` is read as a
right limit that is either a positive real number or `+∞`. -/
structure Assumption2 (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) : Prop where
  /-- `C : ℝ₊ → ℝ₊`. -/
  nonneg : ∀ a : ℝ, 0 ≤ a → 0 ≤ C a
  strictMonoOn : StrictMonoOn C (Ici 0)
  convexOn : ConvexOn ℝ (Ici 0) C
  /-- `C` is twice differentiable on `ℝ₊`: first derivative … -/
  differentiableOn : DifferentiableOn ℝ C (Ici 0)
  /-- … and second derivative. -/
  differentiableOn_deriv : DifferentiableOn ℝ (Cderiv C) (Ici 0)
  /-- `lim_{a → 0⁺} [u₁(a, 0) − C′(a)] > 0` (the limit may be `+∞`). -/
  limit_pos :
    (∃ L : ℝ, 0 < L ∧ Tendsto (fun a => u1 u a 0 - Cderiv C a) (𝓝[>] 0) (𝓝 L)) ∨
      Tendsto (fun a => u1 u a 0 - Cderiv C a) (𝓝[>] 0) atTop

/-- The standing hypotheses of the mission: Assumptions 1 and 2 of the paper together with two
disclosed pins: `u(·, d)` is *strictly* concave on `ℝ₊` (needed by Lemma B.1 and Lemma B.2, which
applies Lemma B.1 to `u(·, d)`), and `C(0) = 0`. -/
structure Standing (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) : Prop where
  assumption1 : Assumption1 u C
  assumption2 : Assumption2 u C
  /-- Pin: strict concavity of `u(·, d)` on `ℝ₊` for every `d ≥ 0`. -/
  strictConcaveOn_a : ∀ d : ℝ, 0 ≤ d → StrictConcaveOn ℝ (Ici 0) (fun a => u a d)
  /-- Pin: `C(0) = 0`. -/
  C_zero : C 0 = 0

/-- A choice of the consumer: the set `J` of platforms she joins and an attention profile `a`
(only the entries `a k`, `k ∈ J`, matter). -/
abbrev Choice (K : ℕ) := Finset (Fin K) × (Fin K → ℝ)

/-- A strategy of the consumer: a choice at every addictiveness profile. -/
abbrev ConsumerStrategy (K : ℕ) := (Fin K → ℝ) → Choice K

/-- The consumer's payoff (1), p. 4: `0` if `J = ∅`, otherwise
`∑_{k ∈ J} u(a_k, d_k) − C(∑_{k ∈ J} a_k)`. -/
noncomputable def payoff {K : ℕ} (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (d : Fin K → ℝ) (x : Choice K) : ℝ :=
  if x.1 = ∅ then 0 else ∑ k ∈ x.1, u (x.2 k) (d k) - C (∑ k ∈ x.1, x.2 k)

/-- Feasibility in (2), p. 6: `a_k ≥ 0` for `k ∈ J` and `∑_{k ∈ J} a_k ≤ Ā`. -/
def Feasible {K : ℕ} (Abar : ℝ≥0∞) (x : Choice K) : Prop :=
  (∀ k ∈ x.1, 0 ≤ x.2 k) ∧ ENNReal.ofReal (∑ k ∈ x.1, x.2 k) ≤ Abar

/-- The choice `x` solves the consumer's problem (2) at the profile `d`. -/
def ConsumerOpt {K : ℕ} (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (Abar : ℝ≥0∞) (d : Fin K → ℝ)
    (x : Choice K) : Prop :=
  Feasible Abar x ∧ ∀ y : Choice K, Feasible Abar y → payoff u C d y ≤ payoff u C d x

/-- Platform `k`'s payoff (p. 6): the attention `a_k` if the consumer joins `k`, else `0`. -/
noncomputable def platformPayoff {K : ℕ} (k : Fin K) (x : Choice K) : ℝ :=
  if k ∈ x.1 then x.2 k else 0

/-- Pure-strategy subgame perfect equilibrium (p. 7) with platform profile `d` and consumer strategy
`σ`: every `d_k ≥ 0`; the consumer best-responds at **every** profile of nonnegative
addictiveness (on and off the path); and no platform has a profitable unilateral deviation to any
`x ≥ 0`. -/
def IsSPE {K : ℕ} (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (Abar : ℝ≥0∞) (d : Fin K → ℝ)
    (σ : ConsumerStrategy K) : Prop :=
  (∀ k, 0 ≤ d k) ∧
    (∀ d' : Fin K → ℝ, (∀ k, 0 ≤ d' k) → ConsumerOpt u C Abar d' (σ d')) ∧
    ∀ (k : Fin K) (x : ℝ), 0 ≤ x →
      platformPayoff k (σ (Function.update d k x)) ≤ platformPayoff k (σ d)

/-- The consumer's equilibrium payoff (consumer surplus): her payoff (1) at the choice `σ d`,
evaluated at the profile `d`. -/
noncomputable def consumerSurplus {K : ℕ} (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (d : Fin K → ℝ)
    (σ : ConsumerStrategy K) : ℝ :=
  payoff u C d (σ d)

/-- Monopoly equilibrium (`K = 1`, p. 7): an SPE in which the platform breaks ties in favour of the
consumer: every addictiveness `x ≥ 0` that gives the platform its equilibrium payoff gives the
consumer at most her equilibrium payoff. -/
def IsMonopolyEq (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (Abar : ℝ≥0∞) (d : Fin 1 → ℝ)
    (σ : ConsumerStrategy 1) : Prop :=
  IsSPE u C Abar d σ ∧
    ∀ x : ℝ, 0 ≤ x →
      platformPayoff 0 (σ (Function.update d 0 x)) = platformPayoff 0 (σ d) →
      consumerSurplus u C (Function.update d 0 x) σ ≤ consumerSurplus u C d σ

/-- Disclosed pin (p. 6): for every profile of nonnegative addictiveness and every nonempty set `J`
of joined platforms, the consumer's problem without attention cap (`Ā = ∞`) has an optimal
attention profile `(a_k)_{k ∈ J} ∈ ℝ₊^J`. -/
def UncOptExists (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (K : ℕ) : Prop :=
  ∀ d : Fin K → ℝ, (∀ k, 0 ≤ d k) → ∀ J : Finset (Fin K), J.Nonempty →
    ∃ a : Fin K → ℝ, (∀ k ∈ J, 0 ≤ a k) ∧
      ∀ a' : Fin K → ℝ, (∀ k ∈ J, 0 ≤ a' k) → payoff u C d (J, a') ≤ payoff u C d (J, a)

/-- `Aopt` is the consumer's unconstrained choice of attention on one platform,
`A(d) := argmax_{A ≥ 0} u(A, d) − C(A)` (p. 10), for every `d ≥ 0`. -/
def IsUncChoice (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (Aopt : ℝ → ℝ) : Prop :=
  ∀ d : ℝ, 0 ≤ d → 0 ≤ Aopt d ∧ IsMaxOn (fun A => u A d - C A) (Ici 0) (Aopt d)

/-- `d^A(Ā) := min {d ∈ [0, ∞] : A(d) ≥ Ā}` (p. 10), the lowest addictiveness under which the
consumer exhausts her attention, in `ℝ≥0∞`. When no finite `d ≥ 0` has `A(d) ≥ Ā` (e.g. `Ā = ∞`) the
infimum of the empty set is `∞`, which is the page's value `d = ∞`. -/
noncomputable def dA (Aopt : ℝ → ℝ) (Abar : ℝ≥0∞) : ℝ≥0∞ :=
  sInf {x : ℝ≥0∞ | ∃ d : ℝ, 0 ≤ d ∧ x = ENNReal.ofReal d ∧ Abar ≤ ENNReal.ofReal (Aopt d)}

/-- `dP` is `d^P(Ā)` (p. 10): `dP ≥ 0` and the consumer's best single-platform payoff under the cap,
`max_{A ∈ [0, Ā]} u(A, dP) − C(A)`, is attained and equals `0`. -/
def IsDP (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (Abar : ℝ≥0∞) (dP : ℝ) : Prop :=
  0 ≤ dP ∧
    (∃ A : ℝ, 0 ≤ A ∧ ENNReal.ofReal A ≤ Abar ∧ u A dP - C A = 0) ∧
    ∀ A : ℝ, 0 ≤ A → ENNReal.ofReal A ≤ Abar → u A dP - C A ≤ 0

/-- `Ā^M` (pp. 10, 12): the least cap from which on consumer surplus is zero in every monopoly
equilibrium, i.e. the infimum of the caps `Ā` such that for every `Ā' ≥ Ā` every monopoly equilibrium
at `Ā'` gives the consumer payoff `0` (`∞` if there is no such cap). -/
noncomputable def AbarM (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) : ℝ≥0∞ :=
  sInf {Abar : ℝ≥0∞ | ∀ Abar' : ℝ≥0∞, Abar ≤ Abar' →
    ∀ (d : Fin 1 → ℝ) (σ : ConsumerStrategy 1),
      IsMonopolyEq u C Abar' d σ → consumerSurplus u C d σ = 0}

/-- The objective `y · u(A / y, d) − C(A)` of (A.1) (p. 28); at `y = K` it is the objective
`K u(A/K, d) − C(A)` defining `A_K(d)` (p. 11). -/
noncomputable def perspObj (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (y d A : ℝ) : ℝ :=
  y * u (A / y) d - C A

/-- `A` maximizes `y · u(A / y, d) − C(A)` over `A ∈ [0, Ā]`: `A = A*(y)` of (A.1), and for
`y = K` the total attention `A_K(d)` of p. 11. -/
def IsPerspMax (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (Abar : ℝ≥0∞) (y d A : ℝ) : Prop :=
  0 ≤ A ∧ ENNReal.ofReal A ≤ Abar ∧
    ∀ A' : ℝ, 0 ≤ A' → ENNReal.ofReal A' ≤ Abar → perspObj u C y d A' ≤ perspObj u C y d A

/-- Equation (3) (p. 11) at `d`: with `A_K(d)` and `A_{K−1}(d)` the maximizers over `[0, Ā]`,
`K u(A_K(d)/K, d) − C(A_K(d)) = (K − 1) u(A_{K−1}(d)/(K − 1), d) − C(A_{K−1}(d))`. -/
def Eq3 (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (Abar : ℝ≥0∞) (K : ℕ) (d : ℝ) : Prop :=
  ∃ AK AK1 : ℝ, IsPerspMax u C Abar (K : ℝ) d AK ∧ IsPerspMax u C Abar ((K : ℝ) - 1) d AK1 ∧
    perspObj u C (K : ℝ) d AK = perspObj u C ((K : ℝ) - 1) d AK1

/-- The objective of (A.3) (p. 29): `x · u(A_x / x, d) + y · u(A_y / y, d′) − C(A_x + A_y)`. -/
noncomputable def objB3 (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (d' x y d Ax Ay : ℝ) : ℝ :=
  x * u (Ax / x) d + y * u (Ay / y) d' - C (Ax + Ay)

/-- `A = (A_x, A_y)` solves (A.3): `A_x, A_y ≥ 0`, `A_x + A_y ≤ Ā`, and it maximizes `objB3` over
all such pairs. -/
def IsB3Max (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (Abar : ℝ≥0∞) (d' x y d : ℝ) (A : ℝ × ℝ) : Prop :=
  0 ≤ A.1 ∧ 0 ≤ A.2 ∧ ENNReal.ofReal (A.1 + A.2) ≤ Abar ∧
    ∀ B : ℝ × ℝ, 0 ≤ B.1 → 0 ≤ B.2 → ENNReal.ofReal (B.1 + B.2) ≤ Abar →
      objB3 u C d' x y d B.1 B.2 ≤ objB3 u C d' x y d A.1 A.2

/-- The objective of (A.4) (p. 30), with platform "1" the index `0`:
`∑_{k ∈ S} u(a_k, d_k) + y · u(a_1, d_1) − C(∑_{k ∈ S ∪ {1}} a_k)`. -/
noncomputable def objB4 {K : ℕ} [NeZero K] (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (d : Fin K → ℝ) (y : ℝ)
    (S : Finset (Fin K)) (a : Fin K → ℝ) : ℝ :=
  ∑ k ∈ S, u (a k) (d k) + y * u (a 0) (d 0) - C (∑ k ∈ insert 0 S, a k)

/-- `a` solves (A.4): `a_k ≥ 0` and `∑ a_k ≤ Ā` over `k ∈ S ∪ {1}`, and it maximizes `objB4` over
all such profiles. -/
def IsB4Max {K : ℕ} [NeZero K] (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (Abar : ℝ≥0∞) (d : Fin K → ℝ)
    (y : ℝ) (S : Finset (Fin K)) (a : Fin K → ℝ) : Prop :=
  (∀ k ∈ insert 0 S, 0 ≤ a k) ∧ ENNReal.ofReal (∑ k ∈ insert 0 S, a k) ≤ Abar ∧
    ∀ a' : Fin K → ℝ, (∀ k ∈ insert 0 S, 0 ≤ a' k) →
      ENNReal.ofReal (∑ k ∈ insert 0 S, a' k) ≤ Abar → objB4 u C d y S a' ≤ objB4 u C d y S a

end AddictivePlatforms.Compete


