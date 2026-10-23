-- Prove2me | Definitions.Def_MFEUnique_Uniq_Game
-- name    : MFEUnique_Uniq_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:19:40.646175+00:00
-- url     : https://prove2.me/theorems/97b8472a-d75b-4c55-943b-a175fd8a7a02
-- title:
--   §2.1, Assumption 1, §2.3, pp. 5–10 — the anonymous stochastic game, strategies, the value function V and the optimal strategy correspondence G
-- statement:
--   This definition sets up the stochastic game model of Light and Weintraub (§2.1 and §2.3) from the point of view of a single player facing a fixed population state.
--
--   Let $X$ be the state space (a compact metric space in every theorem of the mission), let $A \subseteq \mathbb R^q$ be the action set, and let $\mathcal P(X)$ be the set of Borel probability measures on $X$ (the **population states**), carrying the weak topology. An **anonymous stochastic game** consists of
--
--   1. a feasible-action correspondence $\Gamma : X \to 2^A$;
--   2. a single-period payoff $\pi(x, a, s) \in \mathbb R$ for state $x$, action $a$ and population state $s$;
--   3. a transition function $w(x, a, s, \zeta) \in X$, so that the next state is $w(x, a, s, \zeta)$ when the idiosyncratic shock is $\zeta$;
--   4. shock values $\zeta_1, \dots, \zeta_J \in E$ taken with probabilities $p_1, \dots, p_J$, the shock being drawn independently in every period;
--   5. a discount factor $\beta$.
--
--   The **standing assumptions** are $p_j \ge 0$, $\sum_j p_j = 1$, $0 < \beta < 1$, and Assumption 1: $\pi$ is bounded and jointly continuous, $w$ is jointly continuous, $X$ is compact, and $\Gamma$ is compact-valued, upper hemicontinuous and lower hemicontinuous.
--
--   A **strategy** $\sigma = (\sigma_1, \sigma_2, \dots)$ is a sequence of Borel measurable maps $\sigma_t : X^t \to A$ with $\sigma_t(x_1, \dots, x_t) \in \Gamma(x_t)$. With the population state fixed at $s$ and initial state $x$, the expected discounted payoff of $\sigma$ is
--   $$V_\sigma(x, s) = \mathbb E_\sigma\Big[\sum_{t=1}^{\infty} \beta^{t-1} \pi(x(t), a(t), s)\Big],$$
--   the **value function** is $V(x, s) = \sup_\sigma V_\sigma(x, s)$, and the **optimal stationary strategy correspondence** is
--   $$G(x, s) = \operatorname*{argmax}_{a \in \Gamma(x)} \; \pi(x, a, s) + \beta \sum_{j=1}^{J} p_j\, V(w(x, a, s, \zeta_j), s).$$
--
--   These objects are the input to the definition of a mean field equilibrium and to every theorem of the mission.
--
--   **Formalization Note** The paper's number of shock values $n$ is renamed $J$ (the paper also uses $n$ for iterates). Time is 0-based in Lean: the period-$t$ payoff is weighted by $\beta^t$ and the strategy at period $t$ sees the $t+1$ states $x_0, \dots, x_t$; this is the paper's $\beta^{t-1}$ with $t \ge 1$. Because the shock is finitely valued and i.i.d. over time (as §2.1 and the Bellman equation of p. 10 presuppose), $\mathbb E_\sigma$ of the period-$t$ payoff is written as the finite sum over the shock indices $j_0, \dots, j_{t-1}$ weighted by $p_{j_0} \cdots p_{j_{t-1}}$, and $V_\sigma$ is a `tsum` (absolutely convergent since $\pi$ is bounded and $\beta < 1$). Actions live in the subtype of a set $A \subseteq \mathbb R^q$, so continuity of $\pi$ and $w$ is required only on $X \times A \times \mathcal P(X)$ (and $\times E$), as in the paper. Junk values: `sSup` of an empty or unbounded set of reals is $0$, so $V$ would be $0$ if no feasible measurable strategy existed; under the standing assumptions and nonempty $\Gamma$ the set is nonempty and bounded above by $\sup|\pi|/(1-\beta)$. Assumption 1(ii) ($X$ compact) is the instance `CompactSpace X` in each theorem.
-- source:
--   Light and Weintraub, Mean Field Equilibrium: Uniqueness, Existence, and Comparative Statics, arXiv:1903.02273v3, pp. 5–10, §2.1, Definition 1, Assumption 1 (pp. 7–8, footnotes 5–6), §2.3 (strategies, V_σ, V, Bellman equation, G)

import Mathlib

namespace MFEUnique.Uniq

open MeasureTheory

/-- The primitives of an anonymous stochastic game (Light–Weintraub, §2.1, pp. 5–6, Definition 1).
States lie in `X`; actions lie in the set `A ⊆ ℝ^q`; `Γ x ⊆ A` is the feasible action set;
`pay x a s` is the single-period payoff `π(x, a, s)`; `w x a s e` is the transition function
`w(x, a, s, ζ)`; the idiosyncratic shock takes the value `ζ j ∈ E` with probability `p j`
(`j : Fin J`; the paper's `n` is renamed `J`); `β` is the discount factor.
The population state `s` is a probability measure on `X`. -/
structure Game (X : Type*) [MeasurableSpace X] (q J : ℕ) (E : Type*)
    (A : Set (EuclideanSpace ℝ (Fin q))) where
  /-- feasible-action correspondence `Γ : X → 2^A` -/
  Γ : X → Set A
  /-- single-period payoff `π(x, a, s)` -/
  pay : X → A → ProbabilityMeasure X → ℝ
  /-- transition function `w(x, a, s, ζ)` -/
  w : X → A → ProbabilityMeasure X → E → X
  /-- shock values `ζ_1, …, ζ_J` -/
  ζ : Fin J → E
  /-- shock probabilities `p_1, …, p_J` -/
  p : Fin J → ℝ
  /-- discount factor -/
  β : ℝ

variable {X : Type*} [MeasurableSpace X] {q J : ℕ} {E : Type*}
  {A : Set (EuclideanSpace ℝ (Fin q))}

/-- The ranges of §2.1 (`p_j ≥ 0`, `∑ p_j = 1`, `0 < β < 1`, p. 6) and Assumption 1 (pp. 7–8):
(i) `π` is bounded and jointly continuous, `w` is jointly continuous (with `P(X)` carrying the
weak topology); (iii) `Γ` is compact-valued, upper and lower hemicontinuous.
Assumption 1(ii) (`X` compact) is the instance `[CompactSpace X]` in each theorem. -/
structure Game.Standing [TopologicalSpace X] [OpensMeasurableSpace X] [TopologicalSpace E]
    (G : Game X q J E A) : Prop where
  p_nonneg : ∀ j, 0 ≤ G.p j
  p_sum : ∑ j, G.p j = 1
  β_pos : 0 < G.β
  β_lt_one : G.β < 1
  pay_bdd : ∃ C : ℝ, ∀ x a s, |G.pay x a s| ≤ C
  pay_cont : Continuous fun z : X × A × ProbabilityMeasure X => G.pay z.1 z.2.1 z.2.2
  w_cont : Continuous fun z : X × A × ProbabilityMeasure X × E => G.w z.1 z.2.1 z.2.2.1 z.2.2.2
  Γ_compact : ∀ x, IsCompact (G.Γ x)
  Γ_uhc : UpperHemicontinuous G.Γ
  Γ_lhc : LowerHemicontinuous G.Γ

/-- A nonrandomized pure strategy (p. 9), indexed from `t = 0`: `σ t` maps the state history
`(x_0, …, x_t)` (the paper's `(x_1, …, x_{t+1})`) to an action. -/
abbrev Strategy (X : Type*) {q : ℕ} (A : Set (EuclideanSpace ℝ (Fin q))) :=
  (t : ℕ) → (Fin (t + 1) → X) → A

/-- `σ` is (Borel) measurable in every period and always feasible: `σ_t(x_1, …, x_t) ∈ Γ(x_t)`
(p. 9). -/
def Game.IsFeasible (G : Game X q J E A) (σ : Strategy X A) : Prop :=
  ∀ t, Measurable (σ t) ∧ ∀ h : Fin (t + 1) → X, σ t h ∈ G.Γ (h (Fin.last t))

/-- The state history `(x_0, …, x_t)` generated by strategy `σ` from the initial state `x` with
the population state fixed at `s`, when the shocks of periods `0, …, t-1` take the values
`ζ (j 0), …, ζ (j (t-1))`. -/
def Game.hist (G : Game X q J E A) (σ : Strategy X A) (x : X) (s : ProbabilityMeasure X) :
    (t : ℕ) → (Fin t → Fin J) → (Fin (t + 1) → X)
  | 0, _ => fun _ => x
  | t + 1, j =>
      let h := G.hist σ x s t (fun k => j k.castSucc)
      Fin.snoc (α := fun _ => X) h (G.w (h (Fin.last t)) (σ t h) s (G.ζ (j (Fin.last t))))

/-- The expected present discounted value `V_σ(x, s) = E_σ ∑_{t≥1} β^{t-1} π(x(t), a(t), s)`
(p. 9), written with 0-based time. The shocks are i.i.d. over time with law `(p_j)`, so the
expectation of the period-`t` payoff is the finite sum over the shock values of periods
`0, …, t-1`, weighted by the product of their probabilities. -/
noncomputable def Game.payoff (G : Game X q J E A) (σ : Strategy X A) (x : X)
    (s : ProbabilityMeasure X) : ℝ :=
  ∑' t : ℕ, G.β ^ t * ∑ j : Fin t → Fin J, (∏ k, G.p (j k)) *
    G.pay (G.hist σ x s t j (Fin.last t)) (σ t (G.hist σ x s t j)) s

/-- The value function `V(x, s) = sup_σ V_σ(x, s)` over feasible measurable strategies (p. 10). -/
noncomputable def Game.V (G : Game X q J E A) (x : X) (s : ProbabilityMeasure X) : ℝ :=
  sSup {v : ℝ | ∃ σ : Strategy X A, G.IsFeasible σ ∧ v = G.payoff σ x s}

/-- The right-hand side of the Bellman equation (p. 10):
`π(x, a, s) + β ∑_j p_j V(w(x, a, s, ζ_j), s)`. -/
noncomputable def Game.bellmanRHS (G : Game X q J E A) (x : X) (a : A)
    (s : ProbabilityMeasure X) : ℝ :=
  G.pay x a s + G.β * ∑ j, G.p j * G.V (G.w x a s (G.ζ j)) s

/-- The optimal stationary strategy correspondence
`G(x, s) = argmax_{a ∈ Γ(x)} π(x, a, s) + β ∑_j p_j V(w(x, a, s, ζ_j), s)` (p. 10). -/
def Game.Gopt (G : Game X q J E A) (x : X) (s : ProbabilityMeasure X) : Set A :=
  {a | a ∈ G.Γ x ∧ ∀ a' ∈ G.Γ x, G.bellmanRHS x a' s ≤ G.bellmanRHS x a s}

end MFEUnique.Uniq


