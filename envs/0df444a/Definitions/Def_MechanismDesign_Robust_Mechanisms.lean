-- Prove2me | Definitions.Def_MechanismDesign_Robust_Mechanisms
-- name    : MechanismDesign_Robust_Mechanisms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T04:48:54.971299+00:00
-- url     : https://prove2.me/theorems/e762d7b2-11b9-43fa-a59f-49e9f570fcb2
-- title:
--   Mechanisms, Bayesian and ex post Bayesian equilibria, reduced direct mechanisms, welfare functions and dominance
-- statement:
--   Fix a type space $\mathcal T = (T_i,\hat\theta_i,\hat\beta_i)_{i\in I}$, a set $X$ of outcomes and utility functions $u_i : X \times \Theta \to \mathbb R$ (interdependent, and not necessarily transferable).
--
--   A **mechanism** (Definition 10.8) is $(S_1,\dots,S_N,g)$ with nonempty strategy sets $S_i$ and $g : S_1\times\dots\times S_N \to \Delta(X)$. It is a **direct mechanism** (Definition 10.9) if $S_i = T_i$ and a **reduced direct mechanism** (Definition 10.10) if $S_i = \Theta_i$. A strategy profile is $\sigma = (\sigma_i)_i$ with $\sigma_i : T_i \to \Delta(S_i)$. When agents play mixed strategies $\mu_i \in \Delta(S_i)$, the resulting lottery over outcomes is
--
--   $$g(\mu_1,\dots,\mu_N)(x) = \sum_{s \in S} \prod_{i} \mu_i(s_i)\, g(s)(x),$$
--
--   and the equilibrium outcome at the type profile $\tau$ is $g(\sigma_1(\tau_1),\dots,\sigma_N(\tau_N))$.
--
--   The interim expected utility of type $\tau_i$ playing $m \in \Delta(S_i)$ while the others follow $\sigma$ is
--
--   $$U_i(\tau_i; m) = \sum_{\tau_{-i}} \hat\beta_i(\tau_i)(\tau_{-i}) \sum_{x} g\big(m, \sigma_{-i}(\tau_{-i})\big)(x)\, u_i\big(x, \hat\theta(\tau_i,\tau_{-i})\big).$$
--
--   $\sigma$ is a **Bayesian equilibrium** (Definition 10.11) if for every $i$ and $\tau_i$, $\sigma_i(\tau_i)$ maximizes $U_i(\tau_i;\cdot)$ over $\Delta(S_i)$. It is **belief-independent** (Definition 10.12) if $\hat\theta_i(\tau_i) = \hat\theta_i(\tau_i')$ implies $\sigma_i(\tau_i) = \sigma_i(\tau_i')$. A Bayesian equilibrium is an **ex post Bayesian equilibrium** (Definition 10.13) if for all $i$, $\tau_i$ and $\tau_{-i}$, $\sigma_i(\tau_i)$ also maximizes $\tau_i$'s expected utility when $\tau_i$ is certain that the others' types are $\tau_{-i}$. Truth telling is $\tilde\sigma_i(\tau_i) = \tau_i$ in a direct mechanism and $\tilde\sigma_i(\tau_i) = \hat\theta_i(\tau_i)$ in a reduced direct mechanism.
--
--   For every payoff type profile $\theta$, $F(\theta)$ is the set of outcomes produced with positive probability at some type profile $\tau$ with $\hat\theta(\tau) = \theta$ (p.188).
--
--   In the **quasi-linear** setting (§10.7.1), outcomes are $(a,t_1,\dots,t_N)$ with $a$ in a set $A$ of alternatives and $t_i$ the transfer paid by agent $i$, and $u_i((a,t),\theta) = v_i(a,\theta) - t_i$. A deterministic direct mechanism $(T,q,t)$ implements $q(\tau)$ and the transfers $t_i(\tau)$ at the report $\tau$; it is Bayesian incentive-compatible if truth telling is a Bayesian equilibrium. The interim expected payment of type $\tau_i$ is $\sum_{\tau_{-i}} \hat\beta_i(\tau_i)(\tau_{-i})\, t_i(\tau_i,\tau_{-i})$.
--
--   **Welfare functions** (Definitions 10.14–10.15) assign to every type profile $\tau$ a vector: ex post Pareto welfare $\big(\mathbb E\, u_i(g(\tau),\hat\theta(\tau))\big)_i$, interim Pareto welfare $\big(U_i(\tau_i;\sigma_i(\tau_i))\big)_i$, and revenue $\mathbb E \sum_i t_i(g(\tau))$, where $g(\tau)$ is the equilibrium lottery at $\tau$. A mechanism with an equilibrium **dominates** another (Definition 10.16) if its welfare is at least as large at every type profile and larger at some; on $\mathbb R^m$, "at least as large" is componentwise and "larger" means at least as large in every component and strictly larger in one.
--
--   These are the notions of §§10.5–10.9 on which the revelation principles, the belief revelation and betting results and the dominance results are stated.
--
--   **Formalization Note** Lotteries and mixed strategies are countably supported (`PMF`), so all expectations are sums. The book leaves integrability implicit; a Bayesian equilibrium here requires that the expected utility of every type under every mixed strategy exists (absolutely summable family), so that "maximizes" compares real numbers; the same is required of ex post expected utilities. Transfers $t_i$ are payments by agent $i$ (p.183). Direct quasi-linear mechanisms are deterministic, following the book's notation $(T,q,t)$.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, pp.177–180, Definitions 10.8–10.13; p.183, §10.7.1; p.188, §10.7.3; pp.191–192, Definitions 10.14–10.16

import Mathlib
import Definitions.Def_MechanismDesign_Robust_TypeSpaces

open scoped ENNReal

namespace MechanismDesign.Robust

universe u v w x

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Definition 10.8** (p.177). A mechanism `(S_1, …, S_N, g)`: nonempty strategy sets `S i` and
an outcome function `g : S_1 × ⋯ × S_N → Δ(X)` (lotteries over the outcome set `X`). -/
structure Mechanism (S : ι → Type w) (X : Type x) where
  /-- every strategy set is nonempty -/
  nonempty : ∀ i, Nonempty (S i)
  /-- the outcome function -/
  g : (∀ i, S i) → PMF X

variable {S : ι → Type w} {X : Type x}

/-- The probability `∏_i μ_i(s_i)` of a strategy profile when every agent `i` independently
randomizes according to `μ_i ∈ Δ(S_i)`. -/
noncomputable def profileProb (μ : ∀ i, PMF (S i)) (s : ∀ i, S i) : ℝ≥0∞ :=
  ∏ i, μ i (s i)

/-- The lottery over outcomes that results when every agent `i` plays the mixed strategy `μ_i`:
`x ↦ ∑_s ∏_i μ_i(s_i) · g(s)(x)` (the "slightly sloppy" `g(σ_1, …, σ_N)` of p.179). -/
noncomputable def outcomeProb (M : Mechanism S X) (μ : ∀ i, PMF (S i)) (x : X) : ℝ≥0∞ :=
  ∑' s, profileProb μ s * M.g s x

/-- The lottery over outcomes at the type profile `τ` when agents follow the strategy profile
`σ` (`σ_i : T_i → Δ(S_i)`). -/
noncomputable def eqOutcome {T : ι → Type v} (M : Mechanism S X) (σ : ∀ i, T i → PMF (S i))
    (τ : ∀ i, T i) (x : X) : ℝ≥0∞ :=
  outcomeProb M (fun i => σ i (τ i)) x

variable {Θ : ι → Type u} {T : ι → Type v}

/-- The terms of the interim expected utility of type `τ_i` of agent `i` when she plays the
mixed strategy `m ∈ Δ(S_i)` and the others follow `σ`: indexed by the others' types `τ_{-i}`, the
strategy profile `s` and the outcome `x`, the term is
`β̂_i(τ_i)(τ_{-i}) · m(s_i) ∏_{j ≠ i} σ_j(τ_j)(s_j) · g(s)(x) · u_i(x, θ̂(τ_i, τ_{-i}))`. -/
noncomputable def interimFamily (ts : TypeSpace Θ T) (u : ι → X → (∀ i, Θ i) → ℝ)
    (M : Mechanism S X) (σ : ∀ i, T i → PMF (S i)) (i : ι) (τi : T i) (m : PMF (S i)) :
    Others T i × (∀ j, S j) × X → ℝ :=
  fun p =>
    (ts.β i τi p.1 *
        profileProb (Function.update (fun j => σ j (join i τi p.1 j)) i m) p.2.1 *
        M.g p.2.1 p.2.2).toReal *
      u i p.2.2 (ts.payoff (join i τi p.1))

/-- The interim expected utility of type `τ_i` playing `m` against `σ_{-i}`, computed with her
belief `β̂_i(τ_i)`. -/
noncomputable def interimEU (ts : TypeSpace Θ T) (u : ι → X → (∀ i, Θ i) → ℝ)
    (M : Mechanism S X) (σ : ∀ i, T i → PMF (S i)) (i : ι) (τi : T i) (m : PMF (S i)) : ℝ :=
  ∑' p, interimFamily ts u M σ i τi m p

/-- **Definition 10.11** (p.178). `σ` is a Bayesian equilibrium: for every agent `i` and type
`τ_i`, `σ_i(τ_i)` maximizes `τ_i`'s expected utility under the belief `β̂_i(τ_i)` among all mixed
strategies. Expected utilities are required to exist (absolutely summable families) for every
mixed strategy, so that "maximizes expected utility" compares real numbers. -/
def IsBayesEq (ts : TypeSpace Θ T) (u : ι → X → (∀ i, Θ i) → ℝ) (M : Mechanism S X)
    (σ : ∀ i, T i → PMF (S i)) : Prop :=
  ∀ i (τi : T i) (m : PMF (S i)),
    Summable (interimFamily ts u M σ i τi m) ∧
      interimEU ts u M σ i τi m ≤ interimEU ts u M σ i τi (σ i τi)

/-- The terms of the expected utility of type `τ_i` playing `m` when she is certain that the
others' types are `τ_{-i}`. -/
noncomputable def expostFamily (ts : TypeSpace Θ T) (u : ι → X → (∀ i, Θ i) → ℝ)
    (M : Mechanism S X) (σ : ∀ i, T i → PMF (S i)) (i : ι) (τi : T i) (τo : Others T i)
    (m : PMF (S i)) : (∀ j, S j) × X → ℝ :=
  fun p =>
    (profileProb (Function.update (fun j => σ j (join i τi τo j)) i m) p.1 * M.g p.1 p.2).toReal *
      u i p.2 (ts.payoff (join i τi τo))

/-- The expected utility of type `τ_i` playing `m` when certain that the others are `τ_{-i}`. -/
noncomputable def expostEU (ts : TypeSpace Θ T) (u : ι → X → (∀ i, Θ i) → ℝ)
    (M : Mechanism S X) (σ : ∀ i, T i → PMF (S i)) (i : ι) (τi : T i) (τo : Others T i)
    (m : PMF (S i)) : ℝ :=
  ∑' p, expostFamily ts u M σ i τi τo m p

/-- **Definition 10.13** (p.180). A Bayesian equilibrium `σ` is an ex post Bayesian equilibrium
if for every `i`, `τ_i` and `τ_{-i}`, `σ_i(τ_i)` maximizes `τ_i`'s expected utility when her beliefs
attach probability one to the others' types being `τ_{-i}`. -/
def IsExPostBayesEq (ts : TypeSpace Θ T) (u : ι → X → (∀ i, Θ i) → ℝ) (M : Mechanism S X)
    (σ : ∀ i, T i → PMF (S i)) : Prop :=
  IsBayesEq ts u M σ ∧
    ∀ i (τi : T i) (τo : Others T i) (m : PMF (S i)),
      Summable (expostFamily ts u M σ i τi τo m) ∧
        expostEU ts u M σ i τi τo m ≤ expostEU ts u M σ i τi τo (σ i τi)

/-- **Definition 10.12** (p.179). The strategy profile is belief-independent: types with the same
payoff type choose the same (mixed) strategy. -/
def IsBeliefIndependent (ts : TypeSpace Θ T) (σ : ∀ i, T i → PMF (S i)) : Prop :=
  ∀ i (τi τi' : T i), ts.θhat i τi = ts.θhat i τi' → σ i τi = σ i τi'

/-- **Definition 10.9** (p.177). A direct mechanism: strategy sets `S_i = T_i`. -/
def directMechanism (ts : TypeSpace Θ T) (g : (∀ i, T i) → PMF X) : Mechanism T X :=
  ⟨ts.nonempty, g⟩

/-- Truth telling in a direct mechanism: `σ̃_i(τ_i) = τ_i`. -/
noncomputable def truthful (T : ι → Type v) : ∀ i, T i → PMF (T i) :=
  fun _ τi => PMF.pure τi

omit [Fintype ι] [DecidableEq ι] in
/-- The payoff type sets are nonempty, since the type sets are. -/
theorem TypeSpace.payoff_nonempty (ts : TypeSpace Θ T) : ∀ i, Nonempty (Θ i) :=
  fun i => (ts.nonempty i).map (ts.θhat i)

/-- **Definition 10.10** (p.178). A reduced direct mechanism: strategy sets `S_i = Θ_i`. -/
def reducedMechanism (ts : TypeSpace Θ T) (g : (∀ i, Θ i) → PMF X) : Mechanism Θ X :=
  ⟨ts.payoff_nonempty, g⟩

/-- Truth telling in a reduced direct mechanism: `σ̃_i(τ_i) = θ̂_i(τ_i)`. -/
noncomputable def truthfulReduced (ts : TypeSpace Θ T) : ∀ i, T i → PMF (Θ i) :=
  fun i τi => PMF.pure (ts.θhat i τi)

/-- `F(θ)` (p.188): the set of outcomes that the mechanism and the strategy profile produce (with
positive probability) at some type profile whose payoff type profile is `θ`. -/
def outcomeSet (ts : TypeSpace Θ T) (M : Mechanism S X) (σ : ∀ i, T i → PMF (S i))
    (θ : ∀ i, Θ i) : Set X :=
  {x | ∃ τ : ∀ i, T i, ts.payoff τ = θ ∧ eqOutcome M σ τ x ≠ 0}

/-! ### Quasi-linear environments (§10.7.1, p.183) -/

/-- Quasi-linear utility `u_i((a, t), θ) = v_i(a, θ) − t_i` on outcomes `(a, t_1, …, t_N)`, where
`t_i` is the transfer paid by agent `i`. -/
def qlUtility {A : Type*} (vu : ι → A → (∀ i, Θ i) → ℝ) : ι → A × (ι → ℝ) → (∀ i, Θ i) → ℝ :=
  fun i x θ => vu i x.1 θ - x.2 i

/-- The deterministic direct mechanism `(T, q, t)`: reported types `τ` lead to the alternative
`q(τ)` and the transfers `t_i(τ)` paid by the agents. -/
noncomputable def qlDirect {A : Type*} (ts : TypeSpace Θ T) (q : (∀ i, T i) → A)
    (t : ι → (∀ i, T i) → ℝ) : Mechanism T (A × (ι → ℝ)) :=
  ⟨ts.nonempty, fun τ => PMF.pure (q τ, fun i => t i τ)⟩

/-- The deterministic reduced direct mechanism: reported payoff types `θ` lead to `q(θ)` and the
transfers `t_i(θ)`. -/
noncomputable def qlReduced {A : Type*} (ts : TypeSpace Θ T) (q : (∀ i, Θ i) → A)
    (t : ι → (∀ i, Θ i) → ℝ) : Mechanism Θ (A × (ι → ℝ)) :=
  ⟨ts.payoff_nonempty, fun θ => PMF.pure (q θ, fun i => t i θ)⟩

/-- The interim expected payment `∑_{τ_{-i}} β̂_i(τ_i)(τ_{-i}) t_i(τ_i, τ_{-i})` of type `τ_i` in
a direct mechanism when everybody reports truthfully. -/
noncomputable def interimPayment (ts : TypeSpace Θ T) (t : ι → (∀ i, T i) → ℝ) (i : ι)
    (τi : T i) : ℝ :=
  ∑' τo, (ts.β i τi τo).toReal * t i (join i τi τo)

/-! ### Welfare functions and dominance (§10.9, Definitions 10.14–10.16, pp.191–192) -/

/-- **Definition 10.15 (1)**. Ex post Pareto welfare at `τ`: the vector of the agents' expected
utilities from the equilibrium lottery at `τ`, evaluated at the true payoff types `θ̂(τ)`. -/
noncomputable def expostWelfare (ts : TypeSpace Θ T) (u : ι → X → (∀ i, Θ i) → ℝ)
    (M : Mechanism S X) (σ : ∀ i, T i → PMF (S i)) (τ : ∀ i, T i) : ι → ℝ :=
  fun i => ∑' x, (eqOutcome M σ τ x).toReal * u i x (ts.payoff τ)

/-- **Definition 10.15 (2)**. Interim Pareto welfare at `τ`: the vector of the agents' interim
expected utilities `∫_{T_{-i}} u_i(g(τ)) dβ̂_i(τ_i)` in the equilibrium. -/
noncomputable def interimWelfare (ts : TypeSpace Θ T) (u : ι → X → (∀ i, Θ i) → ℝ)
    (M : Mechanism S X) (σ : ∀ i, T i → PMF (S i)) (τ : ∀ i, T i) : ι → ℝ :=
  fun i => interimEU ts u M σ i (τ i) (σ i (τ i))

/-- **Definition 10.15 (3)**. Revenue at `τ` in a quasi-linear environment: the expected sum of
the transfers `∑_i t_i` paid under the equilibrium lottery at `τ`. -/
noncomputable def revenueWelfare {A : Type*} (M : Mechanism S (A × (ι → ℝ)))
    (σ : ∀ i, T i → PMF (S i)) (τ : ∀ i, T i) : ℝ :=
  ∑' x, (eqOutcome M σ τ x).toReal * ∑ i, x.2 i

/-- **Definition 10.16** (p.192). Welfare `w` dominates welfare `w'` on the type profiles of the
type space: `w(τ) ≥ w'(τ)` for every `τ`, and `w(τ) > w'(τ)` for some `τ`, where on `ℝ^m`
`≥` is componentwise and `>` means `≥` componentwise with strict inequality in some component. -/
def Dominates {W : Type*} [Preorder W] (w w' : (∀ i, T i) → W) : Prop :=
  (∀ τ, w' τ ≤ w τ) ∧ ∃ τ, w' τ < w τ

end MechanismDesign.Robust


