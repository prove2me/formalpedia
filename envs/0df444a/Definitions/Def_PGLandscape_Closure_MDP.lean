-- Prove2me | Definitions.Def_PGLandscape_Closure_MDP
-- name    : PGLandscape_Closure_MDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T05:26:37.752105+00:00
-- url     : https://prove2.me/theorems/919b11a9-cbc4-454a-8d62-4206b39061cb
-- title:
--   §2, pp. 5–8 — the MDP (S, (A_s), g, P, γ, ρ), measurable policies, J_π, η_π (2), ℓ (1), T_π (3), T (4), Q_π (6), B (11), optimal policies, Assumptions 1–2
-- statement:
--   This definition file sets up the discounted-cost Markov decision process of Bhandari and Russo, *Global Optimality Guarantees for Policy Gradient Methods*, §2.
--
--   **The model.** A Markov decision process is a tuple $(\mathcal S, (\mathcal A_s)_{s\in\mathcal S}, g, P, \gamma, \rho)$ where $\mathcal S$ and $\mathcal A$ are measurable spaces, $\mathcal A_s \subseteq \mathcal A$ is a nonempty set of feasible actions in state $s$ whose graph $\mathcal K = \{(s,a) : a\in\mathcal A_s\}$ is measurable, $g$ is a bounded measurable cost, $P(\cdot\mid s,a)$ is a stochastic kernel, $\gamma\in(0,1)$ is the discount factor and $\rho$ is an initial probability distribution.
--
--   **Policies.** A stationary policy is a measurable map $\pi:\mathcal S\to\mathcal A$; it is feasible, $\pi\in\Pi$, if $\pi(s)\in\mathcal A_s$ for every $s$.
--
--   **Derived objects.** For a policy $\pi$, with $P^\pi_s(s_t\in\cdot)$ the $t$-step law of the chain driven by $\pi$ from $s$:
--   1. the cost-to-go $J_\pi(s) = \sum_{t\ge0}\gamma^t \int g(s',\pi(s'))\,P^\pi_s(s_t\in ds')$;
--   2. the discounted state-occupancy measure (2): $\eta_\pi = (1-\gamma)\sum_{t\ge0}\gamma^t P^\pi_\rho(s_t\in\cdot)$;
--   3. the discounted average cost (1): $\ell(\pi) = (1-\gamma)\int J_\pi\,d\rho$;
--   4. the Bellman operators (3), (4):
--   $$(T_\pi J)(s) = g(s,\pi(s)) + \gamma\int J(s')P(ds'\mid s,\pi(s)),\qquad (TJ)(s) = \inf_{a\in\mathcal A_s}\Big[g(s,a)+\gamma\int J(s')P(ds'\mid s,a)\Big];$$
--   5. the Q-function (6) $Q_\pi(s,a) = g(s,a)+\gamma\int J_\pi\,dP(\cdot\mid s,a)$ and the weighted policy-iteration objective (11) $\mathcal B(\bar\pi\mid\eta,J) = \int (T_{\bar\pi}J)\,d\eta$.
--
--   A feasible policy $\pi^*$ is optimal if $J_{\pi^*}(s)\le J_\pi(s)$ for every $\pi\in\Pi$ and every $s$, so that $J_{\pi^*} = J^*$. **Assumption 1** asks that $\eta_{\pi^*}\ll\rho$. **Assumption 2** (measurable selection) asks that for every bounded measurable $J$ some $\pi\in\Pi$ attains the infimum in $(TJ)(s)$ at every state.
--
--   These objects are the vocabulary of every statement of the mission.
--
--   **Formalization Note** $\mathcal S,\mathcal A$ are arbitrary measurable spaces (the paper takes Borel subsets of Euclidean spaces; no argument uses that structure). The cost and kernel are given and $g$ is bounded on all of $\mathcal S\times\mathcal A$, not only on $\mathcal K$; only their values on $\mathcal K$ enter $\Pi$, $T$ and $J^*$, but the parameterized policies of Condition 0 are evaluated slightly outside the parameter set, where they need not be feasible. The page prints (3) and (4) without $\gamma$; (6), (7), Assumption 2 and every proof use $\gamma$, and the definition includes it. $T$ is an infimum, equal to the page's minimum on bounded $J$ under Assumption 2. $J^*$ is never defined as an infimum: an optimal policy $\pi^*$ is a binder, and $J^* = J_{\pi^*}$.
-- source:
--   arXiv:1906.01786v3, §2, pp. 5–8, (1)–(7), Assumptions 1–2; (11), p. 11

import Mathlib

namespace PGLandscape.Closure

open MeasureTheory ProbabilityTheory

/-- The Markov decision process `(S, (A_s)_{s∈S}, g, P, γ, ρ)` of §2 (pp. 5–8) of Bhandari and Russo,
arXiv:1906.01786v3: feasible action sets `A_s ⊆ A` whose graph `K` is measurable, a measurable cost `g`
bounded on `S × A`, a stochastic kernel `P(· | s, a)`, a discount factor `γ ∈ (0, 1)` and an initial
probability distribution `ρ`. Cost and kernel are given on all of `S × A`; only their values on `K`
enter `Π`, `T` and `J*`. -/
structure MDP (S A : Type*) [MeasurableSpace S] [MeasurableSpace A] where
  /-- the feasible action set `A_s` -/
  As : S → Set A
  As_nonempty : ∀ s, (As s).Nonempty
  /-- `K = {(s, a) : s ∈ S, a ∈ A_s}` is measurable (Assumption 2) -/
  K_measurable : MeasurableSet {p : S × A | p.2 ∈ As p.1}
  /-- the instantaneous expected cost `g(s, a)` -/
  g : S × A → ℝ
  g_measurable : Measurable g
  /-- per-period costs are uniformly bounded -/
  g_bounded : ∃ C : ℝ, ∀ p, |g p| ≤ C
  /-- the transition kernel `P(· | s, a)` -/
  P : Kernel (S × A) S
  P_markov : IsMarkovKernel P
  /-- the discount factor `γ ∈ (0, 1)` -/
  γ : ℝ
  γ_pos : 0 < γ
  γ_lt_one : γ < 1
  /-- the initial distribution `ρ` -/
  ρ : Measure S
  ρ_prob : IsProbabilityMeasure ρ

attribute [instance] MDP.P_markov MDP.ρ_prob

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

/-- A measurable stationary decision rule `π : S → A` (p. 5). -/
def MPolicy (S A : Type*) [MeasurableSpace S] [MeasurableSpace A] : Type _ :=
  {π : S → A // Measurable π}

/-- `π ∈ Π`: the measurable stationary policy `π` is feasible, `π(s) ∈ A_s` for every `s` (p. 5). -/
def IsFeasible (M : MDP S A) (π : MPolicy S A) : Prop :=
  ∀ s, π.1 s ∈ M.As s

/-- The one-step state kernel `P(· | s, π(s))` of the chain driven by `π`. -/
noncomputable def stepKernel (M : MDP S A) (π : MPolicy S A) : Kernel S S :=
  M.P.comap (fun s => (s, π.1 s)) (measurable_id.prodMk π.2)

/-- The `t`-step kernel `s ↦ P^π_s(s_t ∈ ·)`. -/
noncomputable def iterKernel (M : MDP S A) (π : MPolicy S A) : ℕ → Kernel S S
  | 0 => Kernel.id
  | t + 1 => stepKernel M π ∘ₖ iterKernel M π t

/-- The cost-to-go `J_π(s) = E^π_s[∑_{t≥0} γ^t g_π(s_t)]` (p. 6). -/
noncomputable def costToGo (M : MDP S A) (π : MPolicy S A) (s : S) : ℝ :=
  ∑' t : ℕ, M.γ ^ t * ∫ s', M.g (s', π.1 s') ∂(iterKernel M π t s)

/-- The discounted state-occupancy measure `η_π(·) = (1−γ) ∑_{t≥0} γ^t P^π_ρ(s_t ∈ ·)`, (2) p. 6. -/
noncomputable def occupancy (M : MDP S A) (π : MPolicy S A) : Measure S :=
  Measure.sum (fun t : ℕ => ENNReal.ofReal ((1 - M.γ) * M.γ ^ t) • M.ρ.bind (iterKernel M π t))

/-- The discounted average cost `ℓ(π) = (1−γ) ∫ J_π dρ`, (1) p. 6. -/
noncomputable def loss (M : MDP S A) (π : MPolicy S A) : ℝ :=
  (1 - M.γ) * ∫ s, costToGo M π s ∂M.ρ

/-- The Bellman operator `(T_π J)(s) = g(s, π(s)) + γ ∫ J(s') P(ds' | s, π(s))`, (3) p. 7, with the
factor `γ` of (6), (7) and Assumption 2. -/
noncomputable def bellmanPi (M : MDP S A) (π : S → A) (J : S → ℝ) (s : S) : ℝ :=
  M.g (s, π s) + M.γ * ∫ s', J s' ∂(M.P (s, π s))

/-- The Bellman optimality operator `(TJ)(s) = min_{a ∈ A_s} [g(s, a) + γ ∫ J(s') P(ds' | s, a)]`,
(4) p. 7, with the factor `γ`. The minimum is an infimum over the nonempty set `A_s`; it is the
page's value whenever `J` is bounded (then the family is bounded below). -/
noncomputable def bellmanOpt (M : MDP S A) (J : S → ℝ) (s : S) : ℝ :=
  ⨅ a : M.As s, M.g (s, a.1) + M.γ * ∫ s', J s' ∂(M.P (s, a.1))

/-- The state-action cost-to-go `Q_π(s, a) = g(s, a) + γ ∫ J_π(s') P(ds' | s, a)`, (6) p. 7. -/
noncomputable def qFun (M : MDP S A) (π : MPolicy S A) (s : S) (a : A) : ℝ :=
  M.g (s, a) + M.γ * ∫ s', costToGo M π s' ∂(M.P (s, a))

/-- The weighted policy iteration ("Bellman") objective `B(π̄ | η, J) = ∫ (T_π̄ J)(s) η(ds)`,
(11) p. 11 and §5.1 p. 12. -/
noncomputable def bellmanObj (M : MDP S A) (πbar : S → A) (η : Measure S) (J : S → ℝ) : ℝ :=
  ∫ s, bellmanPi M πbar J s ∂η

/-- `π*` is an optimal policy: `π* ∈ Π` and `J_{π*}(s) ≤ J_π(s)` for every `π ∈ Π` and every `s`,
i.e. `J_{π*} = J* = inf_{π∈Π} J_π` (p. 6). -/
def IsOptimal (M : MDP S A) (πstar : MPolicy S A) : Prop :=
  IsFeasible M πstar ∧
    ∀ π : MPolicy S A, IsFeasible M π → ∀ s, costToGo M πstar s ≤ costToGo M π s

/-- Assumption 1 (p. 7): `η_{π*}` is absolutely continuous with respect to `ρ`. -/
def Assumption1 (M : MDP S A) (πstar : MPolicy S A) : Prop :=
  occupancy M πstar ≪ M.ρ

/-- Assumption 2 (pp. 7–8), measurable selection: for each bounded measurable `J` there is `π ∈ Π`
attaining the minimum of `g(s, a) + γ ∫ J dP(· | s, a)` over `a ∈ A_s` at every state `s`. -/
def Assumption2 (M : MDP S A) : Prop :=
  ∀ J : S → ℝ, Measurable J → (∃ C : ℝ, ∀ s, |J s| ≤ C) →
    ∃ π : MPolicy S A, IsFeasible M π ∧
      ∀ s, ∀ a ∈ M.As s, bellmanPi M π.1 J s ≤ M.g (s, a) + M.γ * ∫ s', J s' ∂(M.P (s, a))

end PGLandscape.Closure


