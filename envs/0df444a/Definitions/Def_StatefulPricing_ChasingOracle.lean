-- Prove2me | Definitions.Def_StatefulPricing_ChasingOracle
-- name    : StatefulPricing_ChasingOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T08:25:17.937599+00:00
-- url     : https://prove2.me/theorems/1548fcaa-a76e-407a-ac35-272d2613f3f1
-- title:
--   Ongoing chasing oracle, chasing regret and $\sigma$-chasability (Definition 3.2)
-- statement:
--   Let $M$ be a Dd-MDP instance. An **ongoing chasing oracle** is invoked at the beginning of some round $t_{\mathrm{init}}$ with a target policy $\gamma$ and an initial state $s_{\mathrm{init}}$, and is halted at the end of some round $t_{\mathrm{final}}\ge t_{\mathrm{init}}$. In each round $t_{\mathrm{init}}\le t\le t_{\mathrm{final}}$ it plays a random action $\hat x(t)$, from the state (Eq. (5))
--   $$
--   \hat s(t_{\mathrm{init}})=s_{\mathrm{init}},\qquad \hat s(t)=g_{t-1}\big(\hat s(t-1),\hat x(t-1)\big)\quad(t_{\mathrm{init}}<t\le t_{\mathrm{final}}).
--   $$
--   Its **chasing regret** is
--   $$
--   \mathrm{CR}=\sum_{t=t_{\mathrm{init}}}^{t_{\mathrm{final}}} f_t\big(s^\gamma(t),x^\gamma(t)\big)-\sum_{t=t_{\mathrm{init}}}^{t_{\mathrm{final}}}\mathbb E\big[f_t(\hat s(t),\hat x(t))\big],
--   $$
--   where $s^\gamma$ is the simulation of $\gamma$ from round $1$. The instance is **$\sigma$-chasable** for a set $\Gamma$ of policies (over horizon $T$) when, for every $\gamma\in\Gamma$, every $1\le t_{\mathrm{init}}\le t_{\mathrm{final}}\le T$ and every initial state $s_{\mathrm{init}}$ (which may differ from $s^\gamma(t_{\mathrm{init}})$), the oracle's actions are feasible for its states and $\mathrm{CR}\le\sigma$.
--
--   Chasability is the structural condition under which the paper's algorithm C&S has vanishing regret (Theorem 3.8), and the property the posted-pricing Dd-MDPs are shown to have (Theorem 3.6).
--
--   **Formalization Note** The oracle is a single online procedure fixed before the instance: its action at round $t$ is a function of its coins, $\gamma$, $t_{\mathrm{init}}$, $s_{\mathrm{init}}$, the feasible sets, $s_1$ and $g_s,f_s$ for $1\le s<t$. It sees the whole past from round $1$, as the oracle of Theorem 3.4 needs (it runs $\gamma$ "from round 1 to $t$", p.9); it does not know $t_{\mathrm{final}}$. Definition 3.2 says the oracle receives "the state transition function $f_t$ and reward function $g_t$": the letters are swapped by a typo, and $g_t$ is the transition here as everywhere else in the paper.
-- source:
--   Emek, Lavi, Niazadeh, Shi, Stateful Posted Pricing with Vanishing Regret via Dynamic Deterministic Markov Decision Processes, arXiv:2005.01869v2, Definition 3.2, p.8, Eq. (5)

import Mathlib
import Definitions.Def_StatefulPricing_DdMDP

set_option autoImplicit false

namespace StatefulPricing

open MeasureTheory

/-- **Ongoing chasing oracle** (Definition 3.2, arXiv:2005.01869v2, p.8): "The chasing oracle is
invoked at the beginning of some round tinit and provided with an initial state sinit ∈ S; this
invocation is halted at the end of some round tfinal ≥ tinit. In each round tinit ≤ t ≤ tfinal,
the chasing oracle generates a (random) action x̂(t) … following that, the chasing oracle is
provided with the Dd-MDP's state transition function … and reward function".

`act ω γ tinit sinit t M` is the action the oracle plays at round `t` of a run started at round
`tinit` from state `sinit` with target policy `γ`, on instance `M`, when its coins are `ω`.

**Formalization Note.** The oracle is one online procedure, fixed before the instance: by
`online`, its round-`t` action depends on `M` only through the feasible sets, the initial state
`s₁` and `g_s`, `f_s` for `1 ≤ s < t`. It sees the whole past from round `1`, not only rounds
`≥ tinit`: the oracle of Theorem 3.4 uses "λγt … obtained by running γ from round 1 to t" (p.9).
It does not know `tfinal`. (The page writes "state transition function ft(·, ·) and reward
function gt(·, ·)"; the letters are swapped by a typo, `g` is the transition everywhere else.) -/
structure ChasingOracle (Ω S X : Type*) where
  /-- The oracle's action at round `t`. -/
  act : Ω → (S → X) → ℕ → S → ℕ → DdMDP S X → X
  /-- The oracle is online. -/
  online : ∀ ω γ tinit sinit t (M M' : DdMDP S X), M.AgreeBefore M' t →
    act ω γ tinit sinit t M = act ω γ tinit sinit t M'

namespace ChasingOracle

variable {Ω S X : Type*}

/-- The oracle's state, Eq. (5) (arXiv:2005.01869v2, p.8): `runState … k` is `ŝ(tinit + k)`,
with `ŝ(tinit) = sinit` and `ŝ(t) = g_{t−1}(ŝ(t − 1), x̂(t − 1))` for `t > tinit`. -/
def runState (O : ChasingOracle Ω S X) (M : DdMDP S X) (ω : Ω) (γ : S → X) (tinit : ℕ)
    (sinit : S) : ℕ → S
  | 0 => sinit
  | k + 1 => M.g (tinit + k) (runState O M ω γ tinit sinit k)
      (O.act ω γ tinit sinit (tinit + k) M)

/-- The oracle's realized reward over the rounds `tinit, …, tfinal`:
`Σ_{t=tinit}^{tfinal} f_t(ŝ(t), x̂(t))`. -/
def runReward (O : ChasingOracle Ω S X) (M : DdMDP S X) (ω : Ω) (γ : S → X)
    (tinit tfinal : ℕ) (sinit : S) : ℝ :=
  ∑ t ∈ Finset.Icc tinit tfinal,
    M.f t (O.runState M ω γ tinit sinit (t - tinit)) (O.act ω γ tinit sinit t M)

/-- The chasing regret (Definition 3.2, arXiv:2005.01869v2, p.8):
`CR = Σ_{t=tinit}^{tfinal} f_t(s^γ(t), x^γ(t)) − Σ_{t=tinit}^{tfinal} E[f_t(ŝ(t), x̂(t))]`,
where `s^γ` is the simulation of `γ` from round `1` (Eq. (2)). -/
noncomputable def chasingRegret [MeasurableSpace Ω] (O : ChasingOracle Ω S X) (P : Measure Ω)
    (M : DdMDP S X) (γ : S → X) (tinit tfinal : ℕ) (sinit : S) : ℝ :=
  (∑ t ∈ Finset.Icc tinit tfinal, M.f t (M.simState γ t) (γ (M.simState γ t)))
    - ∫ ω, O.runReward M ω γ tinit tfinal sinit ∂P

/-- **σ-chasability** (Definition 3.2, arXiv:2005.01869v2, p.8): for every target policy
`γ ∈ Γ`, every `1 ≤ tinit ≤ tfinal ≤ T` and every initial state `sinit`, the oracle's actions are
feasible for its states `ŝ(t)` and its chasing regret is at most `σ`.

**Formalization Note.** "The initial state sinit provided to the chasing oracle may differ from
sγ(tinit)": `sinit` ranges over all of `S`. Feasibility is required for every coin outcome. -/
def IsChasable [MeasurableSpace Ω] (O : ChasingOracle Ω S X) (P : Measure Ω) (M : DdMDP S X)
    (T : ℕ) (σ : ℝ) (Γ : Set (S → X)) : Prop :=
  ∀ γ ∈ Γ, ∀ tinit tfinal : ℕ, 1 ≤ tinit → tinit ≤ tfinal → tfinal ≤ T → ∀ sinit : S,
    (∀ ω t, tinit ≤ t → t ≤ tfinal →
      O.act ω γ tinit sinit t M ∈ M.Xs (O.runState M ω γ tinit sinit (t - tinit))) ∧
    O.chasingRegret P M γ tinit tfinal sinit ≤ σ

end ChasingOracle

end StatefulPricing


