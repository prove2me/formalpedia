-- Prove2me | Definitions.Def_CorruptRobustRL_ElimLB_Setting
-- name    : CorruptRobustRL_ElimLB_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T20:50:23.808265+00:00
-- url     : https://prove2.me/theorems/e24b463d-4817-4183-8cd8-427a012ecedf
-- title:
--   §4.1 and §7, pp. 13, 31 — Q-supervisors, confidence-admissibility (Def 4.1), plausible sets, uniformly action-eliminating learners, run law, expected regret, uniform admissibility
-- statement:
--   Fix a horizon $H$ and an instance $\mathcal M$ on finite $\mathcal X,\mathcal A$.
--
--   A **Q-supervisor** $\mathcal T=(\bar Q,\underline Q,\mathscr A,\pi^{\mathrm{ucb}})$ consists of upper and lower estimates $\bar Q_h(x,a),\underline Q_h(x,a)\in[0,H]$, active sets $\mathscr A_h(x)\subseteq\mathcal A$, and a deterministic policy $\pi^{\mathrm{ucb}}_h(x)\in\arg\max_a\bar Q_h(x,a)$. It is **confidence-admissible** for $\mathcal M$ (Definition 4.1) if for all $h\in[H]$ and $x\in\mathcal X$
--
--   $$
--   \pi^\star_h(x)\subseteq\mathscr A_h(x)\quad\text{and}\quad \underline Q_h(x,a)\le Q^\star_h(x,a)\le\bar Q_h(x,a)\ \ \forall a\in\mathcal A .
--   $$
--
--   The **plausible set** is $\mathscr A^{\mathrm{plaus}}_h(x)=\{a\in\mathscr A_h(x):\bar Q_h(x,a)\ge\underline Q_h(x,a')\ \forall a'\in\mathscr A_h(x)\}$.
--
--   A **uniformly action-eliminating** algorithm produces a Q-supervisor $\mathcal T_k$ before each episode $k$ and, at each stage $h$ of the episode, selects $a_{k;h}$ independently and uniformly at random from $\mathscr A^{\mathrm{plaus}}_{k;h}(x_{k;h})$. In each episode the initial state is drawn from $p_0$, and given $(x,a)$ the reward is drawn from $\mathcal D_{\mathrm{rew}}(x,a)$ and the next state from $p(\cdot\mid x,a)$; the learner observes states, actions and rewards. The law of $\mathcal T_k$ may depend on all past Q-supervisors and observed episodes. The **regret** over $K$ episodes is
--
--   $$
--   \mathrm{Regret}^{\mathcal M}_K=\sum_{k=1}^K\bigl(V^\star-V^{\mathcal M,\pi_k}\bigr),
--   $$
--
--   where $\pi_k$ is the uniformly-at-random policy of episode $k$, and the expected regret $\mathbb E^{\mathcal M}[\mathrm{Regret}^{\mathcal M}_K]$ averages over the run. The event $\mathcal E^{\mathrm{adm}}_k$ says that $\mathcal T_k$ is confidence-admissible. An algorithm is **uniformly admissible** over $K$ episodes if, for every instance $\mathcal M$ on the environment, $\mathbb P^{\mathcal M}\bigl[\bigcap_{k=1}^K\mathcal E^{\mathrm{adm}}_k\bigr]\ge\tfrac12$. Finally, the Q-supervisor **eliminates no action** if at every stage and state $\mathscr A_h(x)=\mathcal A$ and $\bar Q_h(x,a)\ge\max_{a'\in\mathcal A}\underline Q_h(x,a')$ for all $a$.
--
--   **Formalization Note** Stages are 0-based. A learner is a kernel from the observed history (past supervisors and episodes, oldest first) to a discrete law (`PMF`) of the next supervisor; `runLaw` is the law of the history after $K$ episodes. If a plausible set is empty, the action is drawn uniformly from all of $\mathcal A$. `valueUnif` is $V^{\mathcal M,\pi}$ of the uniformly-at-random policy by backward recursion, and `expRegret` is the expectation of the regret under `runLaw` (a sum over the countable support). Uniform admissibility is stated for the joint event over all $K$ episodes, which is the form used in the paper's proof (p. 39); §7 (p. 31) words it as "with probability at least 1/2" for "the Q-supervisor $\mathscr T_k$".
-- source:
--   Lykouris, Simchowitz, Slivkins & Sun, Corruption-robust exploration in episodic reinforcement learning, arXiv:1911.08689v4, p. 13, §4.1 (Q-supervisor, Definition 4.1, plausible set); p. 31, §7 (uniformly action-eliminating, uniformly admissible); pp. 38–39, App. A (ℰ^no elim, ℰ^adm, Regret^M_K)

import Mathlib
import Definitions.Def_CorruptRobustRL_ElimLB_MDP

namespace CorruptRobustRL.ElimLB

open scoped ENNReal

/-- A Q-supervisor `𝒯 = (Q̄, Q̲, 𝒜, π^ucb)` (arXiv:1911.08689v4, §4.1, p. 13), indexed by the
0-based stage `h` (the paper's stage `h + 1`): upper and lower estimates `Q̄, Q̲ ∈ [0, H]`,
active sets `𝒜_h(x) ⊆ A`, and a deterministic UCB policy maximizing `Q̄`. The range and
argmax requirements are imposed at the stages `h < H` that the episode uses. -/
structure Supervisor (X A : Type) (H : ℕ) where
  Qbar : ℕ → X → A → ℝ
  Qlow : ℕ → X → A → ℝ
  act : ℕ → X → Finset A
  ucb : ℕ → X → A
  Qbar_mem : ∀ h < H, ∀ x a, 0 ≤ Qbar h x a ∧ Qbar h x a ≤ H
  Qlow_mem : ∀ h < H, ∀ x a, 0 ≤ Qlow h x a ∧ Qlow h x a ≤ H
  ucb_max : ∀ h < H, ∀ x a, Qbar h x a ≤ Qbar h x (ucb h x)

variable {X A : Type} [Fintype X] [Fintype A] [Nonempty A] {H : ℕ}

/-- Definition 4.1 (confidence-admissible), relative to the instance `inst`: at every stage
`h < H` and state `x`, the active set contains all optimal actions of `inst`, and
`Q̲_h(x,a) ≤ Q⋆_h(x,a) ≤ Q̄_h(x,a)` for every action `a`. -/
def IsAdmissible (inst : Instance X A) (T : Supervisor X A H) : Prop :=
  ∀ h < H, ∀ x : X, optActions inst H h x ⊆ ↑(T.act h x) ∧
    ∀ a : A, T.Qlow h x a ≤ Qstar inst H h x a ∧ Qstar inst H h x a ≤ T.Qbar h x a

/-- The plausible set `𝒜^plaus_h(x) = {a ∈ 𝒜_h(x) : Q̄_h(x,a) ≥ Q̲_h(x,a') ∀ a' ∈ 𝒜_h(x)}`
(p. 13). -/
noncomputable def plaus (T : Supervisor X A H) (h : ℕ) (x : X) : Finset A := by
  classical
  exact (T.act h x).filter (fun a => ∀ a' ∈ T.act h x, T.Qlow h x a' ≤ T.Qbar h x a)

/-- The action law of a uniformly action-eliminating algorithm at stage `h` and state `x`:
uniform on the plausible set; uniform on all of `A` if the plausible set is empty. -/
noncomputable def unifPlaus (T : Supervisor X A H) (h : ℕ) (x : X) : PMF A :=
  if hne : (plaus T h x).Nonempty then PMF.uniformOfFinset (plaus T h x) hne
  else PMF.uniformOfFintype A

/-- An observed episode: the list of (state, action, observed reward) at the stages
`0, …, H - 1`, in order. -/
abbrev Traj (X A : Type) := List (X × A × ℝ)

/-- Law of the observed stages `h, h+1, …, h+n-1` started from state `x`: at each stage the
action is drawn from `unifPlaus T`, then the reward from `R x a` and the next state from
`p x a`, independently given `(x, a)`. -/
noncomputable def stepsLaw (inst : Instance X A) (T : Supervisor X A H) :
    ℕ → ℕ → X → PMF (Traj X A)
  | 0, _, _ => PMF.pure []
  | n + 1, h, x =>
      (unifPlaus T h x).bind fun a =>
        (inst.R x a).bind fun r =>
          (inst.p x a).bind fun x' =>
            (stepsLaw inst T n (h + 1) x').map fun rest => (x, a, r) :: rest

/-- Law of one observed episode when the algorithm uses the Q-supervisor `T`:
`x₁ ∼ p₀`, followed by `H` stages of `stepsLaw`. -/
noncomputable def episodeLaw (inst : Instance X A) (T : Supervisor X A H) : PMF (Traj X A) :=
  inst.p0.bind fun x => stepsLaw inst T H 0 x

/-- A uniformly action-eliminating algorithm: a kernel from the observed history (all past
Q-supervisors and observed episodes, oldest first) to the law of the next Q-supervisor. -/
abbrev Learner (X A : Type) (H : ℕ) :=
  List (Supervisor X A H × Traj X A) → PMF (Supervisor X A H)

/-- Law of the history after `K` episodes (oldest episode first) when the learner `L` runs
on the stochastic instance `inst`: before episode `k` it draws `𝒯_k ∼ L(history)`, then the
episode is drawn from `episodeLaw inst 𝒯_k`. -/
noncomputable def runLaw (inst : Instance X A) (L : Learner X A H) :
    ℕ → PMF (List (Supervisor X A H × Traj X A))
  | 0 => PMF.pure []
  | K + 1 =>
      (runLaw inst L K).bind fun hist =>
        (L hist).bind fun T =>
          (episodeLaw inst T).map fun τ => hist ++ [(T, τ)]

/-- Value with `n` stages remaining, from the 0-based stage `h` and state `x`, of the
policy that plays `unifPlaus T` at every stage. -/
noncomputable def Vunif (inst : Instance X A) (T : Supervisor X A H) : ℕ → ℕ → X → ℝ
  | 0, _, _ => 0
  | n + 1, h, x => ∑ a, (unifPlaus T h x a).toReal *
      (inst.rbar x a + ∑ x', (inst.p x a x').toReal * Vunif inst T n (h + 1) x')

/-- `V^{ℳ, π}` for the policy `π` that plays uniformly on the plausible sets of `T`. -/
noncomputable def valueUnif (inst : Instance X A) (T : Supervisor X A H) : ℝ :=
  ∑ x, (inst.p0 x).toReal * Vunif inst T H 0 x

/-- `Regret^ℳ_K = Σ_k (V⋆ − V^{ℳ, π_k})` of a run, `π_k` being the policy of episode `k`. -/
noncomputable def regret (inst : Instance X A)
    (run : List (Supervisor X A H × Traj X A)) : ℝ :=
  (run.map fun e => Vstar inst H - valueUnif inst e.1).sum

/-- Expected regret after `K` episodes, `E^ℳ[Regret^ℳ_K]`. -/
noncomputable def expRegret (inst : Instance X A) (L : Learner X A H) (K : ℕ) : ℝ :=
  ∑' run, (runLaw inst L K run).toReal * regret inst run

/-- `ℰ^adm_k` for the instance `inst`: the Q-supervisor of episode `k` (0-based) is
confidence-admissible with respect to `inst`. -/
def admEvent (inst : Instance X A) (k : ℕ)
    (run : List (Supervisor X A H × Traj X A)) : Prop :=
  ∃ e, run[k]? = some e ∧ IsAdmissible inst e.1

/-- Uniform admissibility for the environment `(X, A, H)` over `K` episodes: for every problem
instance on the environment, all `K` Q-supervisors are confidence-admissible simultaneously
with probability at least `1/2`. -/
def UniformlyAdmissible (L : Learner X A H) (K : ℕ) : Prop :=
  ∀ inst : Instance X A,
    (1 / 2 : ℝ≥0∞) ≤ (runLaw inst L K).toOuterMeasure {run | ∀ k < K, admEvent inst k run}

/-- The no-elimination condition of `ℰ^{no elim}`: at every stage `h < H` and state `x`, the
active set is all of `A` and `Q̄_h(x,a) ≥ max_{a'} Q̲_h(x,a')` for every `a`. -/
def NoElim (T : Supervisor X A H) : Prop :=
  ∀ h < H, ∀ x : X, T.act h x = Finset.univ ∧
    ∀ a : A, Finset.univ.sup' Finset.univ_nonempty (T.Qlow h x) ≤ T.Qbar h x a

end CorruptRobustRL.ElimLB


