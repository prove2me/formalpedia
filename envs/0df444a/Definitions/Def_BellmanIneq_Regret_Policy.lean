-- Prove2me | Definitions.Def_BellmanIneq_Regret_Policy
-- name    : BellmanIneq_Regret_Policy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T17:31:08.294978+00:00
-- url     : https://prove2.me/theorems/53fbb2c5-cb39-4c55-9e63-8d9a7e466b8e
-- title:
--   Adapted feasible policies, trajectories, disagreement, and regret
-- statement:
--   A state-feedback policy $\pi_t(s)$ selects an action from the current state and sample path. It is **non-anticipative** when $\pi_t(s)$ is measurable with respect to $\mathcal F_t$, and **augmented adapted** when it is measurable with respect to $\mathcal G_t$. Feasibility requires $\pi_t(s)\in\mathcal U(s,\xi^t)$ for every state and decision period.
--
--   Starting from $S^T=s_0$, the trajectory follows $S^{t-1}=\mathcal T(S^t,\xi^t,\pi_t(S^t))$. Write $\widehat U^t=\pi_t(S^t)$ for its action. The disagreement event $Q(t,S^t)$ occurs when $\widehat U^t$ is not satisfying under the specified relaxation and Bellman loss. The online value is the expected sum of rewards over $t=1,\ldots,T$; expected regret is Offline's Bellman value at $(T,s_0)$ minus that online value.
--
--   These constructions give Theorem 5 a concrete benchmark, policy, trajectory, and disagreement event.
--
--   **Formalization Note** Time runs backward: $t$ is time to go. The goal allows every feasible non-anticipative state-feedback policy, including RABBI; Proposition 1 uses an augmented-adapted policy. The same $L_B$ defines the Bellman inequalities and disagreement.
-- source:
--   Vera, Banerjee, Gurvich, Online Allocation and Pricing: Constant Regret via Bellman Inequalities, arXiv:1906.06361v2, p. 4, §2.1 and pp. 9, 12–13, §§3.1–3.2, Theorem 5

import Definitions.Def_BellmanIneq_Regret_BellmanInequalities

set_option autoImplicit false

namespace BellmanIneq.Regret

open MeasureTheory

/-- Vera, Banerjee, Gurvich, *Online Allocation and Pricing: Constant Regret via Bellman
Inequalities*, arXiv:1906.06361v2, pp. 4, 9, 12–13. A state-feedback policy. -/
abbrev Policy (Ω S U : Type*) := ℕ → S → Ω → U

/-- Vera, Banerjee, Gurvich, *Online Allocation and Pricing: Constant Regret via Bellman Inequalities*, arXiv:1906.06361v2, p. 9, §3.1.
An online policy observes only the canonical input filtration. -/
def NonAnticipative {Ω S Ξ U : Type*} [MeasurableSpace Ξ] [MeasurableSpace U]
    (ξ : ℕ → Ω → Ξ) (T : ℕ) (π : Policy Ω S U) : Prop :=
  ∀ t ∈ Finset.Icc 1 T, ∀ s, Measurable[observed ξ T t] (π t s)

/-- Vera, Banerjee, Gurvich, *Online Allocation and Pricing: Constant Regret via Bellman Inequalities*, arXiv:1906.06361v2, p. 12, Proposition 1.
The policy may use the benchmark's augmented information. -/
def AugmentedAdapted {Ω S Ξ U : Type*} [MeasurableSpace Ξ] [MeasurableSpace U]
    (ξ : ℕ → Ω → Ξ) (T : ℕ) (Gextra : MeasurableSpace Ω)
    (π : Policy Ω S U) : Prop :=
  ∀ t ∈ Finset.Icc 1 T, ∀ s, Measurable[augmented ξ T Gextra t] (π t s)

/-- Vera, Banerjee, Gurvich, *Online Allocation and Pricing: Constant Regret via Bellman Inequalities*, arXiv:1906.06361v2, p. 9, §3.1.
The policy chooses an available action in each decision period. -/
def Feasible {Ω S Ξ U : Type*} (P : Problem S Ξ U) (ξ : ℕ → Ω → Ξ)
    (T : ℕ) (π : Policy Ω S U) : Prop :=
  ∀ t ∈ Finset.Icc 1 T, ∀ s ω, π t s ω ∈ P.Feas s (ξ t ω)

/-- Vera, Banerjee, Gurvich, *Online Allocation and Pricing: Constant Regret via Bellman Inequalities*, arXiv:1906.06361v2, pp. 12–13, state
trajectory `S^t`, with `S^T = s₀` and `S^{t−1} = trans(S^t, ξ^t, U^t)`.
Formalization Note: recursion counts elapsed steps, then `traj` reverses the index. -/
def elapsedState {Ω S Ξ U : Type*} (P : Problem S Ξ U)
    (ξ : ℕ → Ω → Ξ) (T : ℕ) (π : Policy Ω S U) (s₀ : S) :
    ℕ → Ω → S :=
  Nat.rec (fun _ => s₀)
    (fun n prev ω =>
      let s := prev ω
      P.trans s (ξ (T - n) ω) (π (T - n) s ω))

/-- Vera, Banerjee, Gurvich, *Online Allocation and Pricing: Constant Regret via Bellman Inequalities*, arXiv:1906.06361v2, pp. 12–13,
the state at the start of period `t`. Used only for `0 ≤ t ≤ T`. -/
def traj {Ω S Ξ U : Type*} (P : Problem S Ξ U)
    (ξ : ℕ → Ω → Ξ) (T : ℕ) (π : Policy Ω S U) (s₀ : S)
    (t : ℕ) (ω : Ω) : S :=
  elapsedState P ξ T π s₀ (T - t) ω

/-- Vera, Banerjee, Gurvich, *Online Allocation and Pricing: Constant Regret via Bellman Inequalities*, arXiv:1906.06361v2, p. 13, the action `Û^t`
taken at the visited state. -/
def act {Ω S Ξ U : Type*} (P : Problem S Ξ U)
    (ξ : ℕ → Ω → Ξ) (T : ℕ) (π : Policy Ω S U) (s₀ : S)
    (t : ℕ) (ω : Ω) : U :=
  π t (traj P ξ T π s₀ t ω) ω

/-- Vera, Banerjee, Gurvich, *Online Allocation and Pricing: Constant Regret via Bellman Inequalities*, arXiv:1906.06361v2, p. 13, Theorem 5.
`Q(t,S^t)` is the event that the action actually taken is not satisfying.
Formalization Note: the same loss `LB` is used here and in Definition 2. -/
def disagreement {Ω S Ξ U : Type*} [mΩ : MeasurableSpace Ω] [mΞ : MeasurableSpace Ξ]
    (μ : Measure Ω) (P : Problem S Ξ U) (ξ : ℕ → Ω → Ξ) (T : ℕ)
    (Gextra : MeasurableSpace Ω) (ϕ LB : ℕ → S → Ω → ℝ)
    (π : Policy Ω S U) (s₀ : S) (t : ℕ) : Set Ω :=
  {ω | ¬ @Satisfying Ω S Ξ U mΩ mΞ μ P ξ T Gextra ϕ LB t
    (traj P ξ T π s₀ t ω) (act P ξ T π s₀ t ω) ω}

/-- Vera, Banerjee, Gurvich, *Online Allocation and Pricing: Constant Regret via Bellman Inequalities*, arXiv:1906.06361v2, p. 4, §2.1,
the online policy's expected total reward. -/
noncomputable def onlineValue {Ω S Ξ U : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (P : Problem S Ξ U) (ξ : ℕ → Ω → Ξ)
    (T : ℕ) (π : Policy Ω S U) (s₀ : S) : ℝ :=
  ∫ ω, ∑ t ∈ Finset.Icc 1 T,
    P.R (traj P ξ T π s₀ t ω) (ξ t ω) (act P ξ T π s₀ t ω) ∂μ

/-- Vera, Banerjee, Gurvich, *Online Allocation and Pricing: Constant Regret via Bellman Inequalities*, arXiv:1906.06361v2, pp. 4, 9,
expected regret against Offline's value (2). -/
noncomputable def regret {Ω S Ξ U : Type*} [mΩ : MeasurableSpace Ω] [mΞ : MeasurableSpace Ξ]
    (μ : Measure Ω) (P : Problem S Ξ U) (ξ : ℕ → Ω → Ξ) (T : ℕ)
    (Gextra : MeasurableSpace Ω) (π : Policy Ω S U) (s₀ : S) : ℝ :=
  ∫ ω, @offlineValue Ω S Ξ U mΩ mΞ μ P ξ T Gextra T s₀ ω ∂μ - @onlineValue Ω S Ξ U mΩ μ P ξ T π s₀

end BellmanIneq.Regret


