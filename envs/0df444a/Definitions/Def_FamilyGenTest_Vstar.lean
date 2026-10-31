-- Prove2me | Definitions.Def_FamilyGenTest_Vstar
-- name    : FamilyGenTest_Vstar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:12:48.498997+00:00
-- url     : https://prove2.me/theorems/df651517-3aeb-4ae3-be6c-c5bdc311af18
-- title:
--   Policies, the value of a policy and the optimal value $V^*$ of (3)
-- statement:
--   A **policy** is a deterministic stationary decision rule $\pi$ with $\pi(\mathbf s)\in\mathcal A_{\mathbf s}$ for every state. For a genotype $g$, the **return** $R^\pi(\mathbf s,g)$ from $\mathbf s$ is the terminal reward of $\mathbf s$ if $\pi$ stops there; if $\pi(\mathbf s)=i$ it is the reward of $i$ at result $g_i$, minus $c_i(\mathbf s)$, plus the return from $\mathbf s_{g_i}\cup\{i\}$. The value of $\pi$ and the optimal value of (3) are
--   $$
--   V^\pi(\mathbf s)=\sum_g\mu(g\mid\mathbf s)R^\pi(\mathbf s,g),\qquad V^*(\mathbf s)=\max_{\pi\in\Pi}V^\pi(\mathbf s).
--   $$
--   The action value of testing $i$ is
--   $$
--   Q^*_i(\mathbf s)=\sum_{\gamma\in\Gamma}\mathbb P(G_i=\gamma\mid\mathbf s)\bigl(r_i(\gamma)-c_i(\mathbf s)+V^*(\mathbf s_\gamma\cup\{i\})\bigr),
--   $$
--   with $r_i(\gamma)$ the reward of $i$ at result $\gamma$; the action value of stopping is the terminal reward. A policy is **optimal** if $V^\pi(\mathbf s)=V^*(\mathbf s)$ at every feasible $\mathbf s$, and **greedy** if at every feasible $\mathbf s$ its action maximizes the action value over $\mathcal A_{\mathbf s}$.
--
--   $V^*$ is defined as the maximum of (3); the optimality equations (4) are a theorem of the mission.
--
--   **Formalization Note** Policies form a finite nonempty type, so the maximum is attained. The return is a recursion with a fuel, started at the number $|\mathcal I\setminus\mathbf s|$ of untested individuals, which is exact because each test removes one of them. The paper's absorbing state $\Delta$ and action $C$ are not needed. All randomness is in $G$: given $G=g$ and $\pi$ the path is determined, so the average over $G$ is the expectation of (3). At an infeasible state $V^*=0$.
-- source:
--   Adelman & Wang, Optimal Genetic Testing of Families, SSRN 4624694 (Jan 24 2023), §2.4, (3), p.10; (4), p.11

import Mathlib
import Definitions.Def_FamilyGenTest_Rewards

namespace FamilyGenTest

/-- The deterministic stationary Markov decision rules `Π` (Adelman & Wang, Optimal Genetic Testing
of Families, SSRN 4624694 (Jan 24 2023), §2.4, p.10): a map with `π(s) ∈ 𝒜_s` for every state.

**Formalization Note** `Π` is finite and nonempty, so that the maximum in `Vstar` is a true
maximum. Rules are defined on all of `State I`, feasible or not, as their values on infeasible
states do not matter. -/
abbrev Policy (I : Type*) [Fintype I] [DecidableEq I] :=
  {a : State I → Option I // ∀ s, a s ∈ actionSet s}

variable {I : Type*} [Fintype I] [DecidableEq I]

instance : Nonempty (Policy I) :=
  ⟨⟨fun _ => none, fun _ => Finset.mem_insert_self _ _⟩⟩

/-- The return of the rule `π` from state `s` when the genotype is `g`, with `n` further tests
allowed: on stopping it is the terminal reward of `s`, and on testing `i` it is the reward of `i` at
`gᵢ`, minus `cᵢ(s)`, plus the return from `s` with `i ↦ gᵢ`. This is the random variable under the
expectation in (3) (Adelman & Wang, SSRN 4624694, p.10).

**Formalization Note** Recursion on a fuel `n`; at fuel `0` it returns the terminal reward. -/
noncomputable def returnFrom (R : Rewards I) (μ : Prior I) (π : Policy I) :
    ℕ → State I → (I → Fin 3) → ℝ
  | 0, s, _ => stopValue R μ s
  | n + 1, s, g =>
    match π.1 s with
    | none => stopValue R μ s
    | some i => testedReward R i (g i) - cost R μ s i + returnFrom R μ π n (test s i (g i)) g

/-- The value of the rule `π` in state `s`: the expectation in (3) (Adelman & Wang, SSRN 4624694,
p.10), namely the average under the posterior `μ(· | s)` of the return from `s`.

**Formalization Note** Given `G = g` and `π`, the sample path is determined, so the paper's
expectation over paths is this average over `G`; the transition probabilities (1) are the marginals
of the posterior (`eq_1_6_7_transition`). The fuel `|I \ s|` is exact: each test removes one
untested individual, and at fuel `0` nobody is left and `π` must stop. -/
noncomputable def value (R : Rewards I) (μ : Prior I) (π : Policy I) (s : State I) : ℝ :=
  ∑ g, posterior μ s g * returnFrom R μ π (untested s).card s g

/-- The optimal value `V*(s) = max_{π ∈ Π} E^π_s[…]` of (3) (Adelman & Wang, SSRN 4624694, p.10).

**Formalization Note** This is the maximum of (3), not a recursion; the optimality equations (4)
are the theorem `eq_4`. At an infeasible state every value is `0`, so `V* = 0`, the Lean value at
the paper's undefined states. -/
noncomputable def Vstar (R : Rewards I) (μ : Prior I) (s : State I) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun π : Policy I => value R μ π s

/-- The action value of testing `i` in `s`: `Eᵢ[rᵢ(ℙᵢ(S′)) − cᵢ(s) + V*(S′) | s]`, the inner term of
(4) (Adelman & Wang, SSRN 4624694, p.11), with `S′` distributed as (1), (6). -/
noncomputable def Qstar (R : Rewards I) (μ : Prior I) (s : State I) (i : I) : ℝ :=
  ∑ γ, marginal μ s i γ * (testedReward R i γ - cost R μ s i + Vstar R μ (test s i γ))

/-- The right-hand side of (4) for one action: `Qstar` for a test, `stopValue` for stopping
(Adelman & Wang, SSRN 4624694, p.11). -/
noncomputable def actionValue (R : Rewards I) (μ : Prior I) (s : State I) : Option I → ℝ
  | none => stopValue R μ s
  | some i => Qstar R μ s i

/-- `π` is optimal when it attains `V*` at every feasible state (Adelman & Wang, SSRN 4624694,
(3), p.10, "for every initial state"). -/
def IsOptimal (R : Rewards I) (μ : Prior I) (π : Policy I) : Prop :=
  ∀ s, Feasible μ s → value R μ π s = Vstar R μ s

/-- `π` picks, at every feasible state, an action solving the right-hand side of (4)
(Adelman & Wang, SSRN 4624694, p.11). -/
def IsGreedy (R : Rewards I) (μ : Prior I) (π : Policy I) : Prop :=
  ∀ s, Feasible μ s →
    ∀ a ∈ actionSet s, actionValue R μ s a ≤ actionValue R μ s (π.1 s)

end FamilyGenTest


