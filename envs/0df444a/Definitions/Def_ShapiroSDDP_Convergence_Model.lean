-- Prove2me | Definitions.Def_ShapiroSDDP_Convergence_Model
-- name    : ShapiroSDDP_Convergence_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T09:33:32.934986+00:00
-- url     : https://prove2.me/theorems/1a7f79b7-fbbb-407f-a33f-83acaadbf99b
-- title:
--   The SAA multistage linear program of §3: sample (3.4), cost-to-go (3.5)–(3.6), optimal value (3.7), policies, expected cost (3.15), optimality, (3.18)
-- statement:
--   This file sets up the sample average approximation (SAA) of a multistage linear stochastic program, as in Shapiro, §1 (1.1) and §3, pp. 6–8.
--
--   There are $T\ge 2$ stages, numbered $1,\dots,T$. The stage-$t$ decision is $x_t\in\mathbb R^{n_t}$, $x_t\ge 0$. The first stage has deterministic data $(c_1,A_1,b_1)$ and constraint $A_1x_1=b_1$. For $t=2,\dots,T$ the true data $\xi_t=(c_t,A_t,B_t,b_t)$ are replaced by a sample (3.4)
--   $$\tilde\xi_t^j=(\tilde c_{tj},\tilde A_{tj},\tilde B_{tj},\tilde b_{tj}),\qquad j=1,\dots,N_t,\quad N_t\ge 1,$$
--   each outcome having probability $1/N_t$, independently across stages. All four components are random. The stage-$t$ constraint after decision $x_{t-1}$ and outcome $j$ is $\tilde B_{tj}x_{t-1}+\tilde A_{tj}x_t=\tilde b_{tj}$, $x_t\ge 0$.
--
--   The SAA **cost-to-go** functions are defined backwards from $\widetilde{\mathcal Q}_{T+1}\equiv 0$ by (3.5)–(3.6):
--   $$\widetilde Q_{tj}(x_{t-1})=\inf_{x_t}\big\{\tilde c_{tj}^\top x_t+\widetilde{\mathcal Q}_{t+1}(x_t):\ \tilde B_{tj}x_{t-1}+\tilde A_{tj}x_t=\tilde b_{tj},\ x_t\ge 0\big\},\qquad \widetilde{\mathcal Q}_{t}(x_{t-1})=\frac1{N_{t}}\sum_{j=1}^{N_{t}}\widetilde Q_{tj}(x_{t-1}),$$
--   and the optimal value of the SAA problem is that of the first-stage problem (3.7), $\min\{c_1^\top x_1+\widetilde{\mathcal Q}_2(x_1): A_1x_1=b_1,\ x_1\ge 0\}$.
--
--   A stage-$t$ decision is **reachable** if it is feasible at stage 1 ($t=1$), or feasible at stage $t$ for some reachable $x_{t-1}$ and some outcome. The paper's standing assumption (p. 6), "the cost-to-go functions are finite valued, in particular we assume the relatively complete recourse", is the predicate **FiniteValued**: for every $1\le t\le T-1$, every reachable $x_t$ and every outcome $j$ of stage $t+1$, the problem defining $\widetilde Q_{t+1,j}(x_t)$ is feasible and its objective is bounded below on its feasible set.
--
--   A **scenario** is a choice $(j_2,\dots,j_T)$ of one outcome per stage; there are $N=\prod_{t=2}^TN_t$ scenarios, each of probability $1/N$ (the SAA tree, p. 6). A **policy** assigns to each stage $t$ and scenario a decision $\bar x_t$; it is **implementable** if $\bar x_t$ depends only on the outcomes of stages $2,\dots,t$, i.e. $\bar x_t=\bar x_t(\tilde\xi_{[t]})$, and **feasible** if it satisfies the constraints of every stage on every scenario. Its **expected cost** (3.15) on the SAA tree is
--   $$\frac1N\sum_{\text{scenarios}}\ \sum_{t=1}^T\tilde c_t^\top\bar x_t .$$
--   A policy is **optimal for the SAA problem** if it is feasible and implementable and its expected cost is at most that of every feasible implementable policy. Finally, the file records the dynamic programming optimality conditions (3.18) on every scenario:
--   $$\bar x_t(\tilde\xi_{[t]})\in\arg\min_{x_t}\big\{\tilde c_t^\top x_t+\widetilde{\mathcal Q}_{t+1}(x_t):\ \tilde B_t\bar x_{t-1}(\tilde\xi_{[t-1]})+\tilde A_tx_t=\tilde b_t,\ x_t\ge 0\big\},\qquad t=1,\dots,T,$$
--   where at stage 1 the constraint is $A_1x_1=b_1$ (the paper's convention $\tilde B_0=0$) and $\widetilde{\mathcal Q}_{T+1}\equiv0$.
--
--   These are the objects against which the SDDP approximations of the mission are measured. Optimality is defined by expected cost, so that its equivalence with (3.18) is a theorem of the mission.
--
--   **Formalization Note** Matrices are indexed by the stage of the decision they follow: for $1\le t\le T-1$, `c t j`, `A t j`, `B t j`, `b t j` are $\tilde c_{t+1,j},\tilde A_{t+1,j},\tilde B_{t+1,j},\tilde b_{t+1,j}$, and `B t j` multiplies $x_t$. `V t x` is $\widetilde{\mathcal Q}_{t+1}(x_t)$ (so `V t ≡ 0` for $t\ge T$), `Qo t x j` is $\widetilde Q_{t+1,j}(x_t)$ and `optVal` is the optimal value (3.7). They are real infima (`sInf`), which Lean sets to $0$ on empty or unbounded-below sets; they are genuine only on reachable states under `FiniteValued`, and no statement of the mission evaluates them elsewhere. The paper assumes finite values for all $x_{t-1}$; requiring them only on reachable states is a weaker hypothesis. A scenario is a function `Scen` on `Fin (T-1)` whose coordinate $u$ is the outcome of stage $u+2$; a policy is a function of the stage and the whole scenario, with implementability as a separate condition.
-- source:
--   Shapiro, Analysis of Stochastic Dual Dynamic Programming Method, Optimization Online 2009/12/2509, pp. 1, 6–8, 10–11, (1.1), (3.4)–(3.7), (3.15), (3.18)

import Mathlib

open Matrix

namespace ShapiroSDDP.Convergence

/-- The sample average approximation (SAA) of a multistage linear stochastic program (Shapiro,
§1 (1.1) and §3 (3.4)–(3.7)). Stages are numbered `1, …, T` as in the paper, with `2 ≤ T`. Stage
`t` has `n t` decision variables and `m t` equality constraints, and `N t > 0` sampled outcomes for
`2 ≤ t ≤ T`, each of probability `1 / N t`. The first-stage data `c₁, A₁, b₁` are deterministic.

Index convention: the sampled data of stage `t + 1` are stored under the index `t` of the
decision they follow. For `1 ≤ t ≤ T − 1` and an outcome `j < N (t+1)`:
`c t j` is `c̃_{t+1,j}`, `A t j` is `Ã_{t+1,j}`, `b t j` is `b̃_{t+1,j}`, and `B t j` is
`B̃_{t+1,j}`, the matrix that multiplies the stage-`t` decision `x_t` in the stage-`(t+1)`
constraint `B̃_{t+1,j} x_t + Ã_{t+1,j} x_{t+1} = b̃_{t+1,j}`. All four depend on the outcome `j`.
Values of the fields outside these ranges are never used. -/
structure Instance where
  T : ℕ
  hT : 2 ≤ T
  n : ℕ → ℕ
  m : ℕ → ℕ
  N : ℕ → ℕ
  hN : ∀ t, 2 ≤ t → t ≤ T → 0 < N t
  c₁ : Fin (n 1) → ℝ
  A₁ : Matrix (Fin (m 1)) (Fin (n 1)) ℝ
  b₁ : Fin (m 1) → ℝ
  c : (t : ℕ) → Fin (N (t + 1)) → Fin (n (t + 1)) → ℝ
  A : (t : ℕ) → Fin (N (t + 1)) → Matrix (Fin (m (t + 1))) (Fin (n (t + 1))) ℝ
  B : (t : ℕ) → Fin (N (t + 1)) → Matrix (Fin (m (t + 1))) (Fin (n t)) ℝ
  b : (t : ℕ) → Fin (N (t + 1)) → Fin (m (t + 1)) → ℝ

variable (I : Instance)

/-- The feasible set `{x₁ ≥ 0 : A₁ x₁ = b₁}` of the first-stage problem (3.7). -/
def Feas₁ : Set (Fin (I.n 1) → ℝ) :=
  {x | 0 ≤ x ∧ I.A₁ *ᵥ x = I.b₁}

/-- The stage-`(t+1)` right-hand side `b̃_{t+1,j} − B̃_{t+1,j} x_t`. -/
def rhs (t : ℕ) (x : Fin (I.n t) → ℝ) (j : Fin (I.N (t + 1))) : Fin (I.m (t + 1)) → ℝ :=
  I.b t j - I.B t j *ᵥ x

/-- The stage-`(t+1)` feasible set `{x_{t+1} ≥ 0 : Ã_{t+1,j} x_{t+1} = b̃_{t+1,j} − B̃_{t+1,j} x_t}`
after decision `x = x_t` and outcome `j`, as in (3.5). -/
def Feas (t : ℕ) (x : Fin (I.n t) → ℝ) (j : Fin (I.N (t + 1))) : Set (Fin (I.n (t + 1)) → ℝ) :=
  {y | 0 ≤ y ∧ I.A t j *ᵥ y = rhs I t x j}

/-- Auxiliary recursion on the number `r` of remaining stages: `Vrem r t x` is the SAA expected
cost-to-go after decision `x = x_t` when `r` further stages follow. -/
noncomputable def Vrem : ℕ → (t : ℕ) → (Fin (I.n t) → ℝ) → ℝ
  | 0, _, _ => 0
  | r + 1, t, x => (1 / (I.N (t + 1) : ℝ)) * ∑ j : Fin (I.N (t + 1)),
      sInf ((fun y => I.c t j ⬝ᵥ y + Vrem r (t + 1) y) '' Feas I t x j)

/-- `V t x` is the SAA cost-to-go `𝒬̃_{t+1}(x_t)` of (3.6); `V t ≡ 0` for `t ≥ T`
(`𝒬̃_{T+1} ≡ 0`). It is a genuine average of infima only on reachable states under
`FiniteValued` (Lean's `sInf` is `0` on empty or unbounded-below sets). -/
noncomputable def V (t : ℕ) (x : Fin (I.n t) → ℝ) : ℝ :=
  Vrem I (I.T - t) t x

/-- `Qo t x j` is `Q̃_{t+1,j}(x_t)` of (3.5), the optimal value of the stage-`(t+1)` problem for
outcome `j`: the infimum of `c̃_{t+1,j}ᵀ y + 𝒬̃_{t+2}(y)` over `Feas t x j`. -/
noncomputable def Qo (t : ℕ) (x : Fin (I.n t) → ℝ) (j : Fin (I.N (t + 1))) : ℝ :=
  sInf ((fun y => I.c t j ⬝ᵥ y + V I (t + 1) y) '' Feas I t x j)

/-- The optimal value (3.7) of the SAA problem: the infimum of `c₁ᵀ x₁ + 𝒬̃₂(x₁)` over `Feas₁`. -/
noncomputable def optVal : ℝ :=
  sInf ((fun x => I.c₁ ⬝ᵥ x + V I 1 x) '' Feas₁ I)

/-- The reachable stage-`t` decisions: `Reach 1 = Feas₁`, and `Reach (t+1)` collects the feasible
stage-`(t+1)` decisions for some reachable `x_t` and some outcome `j`. -/
def Reach : (t : ℕ) → Set (Fin (I.n t) → ℝ)
  | 0 => ∅
  | 1 => Feas₁ I
  | t + 2 => {y | ∃ x ∈ Reach (t + 1), ∃ j, y ∈ Feas I (t + 1) x j}

/-- Finite-valued cost-to-go functions (p. 6, "We assume that the cost-to-go functions are finite
valued, in particular we assume the relatively complete recourse"), read on reachable states: for
every stage `1 ≤ t ≤ T − 1`, every reachable `x_t` and every outcome `j` of stage `t + 1`, the
stage-`(t+1)` problem (3.5) is feasible and its objective `c̃_{t+1,j}ᵀ y + 𝒬̃_{t+2}(y)` is bounded
below on its feasible set, so that `Q̃_{t+1,j}(x_t)` is finite. -/
def FiniteValued : Prop :=
  ∀ t, 1 ≤ t → t + 1 ≤ I.T → ∀ x ∈ Reach I t, ∀ j : Fin (I.N (t + 1)),
    (Feas I t x j).Nonempty ∧
      BddBelow ((fun y => I.c t j ⬝ᵥ y + V I (t + 1) y) '' Feas I t x j)

/-- A scenario of the SAA tree: one outcome index for each stage `2, …, T`. Coordinate `u` is the
outcome `j_{u+2}` of stage `u + 2`. There are `N = ∏_{t=2}^T N_t` scenarios, each of probability
`1 / N`. -/
abbrev Scen := (u : Fin (I.T - 1)) → Fin (I.N ((u : ℕ) + 2))

/-- A policy assigns to each stage `t` and each scenario a stage-`t` decision. -/
abbrev Policy := (t : ℕ) → Scen I → Fin (I.n t) → ℝ

/-- Implementability (nonanticipativity): the stage-`t` decision depends only on the outcomes of
stages `2, …, t`, i.e. `x̄_t = x̄_t(ξ̃_{[t]})`. -/
def IsImplementable (pol : Policy I) : Prop :=
  ∀ t (s s' : Scen I), (∀ u : Fin (I.T - 1), (u : ℕ) + 2 ≤ t → s u = s' u) → pol t s = pol t s'

/-- Feasibility of a policy on every scenario of the SAA tree: `x̄₁ ∈ Feas₁`, and for each stage
`t = u + 2 ≤ T` the decision `x̄_t` is feasible for the stage-`t` constraints given `x̄_{t−1}`
and the scenario's stage-`t` outcome. -/
def IsFeasiblePolicy (pol : Policy I) : Prop :=
  ∀ s : Scen I, pol 1 s ∈ Feas₁ I ∧
    ∀ u : Fin (I.T - 1), pol ((u : ℕ) + 2) s ∈ Feas I ((u : ℕ) + 1) (pol ((u : ℕ) + 1) s) (s u)

/-- A (feasible, implementable) policy of the SAA problem. -/
def IsPolicy (pol : Policy I) : Prop :=
  IsImplementable I pol ∧ IsFeasiblePolicy I pol

/-- The expected cost (3.15) of a policy on the SAA tree, every scenario having probability `1/N`:
`(1/N) Σ_s Σ_{t=1}^T c̃_t(s)ᵀ x̄_t(s)`. -/
noncomputable def expectedCost (pol : Policy I) : ℝ :=
  (Fintype.card (Scen I) : ℝ)⁻¹ * ∑ s : Scen I,
    (I.c₁ ⬝ᵥ pol 1 s + ∑ u : Fin (I.T - 1), I.c ((u : ℕ) + 1) (s u) ⬝ᵥ pol ((u : ℕ) + 2) s)

/-- An optimal policy of the SAA problem: a feasible implementable policy whose expected cost is
at most that of every feasible implementable policy. -/
def IsOptimalPolicy (pol : Policy I) : Prop :=
  IsPolicy I pol ∧ ∀ pol' : Policy I, IsPolicy I pol' → expectedCost I pol ≤ expectedCost I pol'

/-- The dynamic programming optimality conditions (3.18) on every scenario: `x̄₁` minimizes
`c₁ᵀ x + 𝒬̃₂(x)` over `Feas₁` (stage 1, with `B̃₀ = 0`), and for every stage `t = u + 2 ≤ T`,
`x̄_t` minimizes `c̃_tᵀ y + 𝒬̃_{t+1}(y)` over the stage-`t` feasible set given `x̄_{t−1}` and the
scenario's stage-`t` outcome (with `𝒬̃_{T+1} ≡ 0`). -/
def DPOptimal (pol : Policy I) : Prop :=
  (∀ s : Scen I, pol 1 s ∈ Feas₁ I ∧
      ∀ y ∈ Feas₁ I, I.c₁ ⬝ᵥ pol 1 s + V I 1 (pol 1 s) ≤ I.c₁ ⬝ᵥ y + V I 1 y) ∧
    ∀ (s : Scen I) (u : Fin (I.T - 1)),
      pol ((u : ℕ) + 2) s ∈ Feas I ((u : ℕ) + 1) (pol ((u : ℕ) + 1) s) (s u) ∧
        ∀ y ∈ Feas I ((u : ℕ) + 1) (pol ((u : ℕ) + 1) s) (s u),
          I.c ((u : ℕ) + 1) (s u) ⬝ᵥ pol ((u : ℕ) + 2) s + V I ((u : ℕ) + 2) (pol ((u : ℕ) + 2) s) ≤
            I.c ((u : ℕ) + 1) (s u) ⬝ᵥ y + V I ((u : ℕ) + 2) y

end ShapiroSDDP.Convergence


