-- Prove2me | Definitions.Def_RepeatedNRM_Myopic_Model
-- name    : RepeatedNRM_Myopic_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-23T03:54:24.889485+00:00
-- url     : https://prove2.me/theorems/42294f20-b8be-4c9c-a189-05175c7dfda8
-- title:
--   §3–§4, pp. 9–18 — repeated network revenue management: X(b), revenue, service quality (3), budget dynamics, problem (5), myopic LP (7), relaxation (9), Assumptions 1–2
-- statement:
--   The **repeated network revenue management** model of Calmon, Ciocan and Romero (§3).
--
--   An instance has $n$ product types and $m$ customers. In every period the platform has supply $s_i\ge 0$ of product $i$; customer $j$ pays the unit price $p_{ij}\ge 0$ for product $i$ and values it at $v_{ij}\ge p_{ij}$. Customer $j$'s state is a budget $b_j\in[0,1]$, and the budget update function $\varphi_j:[0,1]^2\to[0,1]$ maps the current budget and the service quality received to next period's budget.
--
--   1. **Feasible allocations** $X(\mathbf b)$: matrices $x=(x_{ij})$ with $x_{ij}\ge 0$, budget constraints $\sum_i p_{ij}x_{ij}\le b_j$ (1) and supply constraints $\sum_j x_{ij}\le s_i$ (2). The revenue is $R(x)=\sum_i\sum_j p_{ij}x_{ij}$.
--   2. **Customer side.** $X_j(b_j)$ is the projection of $X(\mathbf b)$ on customer $j$: vectors $y$ with $0\le y_i\le s_i$ and $\sum_i p_{ij}y_i\le b_j$. The utility is $U_j(y)=\sum_i (v_{ij}-p_{ij})y_i$ and $U^*_j(b_j)=\max_{y\in X_j(b_j)}U_j(y)$.
--   3. **Service quality** (3): $q_j(b_j,y)=U_j(y)/U^*_j(b_j)$, and $q_j=1$ when $b_j=0$.
--   4. **Dynamics**: $\mathbf b_{t+1}=\boldsymbol\varphi(\mathbf b_t,\mathbf q(\mathbf b_t,x_t))$, componentwise $b_{j,t+1}=\varphi_j(b_{j,t},q_j(b_{j,t},x_{j,t}))$. Definition 1: $\varphi^t_j(b,q)$ is the $t$-fold iterate of $b\mapsto\varphi_j(b,q)$.
--   5. **Problem (5)** maximizes $\sum_{t=1}^T R(x_t)$ over trajectories with $x_t\in X(\mathbf b_t)$ and the above dynamics. The **myopic policy** solves in each period the linear program (7), $\mathrm{MY}(\mathbf b)=\max\{R(x):x\in X(\mathbf b)\}$.
--   6. **Relaxations**: $J^{\mathrm{relax}}_T(\mathbf b_1)=\sum_{t=1}^T\mathrm{MY}(\boldsymbol\varphi^{t-1}(\mathbf b_1,1))$ (9) and $J^{LBMY}_T(\mathbf b_1)=\sum_{t=1}^T\mathrm{MY}(\boldsymbol\varphi^{t-1}(\mathbf b_1,1-\gamma))$ (EC.6).
--   7. **Assumption 1** for customer $j$: (i) $\varphi_j$ is non-decreasing in each argument on $[0,1]^2$; (ii) $\varphi_j(b,q)\ge\min\{b,q\}$; (iii) $\varphi^t_j(b,1-\vartheta)\ge(1-\vartheta)\varphi^t_j(b,1)$ for $b,\vartheta\in[0,1]$, $t\ge 1$.
--   8. **Assumption 2** with characteristic sets $A_j$ and $\gamma\in[0,1]$: $v_{ij}=p_{ij}=0$ for $i\notin A_j$, and $\min_{i\in A_j}v_{ij}/p_{ij}-1\ge(1-\gamma)(\max_{i\in A_j}v_{ij}/p_{ij}-1)$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** Allocations are indexed item-major, `x i j`. $U_j$ is only evaluated on $X_j(b_j)$, so the paper's "0 if infeasible" branch never matters. $U^*_j$ and $\mathrm{MY}$ are real suprema of nonempty bounded sets for nonnegative budgets, and are attained. When $U^*_j(b_j)=0$ with $b_j>0$, (3) is undefined; Lean sets the quality to $1$ there. Assumption 2 is written pairwise and includes $p_{ij}>0$ for $i\in A_j$, which its ratios require. Trajectories and myopic trajectories are predicates (`IsTrajectory`, `IsMyopicTrajectory`) on sequences indexed by $\mathbb N$, with index $0$ the paper's period $1$.
-- source:
--   Calmon, Ciocan & Romero, accepted manuscript (TSpace), pp. 9–18: §3 (1)–(3), (5), (7); Definition 1, Assumption 1, (9), Assumption 2 (pp. 16–18); (EC.6), p. ec7

import Mathlib

namespace RepeatedNRM.Myopic

/-- An instance of the repeated network revenue management (RNRM) model of §3 (pp. 9–11):
`n` product types, `m` customers, per-period supply `s i` of product `i`, unit price `p i j`
and unit valuation `v i j` of product `i` for customer `j`, and the budget update functions
`phi j : [0,1]² → [0,1]` of customer `j` (only their values on `[0,1]²` are ever used). -/
structure Instance where
  n : ℕ
  m : ℕ
  s : Fin n → ℝ
  p : Fin n → Fin m → ℝ
  v : Fin n → Fin m → ℝ
  phi : Fin m → ℝ → ℝ → ℝ

/-- The standing assumptions of §3: nonnegative supplies and prices, `v i j ≥ p i j` (p. 9),
and `φ_j` maps `[0,1]²` into `[0,1]` (p. 11). -/
def Instance.Standing (I : Instance) : Prop :=
  (∀ i, 0 ≤ I.s i) ∧ (∀ i j, 0 ≤ I.p i j) ∧ (∀ i j, I.p i j ≤ I.v i j) ∧
  (∀ j b q, b ∈ Set.Icc (0 : ℝ) 1 → q ∈ Set.Icc (0 : ℝ) 1 → I.phi j b q ∈ Set.Icc (0 : ℝ) 1)

variable (I : Instance)

/-- The feasible set `X(b)` of allocations, constraints (1), (2) and nonnegativity (p. 10).
An allocation `x i j` is the amount of product `i` given to customer `j`. -/
def feasible (b : Fin I.m → ℝ) (x : Fin I.n → Fin I.m → ℝ) : Prop :=
  (∀ i j, 0 ≤ x i j) ∧ (∀ j, ∑ i, I.p i j * x i j ≤ b j) ∧ (∀ i, ∑ j, x i j ≤ I.s i)

/-- Platform revenue `R(x) = ∑_i ∑_j p_ij x_ij` (p. 10). -/
def revenue (x : Fin I.n → Fin I.m → ℝ) : ℝ := ∑ i, ∑ j, I.p i j * x i j

/-- The projection `X_j(b_j)` of `X(b)` onto customer `j`'s allocations (p. 10). -/
def custFeasible (j : Fin I.m) (bj : ℝ) (y : Fin I.n → ℝ) : Prop :=
  (∀ i, 0 ≤ y i ∧ y i ≤ I.s i) ∧ ∑ i, I.p i j * y i ≤ bj

/-- Customer `j`'s utility `∑_i (v_ij − p_ij) y_i` of an allocation `y` (p. 10); only ever
evaluated on allocations in `X_j(b_j)`. -/
def utility (j : Fin I.m) (y : Fin I.n → ℝ) : ℝ := ∑ i, (I.v i j - I.p i j) * y i

/-- The maximum utility `U*_j(b_j) = max_{y ∈ X_j(b_j)} U_j(b_j, y)` (p. 10). -/
noncomputable def uStar (j : Fin I.m) (bj : ℝ) : ℝ :=
  sSup (utility I j '' {y | custFeasible I j bj y})

/-- The service quality (3) (p. 11): `1` if `b_j = 0`, otherwise `U_j / U*_j`; when
`U*_j(b_j) = 0` (where (3) is undefined) the quality is also `1`. -/
noncomputable def quality (j : Fin I.m) (bj : ℝ) (y : Fin I.n → ℝ) : ℝ :=
  if bj = 0 ∨ uStar I j bj = 0 then 1 else utility I j y / uStar I j bj

/-- The vector of service qualities `q(b, x)`. -/
noncomputable def qualityVec (b : Fin I.m → ℝ) (x : Fin I.n → Fin I.m → ℝ) (j : Fin I.m) : ℝ :=
  quality I j (b j) (fun i => x i j)

/-- The budget update `b_{t+1} = φ(b_t, q(b_t, x_t))` (p. 11). -/
noncomputable def update (b : Fin I.m → ℝ) (x : Fin I.n → Fin I.m → ℝ) : Fin I.m → ℝ :=
  fun j => I.phi j (b j) (qualityVec I b x j)

/-- Definition 1 (p. 16): `φ^t_j(b, q)`, the `t`-fold iterate of `b ↦ φ_j(b, q)`
(`φ^0_j(b, q) = b`). -/
def phiIter (j : Fin I.m) (t : ℕ) (b q : ℝ) : ℝ := (fun b' => I.phi j b' q)^[t] b

/-- The vector form `φ^t(b, q)` of Definition 1. -/
def phiIterVec (t : ℕ) (b : Fin I.m → ℝ) (q : ℝ) : Fin I.m → ℝ :=
  fun j => phiIter I j t (b j) q

/-- A feasible trajectory of problem (5) from the initial budgets `b1`; period `t + 1` of the
paper is index `t`. -/
def IsTrajectory (b1 : Fin I.m → ℝ) (x : ℕ → Fin I.n → Fin I.m → ℝ) (b : ℕ → Fin I.m → ℝ) :
    Prop :=
  b 0 = b1 ∧ ∀ t, feasible I (b t) (x t) ∧ b (t + 1) = update I (b t) (x t)

/-- A myopic allocation: an optimal solution of the linear program (7) (p. 13). -/
def IsMyopicAlloc (b : Fin I.m → ℝ) (x : Fin I.n → Fin I.m → ℝ) : Prop :=
  feasible I b x ∧ ∀ y, feasible I b y → revenue I y ≤ revenue I x

/-- A trajectory of the myopic policy: in every period the allocation is optimal for (7) at the
current budgets, and budgets follow the natural update (p. 13). -/
def IsMyopicTrajectory (b1 : Fin I.m → ℝ) (x : ℕ → Fin I.n → Fin I.m → ℝ)
    (b : ℕ → Fin I.m → ℝ) : Prop :=
  IsTrajectory I b1 x b ∧ ∀ t, IsMyopicAlloc I (b t) (x t)

/-- The optimal value `MY(b)` of the linear program (7) (p. 13). -/
noncomputable def MY (b : Fin I.m → ℝ) : ℝ := sSup (revenue I '' {x | feasible I b x})

/-- The value of the relaxation (9) (p. 17): `J^relax_T(b_1) = ∑_{t=1}^T MY(φ^{t−1}(b_1, 1))`. -/
noncomputable def Jrelax (T : ℕ) (b1 : Fin I.m → ℝ) : ℝ :=
  ∑ t ∈ Finset.range T, MY I (phiIterVec I t b1 1)

/-- The value of problem (EC.6) (p. ec7): `J^LBMY_T(b_1) = ∑_{t=1}^T MY(φ^{t−1}(b_1, 1 − γ))`. -/
noncomputable def JLBMY (T : ℕ) (b1 : Fin I.m → ℝ) (γ : ℝ) : ℝ :=
  ∑ t ∈ Finset.range T, MY I (phiIterVec I t b1 (1 - γ))

/-- Assumption 1(i) (p. 17): `φ_j` is non-decreasing in each argument on `[0,1]²`. -/
def Assumption1i (j : Fin I.m) : Prop :=
  (∀ q bh bl, q ∈ Set.Icc (0 : ℝ) 1 → bh ∈ Set.Icc (0 : ℝ) 1 → bl ∈ Set.Icc (0 : ℝ) 1 →
      bl ≤ bh → I.phi j bl q ≤ I.phi j bh q) ∧
  (∀ b qh ql, b ∈ Set.Icc (0 : ℝ) 1 → qh ∈ Set.Icc (0 : ℝ) 1 → ql ∈ Set.Icc (0 : ℝ) 1 →
      ql ≤ qh → I.phi j b ql ≤ I.phi j b qh)

/-- Assumption 1(ii) (p. 17): `φ_j(b, q) ≥ min{b, q}` on `[0,1]²`. -/
def Assumption1ii (j : Fin I.m) : Prop :=
  ∀ b q, b ∈ Set.Icc (0 : ℝ) 1 → q ∈ Set.Icc (0 : ℝ) 1 → min b q ≤ I.phi j b q

/-- Assumption 1(iii) (p. 17): `φ^t_j(b, 1 − ϑ) ≥ (1 − ϑ) φ^t_j(b, 1)` for `b, ϑ ∈ [0,1]`,
`t ≥ 1`. -/
def Assumption1iii (j : Fin I.m) : Prop :=
  ∀ b, b ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℕ, 1 ≤ t → ∀ θ, θ ∈ Set.Icc (0 : ℝ) 1 →
    (1 - θ) * phiIter I j t b 1 ≤ phiIter I j t b (1 - θ)

/-- Assumption 2 (p. 18) with characteristic sets `A j` and parameter `γ ∈ [0,1]`: products
outside `A j` have `v = p = 0` for customer `j`; products in `A j` have positive price; and
`min_{i∈A_j} v_ij/p_ij − 1 ≥ (1 − γ)(max_{i∈A_j} v_ij/p_ij − 1)`, written pairwise. -/
def Assumption2 (A : Fin I.m → Finset (Fin I.n)) (γ : ℝ) : Prop :=
  γ ∈ Set.Icc (0 : ℝ) 1 ∧
  (∀ j, ∀ i, i ∉ A j → I.v i j = 0 ∧ I.p i j = 0) ∧
  (∀ j, ∀ i ∈ A j, 0 < I.p i j) ∧
  (∀ j, ∀ i ∈ A j, ∀ k ∈ A j, (1 - γ) * (I.v k j / I.p k j - 1) ≤ I.v i j / I.p i j - 1)

end RepeatedNRM.Myopic


