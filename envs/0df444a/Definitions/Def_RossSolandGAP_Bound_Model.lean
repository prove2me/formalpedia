-- Prove2me | Definitions.Def_RossSolandGAP_Bound_Model
-- name    : RossSolandGAP_Bound_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:07:25.169496+00:00
-- url     : https://prove2.me/theorems/87e83b59-7b7b-41ec-b222-8bbd67019543
-- title:
--   The generalized assignment problem (P), its relaxations (PR), (PR_λ), (PR_L), the knapsacks (PK_i) and the bound LB
-- statement:
--   This file sets up the objects of Ross and Soland's bounding procedure for the **generalized assignment problem**.
--
--   There are $m$ agents $I=\{1,\dots,m\}$ and $n$ tasks $J=\{1,\dots,n\}$. Assigning task $j$ to agent $i$ costs $c_{ij}$ and uses $r_{ij}$ units of agent $i$'s resource; agent $i$ has $b_i$ units available. The problem is
--
--   $$
--   \text{(P)}\qquad \min \sum_{i\in I}\sum_{j\in J} c_{ij}x_{ij}\quad\text{s.t.}\quad \sum_{j\in J} r_{ij}x_{ij}\le b_i\ (i\in I),\qquad \sum_{i\in I}x_{ij}=1\ (j\in J),\qquad x_{ij}\in\{0,1\}.
--   $$
--
--   The file defines:
--
--   1. the objective $\sum_i\sum_j c_{ij}x_{ij}$ and the feasible sets of (P), of the relaxation **(PR)** (drop the resource constraints), and of the **Lagrangean relaxation (PR$_\lambda$)** (keep the resource constraints, drop the assignment constraints), together with the (PR$_\lambda$) objective $\sum_i\sum_j c_{ij}x_{ij}+\sum_j\lambda_j\bigl(1-\sum_i x_{ij}\bigr)$;
--   2. a **cheapest-agent selection** $j\mapsto i_j$ with $c_{i_j j}=\min_{i\in I}c_{ij}$, the (PR) solution $x_{i_j j}=1$, $x_{ij}=0$ for $i\neq i_j$, and its value $Z=\sum_j c_{i_j j}$;
--   3. $J_i=\{j : i_j=i\}$, the load $\sum_{j\in J_i} r_{ij}$, the set $I'=\{i : \sum_{j\in J_i}r_{ij}>b_i\}$ of overloaded agents, and the excess $d_i=\sum_{j\in J_i}r_{ij}-b_i$;
--   4. the penalty $p_j=\min_{k\in I-\{i_j\}}\{c_{kj}-c_{i_j j}\}$ and $c_{2j}=\min_{k\in I-\{i_j\}}c_{kj}$, the second smallest of $c_{1j},\dots,c_{mj}$ counted with multiplicity (both need $m\ge 2$);
--   5. the binary knapsack **(PK$_i$)**: minimize $z_i=\sum_{j\in J_i}p_jy_{ij}$ subject to $\sum_{j\in J_i}r_{ij}y_{ij}\ge d_i$, $y_{ij}\in\{0,1\}$; optimality of a solution $y^*_i$; and the revised bound $\mathrm{LB}=Z+\sum_{i\in I'}z^*_i$, where $z^*_i$ is the objective value of the optimal solution $y^*_i$;
--   6. the solution rebuilt from the $y^*$ (each task $j$ with $i_j\in I'$ and $y^*_{i_j j}=1$ is moved from $i_j$ to a given agent $k_j$);
--   7. agent $i$'s knapsack in the separated (PR$_\lambda$): maximize $\sum_j(\lambda_j-c_{ij})v_j$ subject to $\sum_j r_{ij}v_j\le b_i$, $v_j\in\{0,1\}$;
--   8. the bounded-variable linear program **(PR$_L$)**: minimize $\sum_i\sum_j c_{ij}x_{ij}$ subject to $\sum_i x_{ij}=1$, $0\le x_{ij}\le 1$, and its dual: maximize $\sum_j\lambda_j-\sum_i\sum_j u_{ij}$ subject to $\lambda_j-u_{ij}\le c_{ij}$, $u_{ij}\ge0$, where $u_{ij}$ is the multiplier of the bound $x_{ij}\le 1$; and optimality of a dual solution $(\lambda,u)$.
--
--   These are the objects of every statement of the mission.
--
--   **Formalization Note** Agents and tasks are indexed $0,\dots,m-1$ and $0,\dots,n-1$ (`Fin m`, `Fin n`). All data and variables are real numbers; a 0-1 variable is a real number equal to $0$ or $1$, so the paper's sums are literal. The cheapest-agent selection is a function `a : Fin n → Fin m` that the theorems take as an argument together with the hypothesis `IsCheapest c a`, so every statement holds for every tie-break. $p_j$ and $c_{2j}$ are minima over the nonempty set $I-\{i_j\}$ and take the proof `hm : 1 < m` as an argument. $J_i$, $I'$ and $d_i$ are those of the (PR) solution built from `a`. (PK$_i$) constrains $y_{ij}$ only for $j\in J_i$; values outside $J_i$ are irrelevant. $z^*_i$ is not an infimum: $\mathrm{LB}$ is computed from given solutions `ystar i`, and the theorems assume that each is optimal for (PK$_i$), $i\in I'$. The paper's standing hypotheses ($b_i>0$, and $r_{ij}\ge 0$, implicit in "the resource required") are hypotheses of the theorems, not part of the definitions.
-- source:
--   Ross & Soland, A Branch and Bound Algorithm for the Generalized Assignment Problem, Mathematical Programming 8, 1975, DOI 10.1007/BF01580430, p. 92 §1 (P), displays (1)-(3); pp. 93-94 §2 (PR), Z; p. 94 J_i, I', (PK_i), d_i, p_j, LB; pp. 94-95 rebuilt solution; p. 95 (PR_λ) and its separation; pp. 95-96 (PR_L), c_1j, c_2j

import Mathlib

namespace RossSolandGAP.Bound

open Finset

/-!
Ross & Soland (1975), §1 (p. 92) and §2 (pp. 93–96): the generalized assignment problem (P),
its relaxations (PR), (PR_λ), (PR_L), the knapsack problems (PK_i) and the bound LB.

Agents `I = {1, …, m}` are `Fin m` and tasks `J = {1, …, n}` are `Fin n` (0-based).
Costs `c`, resources `r`, budgets `b`, multipliers and the 0-1 variables are real numbers;
a 0-1 variable is a real `x i j` with `x i j = 0 ∨ x i j = 1`.
-/

variable {m n : ℕ}

/-- Every entry of `x` is `0` or `1` (the constraint `x_ij = 0 or 1`). -/
def IsBinary (x : Fin m → Fin n → ℝ) : Prop := ∀ i j, x i j = 0 ∨ x i j = 1

/-- The objective (1): `Σ_{i∈I} Σ_{j∈J} c_ij x_ij`. -/
def cost (c x : Fin m → Fin n → ℝ) : ℝ := ∑ i, ∑ j, c i j * x i j

/-- Feasibility for (P): binary, the resource constraints (2), and the assignment
constraints (3). -/
def FeasibleP (r : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin m → Fin n → ℝ) : Prop :=
  IsBinary x ∧ (∀ i, ∑ j, r i j * x i j ≤ b i) ∧ ∀ j, ∑ i, x i j = 1

/-- Feasibility for the relaxation (PR): binary and the assignment constraints (3). -/
def FeasiblePR (x : Fin m → Fin n → ℝ) : Prop :=
  IsBinary x ∧ ∀ j, ∑ i, x i j = 1

/-- Feasibility for the Lagrangean relaxation (PR_λ): binary and the resource
constraints (2); the assignment constraints (3) are dualized. -/
def FeasibleLag (r : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin m → Fin n → ℝ) : Prop :=
  IsBinary x ∧ ∀ i, ∑ j, r i j * x i j ≤ b i

/-- The objective of (PR_λ) as printed:
`Σ_i Σ_j c_ij x_ij + Σ_j λ_j (1 − Σ_i x_ij)`. -/
def lagObj (c : Fin m → Fin n → ℝ) (lam : Fin n → ℝ) (x : Fin m → Fin n → ℝ) : ℝ :=
  cost c x + ∑ j, lam j * (1 - ∑ i, x i j)

/-- `a` is a cheapest-agent selection: `a j` is an index `i_j` with
`c_{i_j j} = min_{i∈I} c_ij`. -/
def IsCheapest (c : Fin m → Fin n → ℝ) (a : Fin n → Fin m) : Prop :=
  ∀ j k, c (a j) j ≤ c k j

/-- The (PR) lower bound `Z = Σ_{j∈J} c_{i_j j}`. -/
def Z (c : Fin m → Fin n → ℝ) (a : Fin n → Fin m) : ℝ := ∑ j, c (a j) j

/-- The "obvious solution" of (PR): `x_{i_j j} = 1` and `x_ij = 0` for `i ≠ i_j`. -/
def xPR (a : Fin n → Fin m) : Fin m → Fin n → ℝ := fun i j => if a j = i then 1 else 0

/-- `J_i = {j : x_ij = 1}` for the (PR) solution `xPR a`, i.e. the tasks with `i_j = i`. -/
def Jset (a : Fin n → Fin m) (i : Fin m) : Finset (Fin n) :=
  univ.filter (fun j => a j = i)

/-- `Σ_{j∈J_i} r_ij x_ij` at the (PR) solution. -/
def load (r : Fin m → Fin n → ℝ) (a : Fin n → Fin m) (i : Fin m) : ℝ :=
  ∑ j ∈ Jset a i, r i j

/-- `I' = {i : Σ_{j∈J_i} r_ij x_ij > b_i}`, the agents whose constraint (2) is violated by
the (PR) solution. -/
noncomputable def Iprime (r : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (a : Fin n → Fin m) : Finset (Fin m) :=
  univ.filter (fun i => b i < load r a i)

/-- `d_i = Σ_{j∈J_i} r_ij x_ij − b_i`. -/
def dgap (r : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (a : Fin n → Fin m) (i : Fin m) : ℝ :=
  load r a i - b i

/-- With at least two agents, the agents other than `i` form a nonempty set. -/
theorem others_nonempty (hm : 1 < m) (i : Fin m) : (univ.erase i).Nonempty := by
  rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin]
  omega

/-- The penalty `p_j = min_{k∈I−{i_j}} (c_kj − c_{i_j j})`. -/
noncomputable def pen (hm : 1 < m) (c : Fin m → Fin n → ℝ) (a : Fin n → Fin m) (j : Fin n) : ℝ :=
  (univ.erase (a j)).inf' (others_nonempty hm (a j)) (fun k => c k j - c (a j) j)

/-- `c_2j`: the smallest cost of task `j` among the agents other than the cheapest agent
`i_j`, i.e. the second smallest of `c_1j, …, c_mj` counted with multiplicity. -/
noncomputable def c2 (hm : 1 < m) (c : Fin m → Fin n → ℝ) (a : Fin n → Fin m) (j : Fin n) : ℝ :=
  (univ.erase (a j)).inf' (others_nonempty hm (a j)) (fun k => c k j)

/-- Feasibility for the knapsack problem (PK_i): `y_ij ∈ {0,1}` for `j ∈ J_i` and
`Σ_{j∈J_i} r_ij y_ij ≥ d_i`. Values of `y` outside `J_i` are irrelevant. -/
def FeasiblePK (r : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (a : Fin n → Fin m) (i : Fin m)
    (y : Fin n → ℝ) : Prop :=
  (∀ j ∈ Jset a i, y j = 0 ∨ y j = 1) ∧ dgap r b a i ≤ ∑ j ∈ Jset a i, r i j * y j

/-- The objective of (PK_i): `z_i = Σ_{j∈J_i} p_j y_ij`. -/
noncomputable def pkObj (hm : 1 < m) (c : Fin m → Fin n → ℝ) (a : Fin n → Fin m) (i : Fin m)
    (y : Fin n → ℝ) : ℝ :=
  ∑ j ∈ Jset a i, pen hm c a j * y j

/-- `y` is an optimal solution `y*_i` of (PK_i). -/
def IsOptPK (hm : 1 < m) (c r : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (a : Fin n → Fin m)
    (i : Fin m) (y : Fin n → ℝ) : Prop :=
  FeasiblePK r b a i y ∧ ∀ y', FeasiblePK r b a i y' → pkObj hm c a i y ≤ pkObj hm c a i y'

/-- The revised lower bound `LB = Z + Σ_{i∈I'} z*_i`, where `z*_i` is the (PK_i) objective of
`ystar i` (used under the hypothesis that each `ystar i`, `i ∈ I'`, is optimal for (PK_i)). -/
noncomputable def LB (hm : 1 < m) (c r : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (a : Fin n → Fin m)
    (ystar : Fin m → Fin n → ℝ) : ℝ :=
  Z c a + ∑ i ∈ Iprime r b a, pkObj hm c a i (ystar i)

/-- The solution rebuilt from the (PK_i) solutions (§2, pp. 94–95): starting from the (PR)
solution `xPR a`, every task `j` with `i_j ∈ I'` and `y*_{i_j j} = 1` is taken from its agent
`i_j` and given to the agent `k j` (the variable `x_{i_j j}` is set to `0` and `x_{k_j j}` to `1`);
every other task stays with `i_j`. -/
noncomputable def rebuilt (r : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (a : Fin n → Fin m)
    (ystar : Fin m → Fin n → ℝ) (k : Fin n → Fin m) : Fin m → Fin n → ℝ := fun i j =>
  if a j ∈ Iprime r b a ∧ ystar (a j) j = 1 then (if k j = i then 1 else 0) else xPR a i j

/-- Feasibility for agent `i`'s binary knapsack in the separated (PR_λ):
`v_j ∈ {0,1}` and `Σ_j r_ij v_j ≤ b_i`. -/
def KnapFeasible (r : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (i : Fin m) (v : Fin n → ℝ) : Prop :=
  (∀ j, v j = 0 ∨ v j = 1) ∧ ∑ j, r i j * v j ≤ b i

/-- The objective of agent `i`'s knapsack in the separated (PR_λ):
`Σ_j (λ_j − c_ij) v_j` (to be maximized). -/
def knapObj (c : Fin m → Fin n → ℝ) (lam : Fin n → ℝ) (i : Fin m) (v : Fin n → ℝ) : ℝ :=
  ∑ j, (lam j - c i j) * v j

/-- Feasibility for the bounded-variable linear program (PR_L):
`Σ_i x_ij = 1` for all `j` and `0 ≤ x_ij ≤ 1`. -/
def FeasiblePRL (x : Fin m → Fin n → ℝ) : Prop :=
  (∀ i j, 0 ≤ x i j ∧ x i j ≤ 1) ∧ ∀ j, ∑ i, x i j = 1

/-- Dual feasibility for (PR_L): multipliers `λ_j` (free) for `Σ_i x_ij = 1` and
`u_ij ≥ 0` for the upper bounds `x_ij ≤ 1`, with `λ_j − u_ij ≤ c_ij`. -/
def DualFeasiblePRL (c : Fin m → Fin n → ℝ) (lam : Fin n → ℝ) (u : Fin m → Fin n → ℝ) : Prop :=
  (∀ i j, 0 ≤ u i j) ∧ ∀ i j, lam j - u i j ≤ c i j

/-- The dual objective of (PR_L): `Σ_j λ_j − Σ_i Σ_j u_ij`. -/
def dualObjPRL (lam : Fin n → ℝ) (u : Fin m → Fin n → ℝ) : ℝ :=
  ∑ j, lam j - ∑ i, ∑ j, u i j

/-- `(λ, u)` is an optimal solution of the dual of (PR_L). -/
def IsOptDualPRL (c : Fin m → Fin n → ℝ) (lam : Fin n → ℝ) (u : Fin m → Fin n → ℝ) : Prop :=
  DualFeasiblePRL c lam u ∧
    ∀ (lam' : Fin n → ℝ) (u' : Fin m → Fin n → ℝ),
      DualFeasiblePRL c lam' u' → dualObjPRL lam' u' ≤ dualObjPRL lam u

end RossSolandGAP.Bound


