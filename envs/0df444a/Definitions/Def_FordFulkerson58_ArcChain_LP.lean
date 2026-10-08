-- Prove2me | Definitions.Def_FordFulkerson58_ArcChain_LP
-- name    : FordFulkerson58_ArcChain_LP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T07:14:59.820549+00:00
-- url     : https://prove2.me/theorems/7e65e24d-13bc-4e49-be06-05fc03ee2082
-- title:
--   §2, pp. 1778–1779 — the arc-chain linear program (2)–(3), bases, basic feasible solutions, simplex multipliers (4), reduced costs
-- statement:
--   Let $N$ be a multi-commodity network with arcs $A_1,\dots,A_m$, capacities $b_r$, commodity-chain columns $C_1,\dots,C_n$ and incidence matrix $A = (a_{rs})$. The **arc-chain linear program** is
--   $$\text{maximize } \sum_{s=1}^{n} x_s \quad\text{subject to}\quad \sum_{s=1}^{n} a_{rs} x_s + x_{n+r} = b_r \ (r = 1,\dots,m),\qquad x_1,\dots,x_{n+m} \ge 0,$$
--   where $x_s$ is the flow along the chain $C_s$ and $x_{n+r}$ is the slack of arc $A_r$. Its constraint matrix is $[A \mid I]$; the objective coefficient of a chain column is $1$ and of a slack column $0$.
--
--   A **basis** is a choice of $m$ columns $s_1,\dots,s_m$ of $[A \mid I]$ whose $m\times m$ submatrix $B = (b_{rj})$ is invertible. Its **basic feasible solution** is the vector $z$ that vanishes off the chosen columns, satisfies all constraints with equality, and is non-negative. Its **simplex multipliers** are numbers $\alpha_1,\dots,\alpha_m$ with, for every basic column $j = s_1,\dots,s_m$,
--   $$\sum_{r=1}^{m} \alpha_r b_{rj} = \begin{cases} 1 & \text{if } j \le n,\\ 0 & \text{if } j > n,\end{cases}$$
--   which is (4). The **reduced cost** of a column $j$ is its objective coefficient minus $\sum_r \alpha_r$ times its entries; for a chain column $C_s$ it is $1 - \sum_r \alpha_r a_{rs}$, and for the slack column of arc $r$ it is $-\alpha_r$.
--
--   These are the simplex-method objects in which §3 phrases its pricing test.
--
--   **Formalization Note** The columns of $[A \mid I]$ are indexed by `Col N ⊕ E`: `Sum.inl s` is a chain column, `Sum.inr r` the slack column of arc `r`. A basis is a map `β : E → Col N ⊕ E` (its `i`-th column is `β i`), and invertibility of the basis matrix is a separate hypothesis `IsUnit (basisMatrix N β).det` wherever a basis is used. The chain flows `x` and slacks `y` are separate vectors in `Feasible`.
-- source:
--   Ford and Fulkerson, A suggested computation for maximal multi-commodity network flows, Management Sci. 50(12S) (2004), pp. 1778–1779, §2, displays (2), (3) and (4)

import Mathlib
import Definitions.Def_FordFulkerson58_ArcChain_Network

namespace FordFulkerson58.ArcChain

variable {V E ι : Type*} [DecidableEq E]

/-- The columns of the constraint matrix `[A | I]` of (3), indexed by `Col N ⊕ E`: `Sum.inl s` is the
incidence column of the chain `C_s` (variable `x_s`), `Sum.inr r'` is the unit column of the slack
variable `x_{n+r'}`. `column N j r` is the entry in row `r`. -/
def column (N : Network V E ι) : Col N ⊕ E → E → ℝ
  | Sum.inl s, r => inc N r s
  | Sum.inr r', r => if r = r' then 1 else 0

/-- The objective coefficients of (2): `1` for every chain variable, `0` for every slack variable. -/
def cost (N : Network V E ι) : Col N ⊕ E → ℝ :=
  Sum.elim (fun _ => 1) (fun _ => 0)

/-- Feasibility for (3): chain flows `x ≥ 0`, slacks `y ≥ 0` (the page's `x_{n+r}`), and for every arc
`r`, `∑_s a_rs x_s + x_{n+r} = b_r`. -/
def Feasible [Fintype ι] [Fintype E] (N : Network V E ι) (x : Col N → ℝ) (y : E → ℝ) : Prop :=
  (∀ s, 0 ≤ x s) ∧ (∀ r, 0 ≤ y r) ∧ ∀ r, ∑ s, inc N r s * x s + y r = N.b r

/-- The objective (2): the total flow `∑_s x_s`. -/
noncomputable def objective [Fintype ι] [Fintype E] (N : Network V E ι) (x : Col N → ℝ) : ℝ :=
  ∑ s, x s

/-- The basis matrix `B = (b_rj)` of a choice `β : E → Col N ⊕ E` of `m` columns `s₁, …, s_m`
(§2, p. 1779): its `i`-th column is the column `β i` of `[A | I]`. -/
def basisMatrix (N : Network V E ι) (β : E → Col N ⊕ E) : Matrix E E ℝ :=
  fun r i => column N (β i) r

/-- `z` is the basic feasible solution of the basis `β`: it vanishes off the basic columns, satisfies
every constraint of (3) with equality, and is non-negative. -/
def IsBasicFeasibleSolution [Fintype ι] [Fintype E] (N : Network V E ι) (β : E → Col N ⊕ E)
    (z : Col N ⊕ E → ℝ) : Prop :=
  (∀ j, j ∉ Set.range β → z j = 0) ∧ (∀ r, ∑ j, column N j r * z j = N.b r) ∧ ∀ j, 0 ≤ z j

/-- The simplex multipliers (4) of the basis `β`: for every basic column `j = β i`,
`∑_r α_r b_rj` equals the objective coefficient of `j` (`1` for a chain, `0` for a slack). -/
def IsSimplexMultiplier [Fintype E] (N : Network V E ι) (β : E → Col N ⊕ E) (α : E → ℝ) : Prop :=
  ∀ i, ∑ r, α r * basisMatrix N β r i = cost N (β i)

/-- The reduced cost of column `j` with respect to the multipliers `α`: its objective coefficient minus
`∑_r α_r` times its entries. For a chain column `C_s` this is `1 − ∑_r α_r a_rs`. -/
def reducedCost [Fintype E] (N : Network V E ι) (α : E → ℝ) (j : Col N ⊕ E) : ℝ :=
  cost N j - ∑ r, α r * column N j r

end FordFulkerson58.ArcChain


