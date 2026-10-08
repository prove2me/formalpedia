-- Prove2me | Definitions.Def_ManneLP_Equilibrium_LP
-- name    : ManneLP_Equilibrium_LP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T12:53:36.004001+00:00
-- url     : https://prove2.me/theorems/91afb66d-e7f0-45f0-aeba-918513a05adf
-- title:
--   §4–§5 — Manne's linear program: constraints (4), (8.1)–(8.T), equation (8.0), cost coefficients (10), objective (9), and the decoding xᵢⱼ / Σⱼxᵢⱼ
-- statement:
--   This file defines the linear program of Manne (1960), §4–§5, in the unknowns $x_{ij}$, $(i,j)\in A$.
--
--   1. **Marginal** (3): $y_t=\sum_j x_{tj}$, the left-hand side of (8.0)–(8.T).
--   2. **Right-hand sides** (7):
--   $$
--   \sum_{\substack{i,j,n:\\ i+j-n\le 0}} p_n x_{ij}\quad\text{(for (8.0))},\qquad
--   \sum_{\substack{i,j,n:\\ i+j-n=t}} p_n x_{ij}\quad\text{(for (8.t), } t=1,\dots,T).
--   $$
--   3. **Equations** (8.0): $\sum_j x_{0j}=\sum_{i+j-n\le0}p_nx_{ij}$, and (8.t): $\sum_j x_{tj}=\sum_{i+j-n=t}p_nx_{ij}$.
--   4. **Feasibility.** $x$ is feasible if $x_{ij}\ge 0$ on $A$, (4) $\sum_{(i,j)\in A}x_{ij}=1$, and (8.1)–(8.T) hold. Equation (8.0) is not a constraint: the paper drops it as redundant.
--   5. **Cost coefficients** (10):
--   $$
--   c_{ij}=C_1(i)+C_2(j)+\sum_{n\ge0}p_nC_3(n-i-j),
--   $$
--   and the **objective** (9) $\sum_{(i,j)\in A}c_{ij}x_{ij}$. An **optimal solution** is a feasible $x$ whose objective is at most that of every feasible point.
--   6. **Decoding** (§3, N.B.). From $x$, the distribution $y_i=\sum_j x_{ij}$ and the rule
--   $$
--   q(j\mid i)=\frac{x_{ij}}{\sum_{j'}x_{ij'}}\quad\text{for }(i,j)\in A,\ \textstyle\sum_{j'}x_{ij'}\ne0,
--   $$
--   with the default pure action "produce nothing" ($q(0\mid i)=1$) at stock levels with $\sum_{j'}x_{ij'}=0$, and $q(j\mid i)=0$ off $A$.
--
--   This is the linear program whose optimal solutions the mission's goal theorem relates to optimal stationary decision rules.
--
--   **Formalization Note** $x$ is a function on $\mathbb N\times\mathbb N$ of which only the values on $A$ are read. The conditions $i+j-n\le0$ and $i+j-n=t$ are evaluated in $\mathbb Z$, exactly as printed; the sums over $n$ are `tsum`s (the one for (8.0) has infinitely many terms when the demand is unbounded). The page's quotient $x_{ij}/\sum_j x_{ij}$ is $0/0$ at stock levels that the equilibrium never visits; there the rule is not determined by $x$, and the default action $j=0$ (always admissible) is a choice of this formalization.
-- source:
--   Manne, Linear Programming and Sequential Decisions, Management Science 6 (1960), pp. 261–262 (PDF pp. 4–5), §3 (3), (4), N.B.; §4 (7), (8.0)–(8.T), last paragraph; §5 (9), (10)

import Mathlib
import Definitions.Def_ManneLP_Equilibrium_Model

namespace ManneLP.Equilibrium

/-- `Σⱼ xₜⱼ`, the left side of (8.0)–(8.T), and `yₜ` of (3). -/
def marginal (M : Model) (x : ℕ × ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ j ∈ actions M t, x (t, j)

/-- The right side of (7)/(8.0): `Σ_{i,j,n : i+j−n ≦ 0} pₙ xᵢⱼ`. -/
noncomputable def rhsZero (M : Model) (x : ℕ × ℕ → ℝ) : ℝ :=
  ∑ a ∈ M.A, ∑' n : ℕ,
    if (a.1 : ℤ) + (a.2 : ℤ) - (n : ℤ) ≤ 0 then M.p n * x a else 0

/-- The right side of (7)/(8.t), `t = 1, …, T`: `Σ_{i,j,n : i+j−n = t} pₙ xᵢⱼ`. -/
noncomputable def rhsPos (M : Model) (x : ℕ × ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ a ∈ M.A, ∑' n : ℕ,
    if (a.1 : ℤ) + (a.2 : ℤ) - (n : ℤ) = (t : ℤ) then M.p n * x a else 0

/-- Equation (8.0). -/
def Eq80 (M : Model) (x : ℕ × ℕ → ℝ) : Prop :=
  marginal M x 0 = rhsZero M x

/-- Equation (8.t). -/
def Eq8t (M : Model) (x : ℕ × ℕ → ℝ) (t : ℕ) : Prop :=
  marginal M x t = rhsPos M x t

/-- The constraint set of Manne's linear program (§4, last paragraph): `xᵢⱼ ≧ 0` on the admissible
pairs, (4) `Σ xᵢⱼ = 1`, and (8.1)–(8.T). Equation (8.0) is deliberately not included. -/
def IsLPFeasible (M : Model) (x : ℕ × ℕ → ℝ) : Prop :=
  (∀ a ∈ M.A, 0 ≤ x a) ∧ ∑ a ∈ M.A, x a = 1 ∧ ∀ t, 1 ≤ t → t ≤ M.T → Eq8t M x t

/-- The cost coefficient (10): `cᵢⱼ = C₁(i) + C₂(j) + Σₙ pₙ C₃(n − i − j)`. -/
noncomputable def costCoeff (M : Model) (i j : ℕ) : ℝ :=
  M.C₁ i + M.C₂ j + ∑' n : ℕ, M.p n * M.C₃ ((n : ℤ) - (i : ℤ) - (j : ℤ))

/-- The objective (9): `Σ_{i,j} cᵢⱼ xᵢⱼ`. -/
noncomputable def lpObj (M : Model) (x : ℕ × ℕ → ℝ) : ℝ :=
  ∑ a ∈ M.A, costCoeff M a.1 a.2 * x a

/-- `x` is an optimal solution of the linear program: feasible, and of least objective (9) among
feasible points. -/
def IsLPOptimal (M : Model) (x : ℕ × ℕ → ℝ) : Prop :=
  IsLPFeasible M x ∧ ∀ x', IsLPFeasible M x' → lpObj M x ≤ lpObj M x'

/-- The decoded equilibrium distribution (3): `yᵢ = Σⱼ xᵢⱼ`. -/
def decodeDist (M : Model) (x : ℕ × ℕ → ℝ) : ℕ → ℝ :=
  fun i => marginal M x i

/-- The decoded decision rule (§3, N.B.): `q(j | i) = xᵢⱼ / Σⱼ xᵢⱼ` on admissible pairs when
`Σⱼ xᵢⱼ ≠ 0`; at a stock level with `Σⱼ xᵢⱼ = 0` (never visited in equilibrium) the default pure
action "produce nothing" (`j = 0`) is used. -/
noncomputable def decodeRule (M : Model) (x : ℕ × ℕ → ℝ) : ℕ → ℕ → ℝ :=
  fun i j =>
    if (i, j) ∈ M.A then
      (if marginal M x i ≠ 0 then x (i, j) / marginal M x i else if j = 0 then 1 else 0)
    else 0

end ManneLP.Equilibrium


