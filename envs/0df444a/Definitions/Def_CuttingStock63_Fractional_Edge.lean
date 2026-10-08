-- Prove2me | Definitions.Def_CuttingStock63_Fractional_Edge
-- name    : CuttingStock63_Fractional_Edge
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T07:54:57.400153+00:00
-- url     : https://prove2.me/theorems/d894a7a4-286e-48be-8869-d297927228b8
-- title:
--   Customer Tolerances, pp. 882–883 — basic feasible solutions and the edge of a nonbasic variable
-- statement:
--   Let $A$ be a real $m\times n$ matrix and $b\in\mathbb R^m$, and consider the feasible set
--   $$P=\{x\in\mathbb R^n:\ x\ge 0,\ Ax=b\}.$$
--   In Gilmore and Gomory's cutting stock problem with customer tolerances, the columns of $A$ are the cutting patterns $a_j$ together with the slack columns $-e_i$ of the equations $\sum_j a_{ij}x_j-s_i=N_i'$.
--
--   1. **Basic feasible solution.** A point $\bar x$ is a basic feasible solution with basis $B\subseteq\{1,\dots,n\}$ if $\bar x\in P$, $|B|=m$, the columns of $A$ indexed by $B$ are linearly independent, and $\bar x_k=0$ for every nonbasic index $k\notin B$. These are the vertices the simplex method visits.
--   2. **Edge direction.** For a nonbasic index $j\notin B$, a vector $v\in\mathbb R^n$ is the direction of the edge of $x_j$ if
--   $$Av=0,\qquad v_j=1,\qquad v_k=0\ \text{ for every nonbasic } k\ne j .$$
--   Moving from $\bar x$ to $\bar x+\tau v$ ($\tau\ge 0$) is "the edge that would be traced out if $x_j$ were increased, but all other nonbasic variables kept zero" (p. 883). When $B$ is a basis there is exactly one such $v$ for each $j\notin B$; its basic part is $-A_B^{-1}a_j$.
--
--   These are the objects of the simplex method's improvement test: at a vertex one inspects, for each nonbasic variable, the rate of change of the objective along its edge.
--
--   **Formalization Note** The feasible set is the published `DermanSeqDecisions.LinProg.IsFeasible11` and the basis is the published `MatousekLP.BFS.IsBasis`. Indices are 0-based. The edge direction is defined relationally (no basis inverse appears); its existence and uniqueness for a basis are facts to be proved, not part of the definition. Feasibility of the edge ($\bar x+\tau v\ge0$ for small $\tau>0$) is deliberately not required: at a degenerate vertex some edges leave $P$ at once, and the simplex test still inspects them.
-- source:
--   Gilmore & Gomory, A linear programming approach to the cutting stock problem—Part II, Opns. Res. 11 (1963), pp. 882–883, Customer Tolerances, paragraph "It follows that …" (p. 882) and the definition of the edge after (5)'s preamble (p. 883)

import Mathlib
import Definitions.Def_DermanSeqDecisions_LinProg_LinearFractional
import Definitions.Def_MatousekLP_BFS_EquationalForm

namespace CuttingStock63.Fractional

/-! Vertices and edges of the simplex method for the linear-fractional program of
Gilmore & Gomory, *A linear programming approach to the cutting stock problem—Part II*,
Opns. Res. 11 (1963), Customer Tolerances, pp. 881–883.

The feasible set is `{x : Fin n → ℝ | x ≥ 0, A x = b}` (Derman's `IsFeasible11`, published) and
the objective is `ζ(x) = (∑ c_i x_i)/(∑ d_i x_i)` (Derman's `fracObj`, published). A basis is
Matoušek's `IsBasis` (published): `m` columns of `A` that are linearly independent. Indices are
0-based. -/

open Matrix

variable {m n : ℕ}

/-- A vertex of the simplex method: `x` is feasible (`x ≥ 0`, `A x = b`), `B` is a basis of `A`
(`|B| = m`, columns of `A` indexed by `B` linearly independent), and every nonbasic variable
`x_k`, `k ∉ B`, is zero. -/
def IsBasicFeasibleFor (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (B : Finset (Fin n))
    (x : Fin n → ℝ) : Prop :=
  DermanSeqDecisions.LinProg.IsFeasible11 A b x ∧ MatousekLP.BFS.IsBasis A B ∧
    ∀ k, k ∉ B → x k = 0

/-- `v` is the direction of the edge of the nonbasic variable `x_j` at the basis `B`
(p. 883: "the edge that would be traced out if `x_j` were increased, but all other nonbasic
variables kept zero"): `j ∉ B`, `A v = 0` (the equations stay satisfied), `v_j = 1`, and
`v_k = 0` for every other nonbasic `k`. Nonnegativity of `x + τ v` is not required (an edge of a
degenerate vertex may leave the feasible set at once). -/
def IsEdgeDirection (A : Matrix (Fin m) (Fin n) ℝ) (B : Finset (Fin n)) (j : Fin n)
    (v : Fin n → ℝ) : Prop :=
  j ∉ B ∧ A *ᵥ v = 0 ∧ v j = 1 ∧ ∀ k, k ∉ B → k ≠ j → v k = 0

end CuttingStock63.Fractional


