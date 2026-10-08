-- Prove2me | Definitions.Def_ConstrNestedLogit_UpperBound_Relaxation
-- name    : ConstrNestedLogit_UpperBound_Relaxation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:03:26.618389+00:00
-- url     : https://prove2.me/theorems/21f09691-0adc-4993-98f9-e53050c46ae0
-- title:
--   §1, §5.1, pp. 8, 19–20 — space constraints, the LP relaxation of the knapsack problem (10), and families of its solutions
-- statement:
--   Consider the nested logit model with nests $M$ and products $N = \{1, \dots, n\}$ in each nest, preference weights $v_{ij}$ and revenues $r_{ij}$. Product $j$ of nest $i$ consumes $w_{ij}$ units of space and the space available in nest $i$ is $c_i$. The feasible assortments of nest $i$ are
--
--   $$\mathcal C_i = \Big\{ S_i \in \{0,1\}^n : \sum_{j \in N} w_{ij} S_{ij} \le c_i \Big\}.$$
--
--   For a scalar $u$, problem (7) of nest $i$ under space constraints is the knapsack problem (10), $\max\{\sum_{j\in N} v_{ij}(r_{ij}-u)x_{ij} : \sum_{j\in N} w_{ij}x_{ij}\le c_i,\ x_{ij}\in\{0,1\}\}$. Its **linear programming relaxation** replaces $x_{ij} \in \{0,1\}$ by $x_{ij} \in [0,1]$:
--
--   $$\max\Big\{ \sum_{j\in N} v_{ij}(r_{ij}-u)\,x_{j} \;:\; \sum_{j\in N} w_{ij}\,x_{j}\le c_i,\ x \in [0,1]^n \Big\}.$$
--
--   A vector $x$ is an optimal solution of the relaxation at $u$ when it is feasible and no feasible vector has a larger objective value.
--
--   Finally, a family $\{X_i : i \in M\}$ of finite sets of vectors is a **family of relaxation solutions** when every vector of $X_i$ is feasible for the relaxation of nest $i$, and for every $u \ge 0$ the set $X_i$ contains an optimal solution of the relaxation of nest $i$ at $u$. The paper's solutions $\{x_i^g : g \in \mathcal G_i\}$, one optimal solution for each interval $\mathcal I_i^g$ of the partition of the nonnegative half-line by the breakpoints of the ratios $v_{ij}(r_{ij}-u)/w_{ij}$ (p. 20), form such a family.
--
--   These objects carry the linear program (13) and Proposition 7.
--
--   **Formalization Note** Products are indexed $0, \dots, n-1$ (`Fin n`); assortments are finite sets of products, with $\sum_{j \in S} w_{ij} \le c_i$ as the space constraint. The family $X_i$ is abstract: any finite family with the two properties above, not only the paper's interval solutions. These two properties are exactly what the proof of Proposition 7 uses about $\{x_i^g\}$. The family is fixed before $u$.
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, pp. 8 and 19–20, §1 (space constraints) and §5.1 (problem (10), its linear programming relaxation, the solutions x_i^g)

import Mathlib
import Definitions.Def_NestedLogitVariants_General_Model
import Definitions.Def_NestedLogitVariants_General_Relaxation

namespace ConstrNestedLogit.UpperBound

open NestedLogitVariants.General

variable {ι : Type*} {n : ℕ}

/-- The space constraint of nest `i` (§1, p. 8; §5, p. 19): the assortment `S` belongs to
`C_i = {S_i ∈ {0,1}^n : ∑_{j ∈ N} w_{ij} S_{ij} ≤ c_i}`, i.e. `∑_{j ∈ S} w_{ij} ≤ c_i`. -/
def SpaceFeasible (w : ι → Fin n → ℝ) (c : ι → ℝ) (i : ι) (S : Finset (Fin n)) : Prop :=
  ∑ j ∈ S, w i j ≤ c i

/-- The objective of the knapsack problem (10) (§5.1, p. 19) for nest `i` at `u`, evaluated at a
(possibly fractional) vector `x`: `∑_{j ∈ N} v_{ij} (r_{ij} − u) x_{ij}`. -/
def relaxObj (I : Instance ι n) (i : ι) (u : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ j, I.v i j * (I.r i j - u) * x j

/-- `x` is feasible for the linear programming relaxation of the knapsack problem (10) of nest `i`
(§5.1, p. 19): `x ∈ [0, 1]^n` and `∑_{j ∈ N} w_{ij} x_{ij} ≤ c_i`. -/
def RelaxFeasible (w : ι → Fin n → ℝ) (c : ι → ℝ) (i : ι) (x : Fin n → ℝ) : Prop :=
  x ∈ box n ∧ ∑ j, w i j * x j ≤ c i

/-- `x` is an optimal solution of the linear programming relaxation of (10) for nest `i` at `u`:
feasible, and no feasible vector has a larger objective value. -/
def RelaxOptimal (I : Instance ι n) (w : ι → Fin n → ℝ) (c : ι → ℝ) (i : ι) (u : ℝ)
    (x : Fin n → ℝ) : Prop :=
  RelaxFeasible w c i x ∧ ∀ x', RelaxFeasible w c i x' → relaxObj I i u x' ≤ relaxObj I i u x

/-- The two properties of the solutions `{x_i^g : g ∈ G_i}` of §5.1 (p. 20) that LP (13) and
Proposition 7 use: for every nest `i`, every vector of the finite family `X i` is feasible for the
linear programming relaxation of (10), and for every `u ≥ 0` some vector of `X i` is optimal for
that relaxation at `u`. The family is fixed before `u`. -/
def IsRelaxSolutionFamily (I : Instance ι n) (w : ι → Fin n → ℝ) (c : ι → ℝ)
    (X : ι → Finset (Fin n → ℝ)) : Prop :=
  (∀ i, ∀ x ∈ X i, RelaxFeasible w c i x) ∧
    ∀ i, ∀ u : ℝ, 0 ≤ u → ∃ x ∈ X i, RelaxOptimal I w c i u x

end ConstrNestedLogit.UpperBound


