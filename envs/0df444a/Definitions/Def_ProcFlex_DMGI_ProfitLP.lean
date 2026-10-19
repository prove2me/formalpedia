-- Prove2me | Definitions.Def_ProcFlex_DMGI_ProfitLP
-- name    : ProcFlex_DMGI_ProfitLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:24:55.3817+00:00
-- url     : https://prove2.me/theorems/7d6e1890-a2cc-4ed9-a33a-76ee5d2b78cc
-- title:
--   Finite capacitated bipartite profit LP (1) and dual (3)
-- statement:
--   For a finite set of plants and products, assign each plant a capacity $C_j$ and each product a margin $p_i$. A design $A$ specifies which plant–product arcs are available. A production vector $x_{ij}\ge0$ respects each product's demand $d_i$ and each plant's capacity. Its profit is $\sum_{(j,i)\in A}p_i x_{ij}$, and the program value is the supremum of this objective over feasible production vectors.
--
--   The associated dual variables $y_i,z_j\ge0$ satisfy $y_i+z_j\ge p_i$ on every arc, with objective $\sum_i d_i y_i+\sum_j C_j z_j$. This general LP interface can be reused independently of the paper's margin groups.
--
--   **Formalization Note** Lean writes `x j i` for the paper's $x_{ij}$. The demand and capacity constraints sum over all plants and products, while the objective sums over the arcs, as in equation (1).
-- source:
--   Wang, Wang & Zhang, Robust Optimization Approach to Process Flexibility Designs with Contribution Margin Differentials, SSRN 3233721 (version of 22 May 2020), pp. 11–12, (1); p. 16, (3)

import Mathlib

namespace ProcFlex.DMGI

open Finset

/-- The finite capacitated bipartite profit program underlying (1), independently of margin groups. -/
structure ProfitLPData (m n : ℕ) where
  C : Fin m → ℝ
  p : Fin n → ℝ

/-- A plant-product arc set; `(j,i)` means plant `j` can make product `i`. -/
abbrev Design (m n : ℕ) := Finset (Fin m × Fin n)

/-- The feasible production assignments of (1), with `x j i` denoting the paper's `xᵢⱼ`. -/
def ProfitLPData.PrimalFeasible {m n : ℕ} (D : ProfitLPData m n)
    (d : Fin n → ℝ) (x : Fin m → Fin n → ℝ) : Prop :=
  (∀ j i, 0 ≤ x j i) ∧ (∀ i, ∑ j, x j i ≤ d i) ∧
    (∀ j, ∑ i, x j i ≤ D.C j)

/-- The objective of (1), summing only over design arcs. -/
def ProfitLPData.profit {m n : ℕ} (D : ProfitLPData m n)
    (A : Design m n) (x : Fin m → Fin n → ℝ) : ℝ :=
  ∑ a ∈ A, D.p a.2 * x a.1 a.2

/-- The optimal profit in (1). On nonnegative demand the feasible set is nonempty and the
objective is bounded above, so this real supremum is the paper's maximum. -/
noncomputable def ProfitLPData.value {m n : ℕ} (D : ProfitLPData m n)
    (A : Design m n) (d : Fin n → ℝ) : ℝ :=
  sSup (D.profit A '' {x | D.PrimalFeasible d x})

/-- Feasibility in the dual (3). -/
def ProfitLPData.DualFeasible {m n : ℕ} (D : ProfitLPData m n)
    (A : Design m n) (y : Fin n → ℝ) (z : Fin m → ℝ) : Prop :=
  (∀ a ∈ A, D.p a.2 ≤ y a.2 + z a.1) ∧
    (∀ i, 0 ≤ y i) ∧ (∀ j, 0 ≤ z j)

/-- The dual objective in (3). -/
def ProfitLPData.dualObj {m n : ℕ} (D : ProfitLPData m n)
    (d : Fin n → ℝ) (y : Fin n → ℝ) (z : Fin m → ℝ) : ℝ :=
  ∑ i, d i * y i + ∑ j, D.C j * z j

end ProcFlex.DMGI


