-- Prove2me | Definitions.Def_ConstrNestedLogit_Card_Knapsack
-- name    : ConstrNestedLogit_Card_Knapsack
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:04:01.557299+00:00
-- url     : https://prove2.me/theorems/4abb6e71-1478-4d0c-8374-7363c3533c5a
-- title:
--   Utilities $f_{ij}(u)$, the knapsack problem (9), and optimality for problems (7) and (9) under a cardinality limit
-- statement:
--   Fix a nested logit instance (nests $i$, products $j \in N = \{1,\dots,n\}$, preference weights $v_{ij}$, revenues $r_{ij}$), a nest $i$ and a cardinality limit $c_i \in \mathbb{N}$. Assortments of nest $i$ are subsets $S \subseteq N$ (the paper's vectors $S_i \in \{0,1\}^n$), and the cardinality constraint is
--
--   $$\mathcal C_i = \{S \subseteq N : |S| \le c_i\}.$$
--
--   This module defines four objects.
--
--   1. The **utility line** of product $j$, $f_{ij}(u) = v_{ij}(r_{ij} - u)$ for $u \in \mathbb{R}$. The paper's additional line $f_{i0}(u) = 0$ is the constant $0$.
--   2. The **knapsack objective** of problem (9) at $u$: $\sum_{j \in S} f_{ij}(u) = \sum_{j\in S} v_{ij}(r_{ij}-u)$.
--   3. **Optimality for (9)**: $S$ is optimal at $u$ if $|S| \le c_i$ and $\sum_{j\in S} f_{ij}(u) \ge \sum_{j\in S'} f_{ij}(u)$ for every $S'$ with $|S'| \le c_i$.
--   4. **Optimality for (7)**: $S$ is optimal for $\max_{S \in \mathcal C_i} V_i(S)(R_i(S) - u)$ at $u$ if $S \in \mathcal C_i$ and
--
--   $$V_i(S)\,(R_i(S)-u) \ge V_i(S')\,(R_i(S')-u) \quad \text{for every } S' \in \mathcal C_i,$$
--
--   where $V_i(S)$ is the nest's total preference weight and $R_i(S) = \sum_{j\in S} v_{ij} r_{ij}/V_i(S)$ its conditional expected revenue.
--
--   Problem (7) is the single-nest subproblem to which the paper reduces the constrained assortment problem; under cardinality constraints it is equivalent, through (8), to the unit-weight knapsack problem (9).
--
--   **Formalization Note** Products are `Fin n` (0-based), assortments are `Finset (Fin n)`, and $c_i$ is a natural number. $V_i$ and $R_i$ are the published `NestedLogitVariants.LP.V` and `R`; they coincide with the paper's $V_i(S) = \sum_{j\in S} v_{ij}$ when the within-nest no-purchase weight `vnp i` is $0$, which every theorem of this mission that uses them assumes.
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, p. 8 (C_i), p. 14 (problem (7)), p. 16 (problem (9), f_ij)

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model

namespace ConstrNestedLogit.Card

open NestedLogitVariants.LP

variable {ι : Type*} {n : ℕ}

/-- The utility line `f_ij(u) = v_ij (r_ij − u)` of product `j` in nest `i` (Gallego–Topaloglu, §4,
p. 16). The paper's extra line `f_i0(u) = 0` is the constant `0`. -/
def utility (I : Instance ι n) (i : ι) (j : Fin n) (u : ℝ) : ℝ :=
  I.v i j * (I.r i j - u)

/-- The objective of the knapsack problem (9) (p. 16) at the 0/1 vector `x_i = 1_S`:
`∑_{j ∈ S} v_ij (r_ij − u)`. -/
def knapsackValue (I : Instance ι n) (i : ι) (u : ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ j ∈ S, utility I i j u

/-- `S` is an optimal solution of the knapsack problem (9) at `u` under the cardinality limit
`c i` (p. 16): `|S| ≤ c_i`, and `S` has the largest objective among all `S'` with `|S'| ≤ c_i`. -/
def IsKnapsackOptimal (I : Instance ι n) (c : ι → ℕ) (i : ι) (u : ℝ) (S : Finset (Fin n)) :
    Prop :=
  S.card ≤ c i ∧ ∀ S' : Finset (Fin n), S'.card ≤ c i → knapsackValue I i u S' ≤ knapsackValue I i u S

/-- `S` is an optimal solution of problem (7) (p. 14) at `u` under the cardinality constraint
`C_i = {S : |S| ≤ c_i}` (p. 8): `S ∈ C_i` and `V_i(S)(R_i(S) − u) ≥ V_i(S')(R_i(S') − u)` for every
`S' ∈ C_i`. -/
def IsOptimal7 (I : Instance ι n) (c : ι → ℕ) (i : ι) (u : ℝ) (S : Finset (Fin n)) : Prop :=
  S.card ≤ c i ∧
    ∀ S' : Finset (Fin n), S'.card ≤ c i → V I i S' * (R I i S' - u) ≤ V I i S * (R I i S - u)

end ConstrNestedLogit.Card


