-- Prove2me | Definitions.Def_ConstrNestedLogit_Scheme_Model
-- name    : ConstrNestedLogit_Scheme_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T20:08:14.409672+00:00
-- url     : https://prove2.me/theorems/7cf90db4-001f-4e44-8d95-649bd571eb76
-- title:
--   Space constraints, problem (10) and the partially fixed knapsack relaxation (17)
-- statement:
--   Fix a nest $i$ of the nested logit model with products $N=\{1,\dots,n\}$, preference weights $v_{ij}$ and revenues $r_{ij}$. Under **space constraints** each product $j$ consumes $w_{ij}$ units of space and the nest has capacity $c_i$; an assortment $S\subseteq N$ is feasible, $S\in\mathcal C_i$, when
--
--   $$
--   \sum_{j\in S} w_{ij}\le c_i .
--   $$
--
--   For a parameter $u$, the **utility** of product $j$ is $h_{ij}(u)=v_{ij}(r_{ij}-u)$, and problem (10) maximizes $\sum_{j\in S} v_{ij}(r_{ij}-u)$ over $S\in\mathcal C_i$.
--
--   For a set $J\subseteq N$, problem (17) is the linear program
--
--   $$
--   \max\Big\{\sum_{j\in N} v_{ij}(r_{ij}-u)\,x_{ij} \;:\; \sum_{j\in N} w_{ij}x_{ij}\le c_i,\ x_{ij}=1\ \forall j\in J,\ 0\le x_{ik}\le \mathbf 1\big(v_{ik}(r_{ik}-u)\le \min_{j\in J} v_{ij}(r_{ij}-u)\big)\ \forall k\in N\setminus J\Big\},
--   $$
--
--   the linear programming relaxation of the knapsack problem (10) after fixing the products of $J$ in the knapsack and removing every product whose utility exceeds the smallest utility in $J$. A point $x\in[0,1]^n$ is feasible for (17) when it meets these constraints and optimal when, in addition, no feasible point has a larger objective. The rounded-down assortment $\lfloor x\rfloor=\{j : x_{ij}=1\}$ is the paper's $S_i^g(J)$, and the fractional components of $x$ are the products with $0<x_{ij}<1$.
--
--   These objects are the building blocks of the approximation scheme of Online Supplement C.
--
--   **Formalization Note** Products are indexed by `Fin n` (from zero) and assortments are finite sets. The indicator constraint is encoded as "$x_{ik}=0$ whenever $v_{ik}(r_{ik}-u)$ strictly exceeds the utility of some product of $J$"; for $J=\emptyset$ the minimum is $+\infty$ and no product is excluded, which this encoding gives automatically. Ties with the minimum are not excluded, as on the page.
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, p. 8 (space constraints), p. 19 (problem (10)), pp. 39–40 (problem (17), S_i^g(J))

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model
import Definitions.Def_ConstrNestedLogit_Space_Model

namespace ConstrNestedLogit.Scheme

variable {ι : Type*} {n : ℕ}

/-- The objective of problem (10) (p. 19): `∑_{j ∈ S} v_ij (r_ij − u)`. -/
def obj10 (I : NestedLogitVariants.LP.Instance ι n) (i : ι) (u : ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ j ∈ S, ConstrNestedLogit.Space.utility I i u j

/-- `x ∈ ℝ^n` is feasible for problem (17) (p. 39) with fixed set `J` at the parameter `u`:
`0 ≤ x_j ≤ 1`, `∑_j w_ij x_ij ≤ c_i`, `x_ij = 1` for `j ∈ J`, and for `k ∉ J`
`x_ik ≤ 1(v_ik (r_ik − u) ≤ min_{j ∈ J} v_ij (r_ij − u))`, i.e. `x_ik = 0` as soon as the
ConstrNestedLogit.Space.utility of `k` strictly exceeds the ConstrNestedLogit.Space.utility of some product of `J` (for `J = ∅` the minimum is
`+∞` and no product is excluded). -/
def feasible17 (I : NestedLogitVariants.LP.Instance ι n) (w : ι → Fin n → ℝ) (c : ι → ℝ)
    (i : ι) (u : ℝ) (J : Finset (Fin n)) (x : Fin n → ℝ) : Prop :=
  (∀ j, 0 ≤ x j ∧ x j ≤ 1) ∧
  (∑ j, w i j * x j) ≤ c i ∧
  (∀ j ∈ J, x j = 1) ∧
  ∀ k, k ∉ J → (∃ j ∈ J, ConstrNestedLogit.Space.utility I i u j < ConstrNestedLogit.Space.utility I i u k) → x k = 0

/-- The objective of problem (17): `∑_j v_ij (r_ij − u) x_ij`. -/
def obj17 (I : NestedLogitVariants.LP.Instance ι n) (i : ι) (u : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ j, ConstrNestedLogit.Space.utility I i u j * x j

/-- `x` is an optimal solution of problem (17): feasible, and no feasible point has a larger
objective value. -/
def optimal17 (I : NestedLogitVariants.LP.Instance ι n) (w : ι → Fin n → ℝ) (c : ι → ℝ)
    (i : ι) (u : ℝ) (J : Finset (Fin n)) (x : Fin n → ℝ) : Prop :=
  feasible17 I w c i u J x ∧ ∀ y, feasible17 I w c i u J y → obj17 I i u y ≤ obj17 I i u x

/-- The products at value one, `S_i^g(J) = ⌊x_i^g(J)⌋` (p. 40) for `x ∈ [0,1]^n`. -/
noncomputable def roundDown (x : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => x j = 1)

/-- The fractional components of `x`: the products with `0 < x_j < 1`. -/
noncomputable def fractional (x : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => 0 < x j ∧ x j < 1)

end ConstrNestedLogit.Scheme


