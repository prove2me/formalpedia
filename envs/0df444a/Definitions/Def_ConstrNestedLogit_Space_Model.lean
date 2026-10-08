-- Prove2me | Definitions.Def_ConstrNestedLogit_Space_Model
-- name    : ConstrNestedLogit_Space_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T19:03:56.092303+00:00
-- url     : https://prove2.me/theorems/685707a5-7218-44a3-8a12-fbc88bcedade
-- title:
--   Space-constrained assortments, problem (10), its LP relaxation and rounded candidate families
-- statement:
--   This module fixes the objects of problem (7) under space constraints (Gallego and Topaloglu, §1 and §5.1).
--
--   Fix a nest $i$ of the nested logit model with products $N=\{1,\dots,n\}$, preference weights $v_{ij}$ and revenues $r_{ij}$. Under **space constraints** product $j$ consumes $w_{ij}$ units of space and the nest has capacity $c_i$, so an assortment $S\subseteq N$ is feasible, $S\in\mathcal C_i$, when
--
--   $$
--   \sum_{j\in S} w_{ij}\le c_i .
--   $$
--
--   For a parameter $u\ge 0$ the **utility** of product $j$ is $v_{ij}(r_{ij}-u)$, and problem (7) is written as the 0–1 knapsack problem (10),
--
--   $$
--   \max\Big\{\sum_{j\in N} v_{ij}(r_{ij}-u)\,x_{ij} \;:\; \sum_{j\in N} w_{ij}x_{ij}\le c_i,\ x_{ij}\in\{0,1\}\ \forall j\in N\Big\}.
--   $$
--
--   The module defines:
--
--   1. the knapsack objective $\sum_{j\in S} v_{ij}(r_{ij}-u)$ of an assortment $S$;
--   2. the **utility to space consumption ratio** $f_{ij}(u)=v_{ij}(r_{ij}-u)/w_{ij}$;
--   3. optimality of a vector $x\in[0,1]^n$ for the linear programming relaxation of (10), in which $x_{ij}\in\{0,1\}$ is replaced by $0\le x_{ij}\le 1$;
--   4. the **rounded-down assortment** of such an $x$, with $S_{ij}=\lfloor x_{ij}\rfloor$, i.e. the products with $x_{ij}=1$;
--   5. the predicates "$x_{j}$ is the only fractional component of $x$" and "$x$ has at most one fractional component";
--   6. **rounded candidate families**: a finite family $A$ of assortments that contains the empty assortment and every singleton $\{j\}$, and each of whose members is either a singleton or the rounded-down assortment of an optimal solution of the relaxation, at some $u\ge 0$, with at most one fractional component. This describes the collection $\{S_i^g : g\in\mathcal G_i\}\cup\{\{j\}:j\in N\}$ of p. 20 by its members;
--   7. **$\alpha$-approximate solutions** to problem (7) at $u$, in the form of (5): $S\in\mathcal C_i$ and
--   $$
--   \alpha\, V_i(S)\big(R_i(S)-u\big)\ \ge\ V_i(T)\big(R_i(T)-u\big)\quad\text{for every } T\in\mathcal C_i .
--   $$
--
--   These are the shared vocabulary of the space-constrained results of the paper: the factor-two guarantee (Theorem 6) and its refinement by the factor $1/(1-\epsilon)$, and the approximation scheme of Supplement C.
--
--   **Formalization Note** Products are indexed by `Fin n` (0-based) and nests by an arbitrary type; an assortment is a `Finset (Fin n)` and the empty assortment $\bar 0$ is `∅`. $V_i$ and $R_i$ come from the published `NestedLogitVariants.LP.Model`, whose $V_i(S)=v_{i0}+\sum_{j\in S}v_{ij}$ carries a within-nest no-purchase weight; the theorems that use this module set $v_{i0}=0$, which gives the paper's $V_i$ and, by (8), makes the objective of (7) equal to the knapsack objective above. The ratio $f_{ij}(u)$ is the paper's only when $w_{ij}>0$ (Lean's $x/0=0$); the theorems assume $w_{ij}>0$ and the paper's $w_{ij}\le c_i$. The empty assortment is required in a candidate family explicitly; in the paper it is the rounding $S_i^g=\bar 0$ of the relaxation's optimum $x_i^g=0$ on the last interval, where every utility is negative.
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, p. 8 (space constraints C_i), p. 13 (5), p. 19 (10) and f_ij(u), p. 20 (x_i^g, S_i^g, j^g, the collection {S_i^g} ∪ {{j}})

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model
import Definitions.Def_ConstrNestedLogit_Space_KnapsackLP

namespace ConstrNestedLogit.Space

variable {ι : Type*} {n : ℕ}

/-- Space feasibility in nest `i` (p. 8): `S ∈ C_i` iff `∑_{j ∈ S} w_ij ≤ c_i`. -/
def spaceFeasible (w : ι → Fin n → ℝ) (c : ι → ℝ) (i : ι)
    (S : Finset (Fin n)) : Prop :=
  (∑ j ∈ S, w i j) ≤ c i

/-- Product utility in (10) at the parameter `u`. -/
def utility (I : NestedLogitVariants.LP.Instance ι n) (i : ι) (u : ℝ) (j : Fin n) : ℝ :=
  I.v i j * (I.r i j - u)

/-- The utility per unit of space, `f_ij(u) = v_ij (r_ij − u) / w_ij` on p. 19. It is the paper's
ratio only when `w_ij > 0`, which the theorems assume (`x / 0 = 0` in Lean). -/
noncomputable def utilityRatio (I : NestedLogitVariants.LP.Instance ι n)
    (w : ι → Fin n → ℝ) (i : ι) (u : ℝ) (j : Fin n) : ℝ :=
  utility I i u j / w i j

/-- Objective of the integer knapsack (10), equal to (7) when `vnp = 0`. -/
def assortmentUtility (I : NestedLogitVariants.LP.Instance ι n) (i : ι) (u : ℝ)
    (S : Finset (Fin n)) : ℝ :=
  ∑ j ∈ S, utility I i u j

/-- `x ∈ [0,1]^n` is an optimal solution of the linear programming relaxation of (10) at `u`. -/
def spaceLPOptimal (I : NestedLogitVariants.LP.Instance ι n)
    (w : ι → Fin n → ℝ) (c : ι → ℝ) (i : ι) (u : ℝ) (x : Fin n → ℝ) : Prop :=
  knapsackLPOptimal (w i) (utility I i u) (c i) x

/-- The assortment obtained by rounding the LP solution down, `S_ij = ⌊x_ij⌋` (p. 20); for
`x ∈ [0,1]^n` this is the set of products with `x_j = 1`. -/
noncomputable def rounded (x : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => x j = 1)

/-- `x_j` is the fractional component `j^g` of `x` (p. 20), and every other component is `0` or `1`. -/
def oneFractional (x : Fin n → ℝ) (j : Fin n) : Prop :=
  0 < x j ∧ x j < 1 ∧ ∀ k, k ≠ j → x k = 0 ∨ x k = 1

/-- At most one component lies strictly between zero and one. -/
def atMostOneFractional (x : Fin n → ℝ) : Prop :=
  ∀ j k, 0 < x j → x j < 1 → 0 < x k → x k < 1 → j = k

/-- The candidate family `{S_i^g : g ∈ G_i} ∪ {{j} : j ∈ N}` of p. 20, described by its members:
it contains the empty assortment (the rounding of the LP optimum `x = 0` for large `u`) and every
singleton, and each member is a singleton or the rounding of an optimal solution of the LP
relaxation of (10) with at most one fractional component, at some `u ≥ 0`. -/
def isRoundedCandidateFamily (I : NestedLogitVariants.LP.Instance ι n)
    (w : ι → Fin n → ℝ) (c : ι → ℝ) (i : ι)
    (A : Finset (Finset (Fin n))) : Prop :=
  (∅ ∈ A) ∧ (∀ j, ({j} : Finset (Fin n)) ∈ A) ∧
  ∀ S ∈ A, (∃ j, S = {j}) ∨
    ∃ u : ℝ, 0 ≤ u ∧ ∃ x : Fin n → ℝ,
      spaceLPOptimal I w c i u x ∧ atMostOneFractional x ∧ S = rounded x

/-- `S` is an `α`-approximate solution to problem (7) at `u` under space constraints, in the form
of (5) (p. 13): `S ∈ C_i` and `α · V_i(S)(R_i(S) − u) ≥ V_i(T)(R_i(T) − u)` for every `T ∈ C_i`. -/
def isApproximateAt (I : NestedLogitVariants.LP.Instance ι n)
    (w : ι → Fin n → ℝ) (c : ι → ℝ) (i : ι) (u α : ℝ)
    (S : Finset (Fin n)) : Prop :=
  spaceFeasible w c i S ∧
    ∀ T, spaceFeasible w c i T →
      NestedLogitVariants.LP.V I i T * (NestedLogitVariants.LP.R I i T - u) ≤
        α * (NestedLogitVariants.LP.V I i S * (NestedLogitVariants.LP.R I i S - u))

end ConstrNestedLogit.Space


