-- Prove2me | Definitions.Def_WagelmansELS_DualGreedy_Model
-- name    : WagelmansELS_DualGreedy_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:14.815356+00:00
-- url     : https://prove2.me/theorems/1b77533c-ca42-4f62-a08c-a2f959e7fa09
-- title:
--   Section 1 and 4: economic lot-sizing data, D′ and the forward cost F
-- statement:
--   An economic lot-sizing instance has periods $1,\ldots,n$, nonnegative demands $d_t$, nonnegative setup costs $f_i$, and unrestricted real marginal costs $c_i$. Define cumulative demand $d_{i,j}=\sum_{t=i}^j d_t$. The forward cost $F$ starts at $F(0)=0$, skips a zero-demand period, and at a positive-demand period obeys
--
--   $$F(j)=\min_{1\le i\le j}\{f_i+c_i d_{i,j}+F(i-1)\}. $$
--
--   Program D′ has free dual values $v_t$, objective $\sum_{t=1}^n d_tv_t$, and constraints $\sum_{t=i}^n d_t\max\{0,v_t-c_i\}\le f_i$ for every $i=1,\ldots,n$. This module defines its feasibility and prefix objective.
--
--   **Formalization Note** The paper identifies $F(j)$ with the optimal primal lot-sizing cost using the zero-inventory property. That identification and the reduction from Program D to D′ are not formalized here. The zero-demand branch is essential: if $d_1=0$ and $f_1>0$, then $F(1)=0$.
-- source:
--   Wagelmans, Van Hoesel and Kolen, Economic Lot Sizing, Oper. Res. 40 Supp. 1 (1992), pp. S146–S147, Section 1, and pp. S152–S153, Section 4, Program D′ and the paragraph defining F

import Mathlib

namespace WagelmansELS.DualGreedy

/-- The finite-horizon economic lot-sizing data of Section 1. Periods are `1, …, n`.
The nonnegativity assumptions on demand and setup cost are stated at each theorem. -/
structure Instance where
  n : ℕ
  d : ℕ → ℝ
  f : ℕ → ℝ
  c : ℕ → ℝ

/-- Cumulative demand `d_{i,j}`. -/
def demand (P : Instance) (i j : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc i j, P.d t

/-- The objective of Program D′ through period `j`. -/
def objective (P : Instance) (v : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 j, P.d t * v t

/-- The amount used in constraint `i` of Program D′ through period `j`. -/
def constraintUse (P : Instance) (v : ℕ → ℝ) (i j : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc i j, P.d t * max 0 (v t - P.c i)

/-- Feasibility in Program D′, with every constraint summed through `n`. -/
def IsFeasible (P : Instance) (v : ℕ → ℝ) : Prop :=
  ∀ i, 1 ≤ i → i ≤ P.n → constraintUse P v i P.n ≤ P.f i

/-- Cost of using production period `i` for a terminal block through `j`. -/
def blockCost (P : Instance) (F : ℕ → ℝ) (i j : ℕ) : ℝ :=
  P.f i + P.c i * demand P i j + F (i - 1)

/-- The forward zero-inventory recursion for the cost through period `j`.
At a zero-demand period no production is required. Values beyond the horizon are irrelevant. -/
noncomputable def F (P : Instance) (j : ℕ) : ℝ :=
  (Nat.rec (motive := fun _ => ℕ → ℝ) (fun _ => (0 : ℝ)) (fun k hist =>
    fun t => if t = k + 1 then
      if k + 1 ≤ P.n then
        if P.d (k + 1) = 0 then hist k
        else (Finset.Icc 1 (k + 1)).inf' (by
          refine ⟨1, Finset.mem_Icc.mpr ?_⟩
          omega) (fun i => P.f i + P.c i * demand P i (k + 1) + hist (i - 1))
      else 0
    else hist t) j) j

end WagelmansELS.DualGreedy


