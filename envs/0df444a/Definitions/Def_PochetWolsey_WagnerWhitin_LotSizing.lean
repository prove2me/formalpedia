-- Prove2me | Definitions.Def_PochetWolsey_WagnerWhitin_LotSizing
-- name    : PochetWolsey_WagnerWhitin_LotSizing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:26:55.02934+00:00
-- url     : https://prove2.me/theorems/92b38a29-e2bf-4c5a-81ec-5ea99de09a96
-- title:
--   Finite-horizon lot-sizing constraints and stock projection
-- statement:
--   Let $n$ be the number of periods, $d_t$ the real demand in period $t$, and $M$ a finite production bound. A point consists of production $x$, setup $y$, and stock $s$. The set $X^{LS-U}$ is defined by
--   $$x_t\ge0,\quad s_t\ge0,\quad y_t\in\{0,1\},\quad s_{t-1}+x_t=d_t+s_t,\quad x_t\le My_t,\quad s_0=s_n=0.$$
--   Write $d_{ij}=\sum_{t=i}^j d_t$. For production costs $p$ and fixed costs $q$, the objective is $\sum_t p_tx_t+\sum_t q_ty_t$. Projection onto $(x,y)$ means that there exists a stock vector completing the point to the given set.
--
--   These definitions retain the original balance and setup constraints before any hull is taken. Demands and costs are unrestricted in the definitions; each theorem supplies its assumptions.
--
--   **Formalization Note** Periods use `Fin n`, with index $t$ corresponding to printed period $t+1$; stock uses `Fin (n+1)`. Nonnegative production follows the production interpretation and (7.47); the missing plus sign in printed (7.4) is recorded in F1. The objective has already absorbed holding costs, as in (7.7).
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, pp. 208–211 (PDF 222–225), Eqs. (7.2)–(7.7); p. 229 (PDF 243), Eq. (7.47)

import Mathlib

open scoped BigOperators

namespace PochetWolsey.WagnerWhitin

/-- Period t : Fin n denotes printed period t+1. Stock coordinates are 0,...,n. -/
abbrev LSPoint (n : ℕ) := (Fin n → ℝ) × (Fin n → ℝ) × (Fin (n + 1) → ℝ)

noncomputable def demandSum {n : ℕ} (d : Fin n → ℝ) (i j : Fin n) : ℝ :=
  ∑ t ∈ Finset.Icc i j, d t

/-- The production interpretation of (7.4) uses x ≥ 0; see Findings F1. -/
def lsFeasible {n : ℕ} (d : Fin n → ℝ) (M : ℝ) : Set (LSPoint n) :=
  {z | (∀ t, 0 ≤ z.1 t) ∧ (∀ t, 0 ≤ z.2.2 t) ∧
    (∀ t, z.2.1 t = 0 ∨ z.2.1 t = 1) ∧
    (∀ t, z.2.2 t.castSucc + z.1 t = d t + z.2.2 t.succ) ∧
    (∀ t, z.1 t ≤ M * z.2.1 t) ∧
    z.2.2 0 = 0 ∧ z.2.2 (Fin.last n) = 0}

noncomputable def productionCost {n : ℕ} (p q : Fin n → ℝ)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  (∑ t, p t * z.1 t) + ∑ t, q t * z.2 t

/-- Existential elimination of stock, for any set in (x,y,s)-space. -/
def projectXY {n : ℕ} (S : Set (LSPoint n)) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {z | ∃ s : Fin (n + 1) → ℝ, (z.1, z.2, s) ∈ S}

end PochetWolsey.WagnerWhitin


