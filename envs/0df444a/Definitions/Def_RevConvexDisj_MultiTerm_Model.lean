-- Prove2me | Definitions.Def_RevConvexDisj_MultiTerm_Model
-- name    : RevConvexDisj_MultiTerm_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:15:08.560689+00:00
-- url     : https://prove2.me/theorems/a0e829ed-8b03-4018-9a4b-172d52bc075a
-- title:
--   §2–§4.3, (2), (7), (26), (27) — basis cone P^B, extreme rays, recession cone, α_j, β_j, N0/N1/N2, segments, T^C, S^C_0, S^C_k
-- statement:
--   This file fixes the setting of Towle and Luedtke's study of intersection disjunctions for reverse convex sets.
--
--   **The linear program and the basis (§2, p. 4).** Let $A \in \mathbb{R}^{m\times n}$ have full row rank and let $b\in\mathbb{R}^m$; the variables are indexed by a finite set $\iota$ playing the role of $\{1,\dots,n\}$. A basis is given by a partition $\iota = B \sqcup N$ into basic and nonbasic variables, a tableau $\bar a = (\bar a_{ij})$ and a basic solution $\bar x$ with $\bar x_j = 0$ for $j\in N$, such that
--   $$Ax = b \iff x_i = \bar x_i - \sum_{j\in N}\bar a_{ij}x_j \quad (i \in B).$$
--   Removing the nonnegativity constraints of the basic variables gives the **basis cone**
--   $$P^B = \Big\{x : x_i = \bar x_i - \sum_{j\in N}\bar a_{ij}x_j,\ i\in B,\quad x_j \ge 0,\ j\in N\Big\},$$
--   a translated simplicial cone with apex $\bar x$ and extreme rays $\bar r^j$ ($j\in N$), where $\bar r^j_k = -\bar a_{kj}$ for $k\in B$, $\bar r^j_j = 1$ and $\bar r^j_k = 0$ for $k\in N\setminus\{j\}$.
--
--   **The convex set.** For $C\subseteq\mathbb{R}^n$, its **recession cone** is $\operatorname{recc}(C) = \{d : x + t d\in C \text{ for all } x\in C,\ t\ge 0\}$. For each $j\in N$,
--   $$\alpha_j := \inf\{\alpha\ge 0 : \bar x + \alpha\bar r^j\in C\},\qquad \beta_j := \sup\{\beta\ge 0 : \bar x + \beta\bar r^j\in C\},$$
--   taken in the extended reals $\bar{\mathbb{R}}$, with $\alpha_j = +\infty$, $\beta_j = -\infty$ when the halfline $\{\bar x\} + [0,+\infty)\bar r^j$ misses $C$. The nonbasic indices split as
--   $$N_0 = \{j : \alpha_j = +\infty,\ \beta_j = -\infty\},\quad N_1 = \{j : \alpha_j\in(0,+\infty),\ \beta_j = +\infty\},\quad N_2 = \{j : \alpha_j\in(0,+\infty),\ \beta_j\in(\alpha_j,+\infty)\},$$
--   and $N_0^{\mathrm c} := N_1\cup N_2$.
--
--   **Segments and the sets of §4.** For $\alpha,\beta\in\bar{\mathbb{R}}$ and a vector $r$, $(\alpha,\beta)r := \{\lambda r : \lambda\in\mathbb{R},\ \alpha<\lambda<\beta\}$, and similarly $[0,\beta)r$ and $(-\infty,0]r$. With Minkowski sums and convex hulls,
--   $$T := \{\bar x\} + \operatorname{conv}\Big(\bigcup_{j\in N_0^{\mathrm c}}(\alpha_j,\beta_j)\bar r^j\Big),\qquad T^C := T + \operatorname{recc}(C) \quad (7),$$
--   $$S^C_0 := \{\bar x\} + \operatorname{conv}\Big(\bigcup_{j\in N_0^{\mathrm c}}(\alpha_j,+\infty)\bar r^j\Big) + \operatorname{recc}(C)\quad (26),$$
--   $$S^C_k := \{\bar x\} + \operatorname{conv}\Big(\bigcup_{j\in N_2}[0,\beta_j)\bar r^j\Big) + (-\infty,0]\bar r^k + \operatorname{recc}(C)\quad (k\in N_2)\quad (27).$$
--
--   $T^C$ is an inner approximation of $C$ built from the recession cone, and the sets $S^C_0$, $S^C_k$ are the terms of the paper's multi-term disjunction for $P^B\setminus T^C$.
--
--   **Formalization Note.** Vectors are functions $\iota\to\mathbb{R}$. The basis is the published `Disjunctive.GeneralDisjunctions.IsTableau`, and $\bar r^j$ is the published `Disjunctive.GeneralDisjunctions.extremeRay`. The paper's §2 also writes $\bar b\in\mathbb{R}^{|B|}_+$ (a feasible basic solution); this is not imposed, since the paper's own Example 2 uses an infeasible basic solution and none of the results formalized here use it, so the definitions cover every basic solution. $\alpha_j,\beta_j$ are `EReal`-valued infimum/supremum of real parameter sets, so the empty set gives exactly $+\infty$/$-\infty$ and an unbounded set gives $\beta_j = +\infty$; segment parameters $\lambda$ are real numbers compared with extended-real endpoints. Under the universal definition, $\operatorname{recc}(\emptyset)$ is the whole space; this is harmless, since for $C=\emptyset$ all of $N_0^{\mathrm c}$, $T$, $S^C_0$ are empty and $N_2=\emptyset$.
-- source:
--   Towle & Luedtke, Intersection disjunctions for reverse convex sets, arXiv:1901.02112v5, p. 4, §2 and (2); p. 5, §3 (α_j, N0, N1, N2); p. 9, (7); p. 17, (26)–(27)

import Mathlib
import Definitions.Def_Disjunctive_GeneralDisjunctions_Basic
import Definitions.Def_Disjunctive_GeneralDisjunctions_SIC

namespace RevConvexDisj.MultiTerm

open scoped Pointwise

/-- §2, p. 4: the LP data `A ∈ ℝ^{m×n}` of full row rank and `b ∈ ℝ^m`, a basis `B` with nonbasic
set `N = {1,…,n} \ B`, its tableau `ā` and basic solution `x̄`. The basis is a genuine tableau of
`Ax = b` (the published `Disjunctive.GeneralDisjunctions.IsTableau`). The basic solution is not
required to be feasible (`x̄ ≥ 0` is not imposed). -/
structure BasisData (ι : Type*) [Fintype ι] [DecidableEq ι] where
  m : ℕ
  A : Matrix (Fin m) ι ℝ
  b : Fin m → ℝ
  B : Finset ι
  N : Finset ι
  abar : ι → ι → ℝ
  xbar : ι → ℝ
  fullRowRank : A.rank = m
  isTableau : Disjunctive.GeneralDisjunctions.IsTableau A b B N abar xbar

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The extreme ray `r̄^j` of `P^B` (p. 4): `r̄^j_k = -ā_kj` for `k ∈ B`, `1` for `k = j`,
`0` for `k ∈ N \ {j}` (the published `Disjunctive.GeneralDisjunctions.extremeRay`). -/
def BasisData.ray (D : BasisData ι) (j : ι) : ι → ℝ :=
  Disjunctive.GeneralDisjunctions.extremeRay D.B D.abar j

/-- `P^B` (p. 4): the tableau form of `P` with the nonnegativity constraints on the basic
variables `x_i`, `i ∈ B`, removed. -/
def BasisData.PB (D : BasisData ι) : Set (ι → ℝ) :=
  {x | (∀ i ∈ D.B, x i = D.xbar i - ∑ j ∈ D.N, D.abar i j * x j) ∧ ∀ j ∈ D.N, 0 ≤ x j}

/-- The recession cone `recc(C) = {d : x + t d ∈ C for all x ∈ C, t ≥ 0}`. -/
def recc (C : Set (ι → ℝ)) : Set (ι → ℝ) :=
  {d | ∀ x ∈ C, ∀ t : ℝ, 0 ≤ t → x + t • d ∈ C}

/-- `α_j := inf{α ≥ 0 : x̄ + α r̄^j ∈ C}` (p. 5), in the extended reals; the infimum of the empty
set is `+∞`, the paper's convention. -/
noncomputable def alpha (D : BasisData ι) (C : Set (ι → ℝ)) (j : ι) : EReal :=
  sInf ((fun t : ℝ => (t : EReal)) '' {t : ℝ | 0 ≤ t ∧ D.xbar + t • D.ray j ∈ C})

/-- `β_j := sup{β ≥ 0 : x̄ + β r̄^j ∈ C}` ((2), p. 4), in the extended reals; the supremum of the
empty set is `-∞` (the paper's convention) and of an unbounded set `+∞`. -/
noncomputable def beta (D : BasisData ι) (C : Set (ι → ℝ)) (j : ι) : EReal :=
  sSup ((fun t : ℝ => (t : EReal)) '' {t : ℝ | 0 ≤ t ∧ D.xbar + t • D.ray j ∈ C})

open Classical in
/-- `N0 := {j ∈ N : α_j = +∞, β_j = -∞}` (p. 5). -/
noncomputable def N0 (D : BasisData ι) (C : Set (ι → ℝ)) : Finset ι :=
  D.N.filter fun j => alpha D C j = ⊤ ∧ beta D C j = ⊥

open Classical in
/-- `N1 := {j ∈ N : α_j ∈ (0, +∞), β_j = +∞}` (p. 5). -/
noncomputable def N1 (D : BasisData ι) (C : Set (ι → ℝ)) : Finset ι :=
  D.N.filter fun j => 0 < alpha D C j ∧ alpha D C j < ⊤ ∧ beta D C j = ⊤

open Classical in
/-- `N2 := {j ∈ N : α_j ∈ (0, +∞), β_j ∈ (α_j, +∞)}` (p. 5). -/
noncomputable def N2 (D : BasisData ι) (C : Set (ι → ℝ)) : Finset ι :=
  D.N.filter fun j =>
    0 < alpha D C j ∧ alpha D C j < ⊤ ∧ alpha D C j < beta D C j ∧ beta D C j < ⊤

/-- `N^c_0 := N1 ∪ N2` (p. 9). -/
noncomputable def N0c (D : BasisData ι) (C : Set (ι → ℝ)) : Finset ι :=
  N1 D C ∪ N2 D C

/-- The segment `(α, β)r := {λ r : λ ∈ (α, β)}` (p. 4), `α, β ∈ ℝ̄`, `λ` real. -/
def openSeg (a b : EReal) (r : ι → ℝ) : Set (ι → ℝ) :=
  {v | ∃ t : ℝ, a < (t : EReal) ∧ (t : EReal) < b ∧ v = t • r}

/-- The segment `[0, β)r := {λ r : λ ∈ [0, β)}` (p. 4), `β ∈ ℝ̄`, `λ` real. -/
def icoSeg (b : EReal) (r : ι → ℝ) : Set (ι → ℝ) :=
  {v | ∃ t : ℝ, 0 ≤ t ∧ (t : EReal) < b ∧ v = t • r}

/-- The halfline `(-∞, 0]r := {λ r : λ ≤ 0}` (p. 4). -/
def nonposRay (r : ι → ℝ) : Set (ι → ℝ) :=
  {v | ∃ t : ℝ, t ≤ 0 ∧ v = t • r}

/-- `T := {x̄} + conv(⋃_{j ∈ N^c_0} (α_j, β_j) r̄^j)` ((7), p. 9). -/
noncomputable def T (D : BasisData ι) (C : Set (ι → ℝ)) : Set (ι → ℝ) :=
  {D.xbar} + convexHull ℝ (⋃ j ∈ N0c D C, openSeg (alpha D C j) (beta D C j) (D.ray j))

/-- `T^C := T + recc(C)` ((7), p. 9). -/
noncomputable def TC (D : BasisData ι) (C : Set (ι → ℝ)) : Set (ι → ℝ) :=
  T D C + recc C

/-- `S^C_0 := {x̄} + conv(⋃_{j ∈ N^c_0} (α_j, +∞) r̄^j) + recc(C)` ((26), p. 17). -/
noncomputable def SC0 (D : BasisData ι) (C : Set (ι → ℝ)) : Set (ι → ℝ) :=
  {D.xbar} + convexHull ℝ (⋃ j ∈ N0c D C, openSeg (alpha D C j) ⊤ (D.ray j)) + recc C

/-- `S^C_k := {x̄} + conv(⋃_{j ∈ N2} [0, β_j) r̄^j) + (-∞, 0] r̄^k + recc(C)` ((27), p. 17),
used for `k ∈ N2`. -/
noncomputable def SCk (D : BasisData ι) (C : Set (ι → ℝ)) (k : ι) : Set (ι → ℝ) :=
  {D.xbar} + convexHull ℝ (⋃ j ∈ N2 D C, icoSeg (beta D C j) (D.ray j))
    + nonposRay (D.ray k) + recc C

end RevConvexDisj.MultiTerm


