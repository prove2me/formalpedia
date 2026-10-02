-- Prove2me | Definitions.Def_Disjunctive_IntroDuality_IntersectionCut
-- name    : Disjunctive_IntroDuality_IntersectionCut
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T16:01:57.667873+00:00
-- url     : https://prove2.me/theorems/5e32fd2b-2c2b-42c3-8e0f-06368de380de
-- title:
--   The extreme rays of the LP cone $C(J)$ and $P_I$-free convex sets
-- statement:
--   This definition sets up the two objects Theorem 1.1 (the intersection cut) is built from.
--
--   Fix a finite index set $\iota$ (the structural and surplus variables of the LP relaxation
--   together), a basic index set $I \subseteq \iota$, and the optimal simplex tableau's
--   coefficients $\bar a_{ij}$ for $i \in I$. For a nonbasic index $j$, the **extreme ray**
--   direction of the LP cone $C(J)$ associated with $j$ is the vector $r^j \in \mathbb{R}^\iota$
--   with
--
--   $$
--   r^j_i = \begin{cases} -\bar a_{ij}, & i \in I, \\ 1, & i = j, \\ 0, & i \notin I \cup \{j\}. \end{cases}
--   $$
--
--   A convex set $S \subseteq \mathbb{R}^\iota$ is **$P_I$-free** at a point $\bar x$ if $\bar x$
--   lies in the interior of $S$, and the interior of $S$ contains no point of $P_I$ (the mixed-
--   integer feasible set). $P_I$-free sets are exactly the sets from which an intersection cut can
--   be generated: cutting off $\mathrm{int}(S)$ removes no feasible integer point.
--
--   **Formalization Note.** `extremeRay` returns the ray's *direction* vector; the ray itself,
--   as used in Theorem 1.1, is the set of points $\bar x + \lambda_j \cdot r^j$ for $\lambda_j \ge 0$.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 3-4, Section 1.2

import Mathlib

namespace Disjunctive.IntroDuality

/-- The extreme-ray direction `r^j` of the LP cone `C(J)` at a basic solution with basic index
set `I` and tableau coefficients `ā` (Balas §1.2, p. 3): for `i ∈ I`, `r^j_i = -ā_{ij}`;
`r^j_j = 1`; and `r^j_i = 0` for `i ∈ J \ {j}`. -/
def extremeRay {ι : Type*} [DecidableEq ι] (I : Finset ι) (abar : ι → ι → ℝ) (j : ι) : ι → ℝ :=
  fun i => if i = j then 1 else if i ∈ I then -abar i j else 0

/-- A convex set `S` is `P_I`-free at `x̄` (Balas §1.2, p. 4): `x̄ ∈ int S` and `int S` contains
no point of `P_I`. -/
def PIFree {ι : Type*} [Fintype ι] (S : Set (ι → ℝ)) (PI : Set (ι → ℝ)) (xbar : ι → ℝ) : Prop :=
  Convex ℝ S ∧ xbar ∈ interior S ∧ interior S ∩ PI = ∅

end Disjunctive.IntroDuality


