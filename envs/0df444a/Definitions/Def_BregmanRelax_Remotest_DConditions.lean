-- Prove2me | Definitions.Def_BregmanRelax_Remotest_DConditions
-- name    : BregmanRelax_Remotest_DConditions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T00:52:47.740478+00:00
-- url     : https://prove2.me/theorems/dd3ca3d4-f298-4e1f-aa81-79f8a407c4d5
-- title:
--   The remotest-set control of Theorem 2 (p. 203)
-- statement:
--   Let $(A_i)_{i\in I}$ be a family of subsets of a set $X$ indexed by an arbitrary set $I$, let $D : X\times X\to\mathbb R$ be a function and let $P_i : X\to X$, $i\in I$, be the D-projections of condition II of §1 (the standing conditions I–VI, the relaxation sequence and condition V are the series' shared definitions $\mathrm{DConditions}$, $\mathrm{IsRelaxSeq}$, $\mathrm{CondV}$). A control $(i_n)_{n\ge0}$ is **remotest-set** for a sequence $(x^n)$ when at every step it picks a set that is farthest from $x^n$ in the sense of $D$:
--   $$D(P_jx^n,x^n)\le D(P_{i_n}x^n,x^n)\qquad\text{for all } n \text{ and all } j\in I.$$
--
--   This is the index rule of Theorem 2: $i_n$ realizes $\max_{j\in I}\min_{x\in A_j}D(x,x^n)$.
--
--   **Formalization Note** Theorem 2 maximizes $\min_{x\in A_j}D(x,x^n)$. Since $D$ is defined on $S\times S$ that minimum is over $A_j\cap S$, and by condition II (for $x^n\in S$) it is attained at the D-projection and equals $D(P_jx^n,x^n)$, which is the quantity compared here. The argument order is $D(\text{projection},\text{iterate})$, as in the paper's proof (p. 204).
-- source:
--   Bregman, The relaxation method of finding the common point of convex sets and its application to the solution of problems in convex programming, USSR Comput. Math. Math. Phys. 7(3) (1967), pp. 200–201, conditions I–VI and the iterative process (1)–(2); p. 203, Theorem 2 (the control)

import Mathlib
import Definitions.Def_BregmanRelax_Cyclic_DConditions

namespace BregmanRelax.Remotest

/-- The remotest-set control of Theorem 2 (p. 203): at every step the chosen index `i n`
realizes `max_j min_{z ∈ A j} D z (x n)`. By condition II the inner minimum (over `A j ∩ S`,
where `D` is defined) is attained at the D-projection, so it equals `D (P j (x n)) (x n)`. -/
def IsRemotestControl {X : Type*} {ι : Type*} (D : X → X → ℝ) (P : ι → X → X) (i : ℕ → ι)
    (x : ℕ → X) : Prop :=
  ∀ n, ∀ j, D (P j (x n)) (x n) ≤ D (P (i n) (x n)) (x n)

end BregmanRelax.Remotest


