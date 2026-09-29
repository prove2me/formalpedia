-- Prove2me | Definitions.Def_AKSSorting_Core_compareExchange
-- name    : AKSSorting_Core_compareExchange
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T09:34:37.773964+00:00
-- url     : https://prove2.me/theorems/b0a4e4d2-006d-450f-9be9-6ad2acfd7057
-- title:
--   Compare-exchange: the elementary step that puts the minimum in the first register
-- statement:
--   Let $\mathcal R$ be a set of registers and let $x:\mathcal R\to L$ assign to every register a content from a linearly ordered set $L$. For two registers $i, j$, the **compare-exchange** step $\operatorname{ce}_{i,j}$ compares the contents of $i$ and $j$ and exchanges them if the content of $i$ is greater than the content of $j$. The resulting assignment is
--
--   $$
--   \operatorname{ce}_{i,j}(x)(r)=\begin{cases}\min(x_i,x_j) & r=i,\\ \max(x_i,x_j) & r=j,\\ x_r & \text{otherwise.}\end{cases}
--   $$
--
--   This is the elementary step of Ajtai, Komlós and Szemerédi (Section 1, and Definition 3.2: "if the content of $R_1$ is greater than the content of $R_2$ then exchange the contents of these registers, otherwise leave them unchanged"). It is the building block of comparator networks and of the expander-based halving steps.
--
--   **Formalization Note** The contents are a function $x : R \to \alpha$ into an arbitrary linearly ordered type; the step is written with two `Function.update`s. The ordered pair $(i,j)$ fixes the direction: the minimum goes to $i$, the maximum to $j$.
-- source:
--   Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983), p. 1, Section 1; p. 6, Definition 3.2

import Mathlib

namespace AKSSorting.Core

/-- The elementary step "compare registers `i` and `j`; if the content of `i` is greater than the
content of `j`, exchange them" (Ajtai–Komlós–Szemerédi 1983, §1 p. 1 and Definition 3.2 p. 6).
Afterwards register `i` holds the minimum and register `j` the maximum of the two contents; all
other registers are unchanged. -/
def compareExchange {R : Type} [DecidableEq R] {α : Type} [LinearOrder α] (i j : R) (x : R → α) :
    R → α :=
  Function.update (Function.update x i (min (x i) (x j))) j (max (x i) (x j))

end AKSSorting.Core


