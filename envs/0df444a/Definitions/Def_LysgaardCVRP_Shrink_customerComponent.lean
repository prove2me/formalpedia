-- Prove2me | Definitions.Def_LysgaardCVRP_Shrink_customerComponent
-- name    : LysgaardCVRP_Shrink_customerComponent
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T16:43:15.236396+00:00
-- url     : https://prove2.me/theorems/64e58920-e570-4420-8ea2-87327fa4f40c
-- title:
--   Support graph $G^*_c$, its connected components, and the components detached from the depot
-- statement:
--   For an edge vector $x$, the **support graph** is $G^* = (V, E^*)$ with $E^* = \{e \in E : x_e > 0\}$, and $G^*_c = (V_c, E^*_c)$ is obtained from $G^*$ by removing the depot. This file defines
--
--   1. $G^*_c$: distinct customers $i, j$ are adjacent iff $x_{ij} > 0$;
--   2. for a customer $i$, the connected component $S(i)$ of $G^*_c$ containing $i$, as a set of customers;
--   3. the union $U$ of those components of $G^*_c$ that are not connected to the depot in $G^*$, i.e. the customers $j$ such that $x_{0v} = 0$ for every $v \in S(j)$.
--
--   These are the sets the connected components separation heuristic checks: $S_1, \dots, S_p$, their complements $V_c \setminus S_i$, and $U$.
--
--   **Formalization Note** The graph is built on all vertices with the depot isolated, which is the same as removing it. Positivity is used for adjacency, so values of $x$ on diagonal pairs play no role.
-- source:
--   Lysgaard, Letchford & Eglese, A new branch-and-cut algorithm for the capacitated vehicle routing problem, Math. Program. Ser. A 100 (2004), pp. 425–426 (PDF pp. 3–4), §2 (support graph) and §2.1 (connected components heuristic)

import Mathlib

namespace LysgaardCVRP.Shrink

/-- The support graph $G^*_c = (V_c, E^*_c)$ on the customers (Lysgaard, Letchford & Eglese, Math.
Program. Ser. A 100 (2004), §2, pp. 425–426, PDF pp. 3–4): $E^* = \{e \in E : x^*_e > 0\}$, and
$G^*_c$ is obtained from $G^* = (V, E^*)$ by removing the depot.

**Formalization Note.** The graph lives on all of `Fin (n+1)`; the depot `0` is made an isolated
vertex, which is the same as removing it. Two distinct customers $i \ne j$ are adjacent iff
$x_{ij} > 0$ (`SimpleGraph.fromRel` adds `i ≠ j` and symmetrizes; `x s(i, j) = x s(j, i)` anyway). -/
def customerSupportGraph {n : ℕ} (x : Sym2 (Fin (n + 1)) → ℝ) : SimpleGraph (Fin (n + 1)) :=
  SimpleGraph.fromRel (fun i j => i ≠ 0 ∧ j ≠ 0 ∧ 0 < x s(i, j))

open Classical in
/-- The connected component of $G^*_c$ containing the customer $i$, as a customer set: the
customers $j$ reachable from $i$ in $G^*_c$ (Lysgaard, Letchford & Eglese, §2.1, p. 426, PDF p. 4,
"the connected components $S_1, \dots, S_p$ of $G^*_c$").

**Formalization Note.** The components $S_1, \dots, S_p$ are exactly the sets
`customerComponent x i` for customers `i ≠ 0`. -/
noncomputable def customerComponent {n : ℕ} (x : Sym2 (Fin (n + 1)) → ℝ) (i : Fin (n + 1)) :
    Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun j => j ≠ 0 ∧ (customerSupportGraph x).Reachable i j)

open Classical in
/-- The union of those components of $G^*_c$ which are not connected to the depot in $G^*$
(Lysgaard, Letchford & Eglese, §2.1, p. 426, PDF p. 4): the customers $j$ such that no customer
$v$ of the component of $j$ has $x^*_{0v} > 0$. -/
noncomputable def detachedUnion {n : ℕ} (x : Sym2 (Fin (n + 1)) → ℝ) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun j => j ≠ 0 ∧ ∀ v ∈ customerComponent x j, ¬ 0 < x s(0, v))

end LysgaardCVRP.Shrink


