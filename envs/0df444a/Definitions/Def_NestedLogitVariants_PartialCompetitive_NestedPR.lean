-- Prove2me | Definitions.Def_NestedLogitVariants_PartialCompetitive_NestedPR
-- name    : NestedLogitVariants_PartialCompetitive_NestedPR
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T07:46:18.974908+00:00
-- url     : https://prove2.me/theorems/951c32b1-5021-4415-bde4-85cfb6653603
-- title:
--   §5, pp. 24–25 — N^k_ij, the first j products by revenue among the k products of smallest preference weight
-- statement:
--   Fix a nest $i$. Order the products of the nest by preference weight, breaking ties by index: $l$ precedes $j$ when $v_{il} < v_{ij}$, or $v_{il} = v_{ij}$ and $l < j$. For $k \in \{0, 1, \dots, n\}$ let the **$k$ products with the smallest preference weights** be the first $k$ products in this order. Among them, ordered by revenue (that is, by index, since $r_{i1} \ge r_{i2} \ge \dots \ge r_{in}$), let
--
--   $$N^k_{ij} = \text{the first } j \text{ of these } k \text{ products}, \qquad N^k_{i0} = \emptyset.$$
--
--   These are the nested-by-revenue assortments restricted to the light products; §5 shows that every greedy assortment $\hat S_i(\epsilon_i)$ is one of them, which bounds the candidate collection by $1 + n^2$ assortments.
--
--   **Formalization Note** Ties in preference weight are broken by index (lexicographic order of $(v_{ij}, j)$), ties in revenue by index. With $k = n$ the assortment $N^n_{ij}$ is the ordinary nested-by-revenue assortment $N_{ij}$.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), pp. 24–25, §5, definition of N^k_ij

import Mathlib
import Definitions.Def_NestedLogitVariants_PartialCompetitive_Model

namespace NestedLogitVariants.PartialCompetitive

open Classical

variable {ι : Type*} {n : ℕ}

/-- `(v_il, l)` precedes `(v_ij, j)` lexicographically. -/
def weightLt (I : Instance ι n) (i : ι) (l j : Fin n) : Prop :=
  I.v i l < I.v i j ∨ (I.v i l = I.v i j ∧ l < j)

/-- The products with the `k` smallest preference weights in nest `i`. -/
noncomputable def smallK (I : Instance ι n) (i : ι) (k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => (Finset.univ.filter (fun l => weightLt I i l j)).card < k)

/-- `N^k_ij`: the first `j` products (index = revenue order) among `smallK I i k`. -/
noncomputable def nestedPR (I : Instance ι n) (i : ι) (k j : ℕ) : Finset (Fin n) :=
  (smallK I i k).filter (fun l => ((smallK I i k).filter (fun l' => l' < l)).card < j)

end NestedLogitVariants.PartialCompetitive


