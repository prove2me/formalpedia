-- Prove2me | Definitions.Def_ConsiderThenChoose_typesOf
-- name    : ConsiderThenChoose_typesOf
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:31:36.879728+00:00
-- url     : https://prove2.me/theorems/589fa33d-9859-40d7-999a-f3da58470214
-- title:
--   The customer types $T(i)$ that consider product $i$
-- statement:
--   For a product $i \in [N]$, let
--
--   $$
--   T(i) = \{ j \in [K] : i \in C_j \}
--   $$
--
--   be the customer types whose consideration sets contain $i$. When the dynamic program stocks product $i$ (the most preferred product of the current subproblem), every type of $T(i)$ buys $i$ and leaves the problem, so the residual subproblem keeps only the types outside $T(i)$.
--
--   **Formalization Note** `typesOf C i` is the `Finset` filter of `Finset.univ : Finset (Fin K)`.
-- source:
--   Aouad, Farias and Levi, Assortment Optimization Under Consider-then-Choose Choice Models, Management Science 67(6) (2021), doi:10.1287/mnsc.2020.3681, §3 "Case 1: Product i is stocked", p. 13

import Mathlib

namespace ConsiderThenChoose

/-- **The types `T(i)` that consider product `i`.** Aouad, Farias and Levi, Management Science
67(6) (2021), doi:10.1287/mnsc.2020.3681, §3 "Case 1: Product i is stocked", unnumbered, p. 13:
"Let T(i) be the customer-types whose consideration sets contain product i."

`typesOf C i = {j ∈ [K] : i ∈ C_j}`. -/
def typesOf {N K : ℕ} (C : Fin K → Finset (Fin N)) (i : Fin N) : Finset (Fin K) :=
  Finset.univ.filter fun j => i ∈ C j

end ConsiderThenChoose


