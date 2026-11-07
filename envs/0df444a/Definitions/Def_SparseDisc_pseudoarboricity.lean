-- Prove2me | Definitions.Def_SparseDisc_pseudoarboricity
-- name    : SparseDisc_pseudoarboricity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:50:01.971935+00:00
-- url     : https://prove2.me/theorems/932f83fa-3b61-4ed3-aa8d-fcfc37b7b76e
-- title:
--   Pseudoarboricity $p(H)$
-- statement:
--   The **pseudoarboricity** of a finite graph $H$ is
--   $$
--   p(H) = \max_{H'} \left\lceil \frac{|E(H')|}{|V(H')|} \right\rceil ,
--   $$
--   the maximum over the nonempty subgraphs $H'$ of $H$. By Hakimi's theorem it is the least $k$ such that $H$ has an orientation with every in-degree at most $k$.
--
--   **Formalization Note** The maximum is taken over nonempty vertex sets $W$ of the number of edges of $H$ with both ends in $W$ (the published `TaitTobin.Outerplanar.eIn`), i.e. over induced subgraphs; for a fixed vertex set the induced subgraph has the most edges, so the maxima agree. The ceiling is the natural-number quotient $(e + |W| - 1) / |W|$. On the empty graph the value is $0$.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Theorem 1.9, p.4; Theorem 8.32, p.43

import Mathlib
import Definitions.Def_TaitTobin_Outerplanar_Setting

namespace SparseDisc

open Classical in
/-- The **pseudoarboricity** `p(H) = max_{H'} ⌈|E(H')| / |V(H')|⌉` over the nonempty subgraphs `H'`
of `H` (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC 2027
submission manuscript (sha256 0f09ec60…25b81), Theorem 1.9, p.4, and Theorem 8.32, p.43).

**Formalization Note** The maximum is taken over nonempty vertex sets `W` of the number
`eIn H W` of edges of `H` with both ends in `W` (the published `TaitTobin.Outerplanar.eIn`), i.e.
over induced subgraphs. For a fixed vertex set the induced subgraph has the most edges, so this is
the paper's maximum over all nonempty subgraphs. `⌈a / b⌉` for `b ≥ 1` is the natural-number
quotient `(a + b − 1) / b`. On the empty vertex type the value is `0`. -/
noncomputable def pseudoarboricity {V : Type} [Fintype V] (H : SimpleGraph V) : ℕ :=
  (Finset.univ : Finset (Finset V)).sup
    (fun W => if W.Nonempty then (TaitTobin.Outerplanar.eIn H W + W.card - 1) / W.card else 0)

end SparseDisc


