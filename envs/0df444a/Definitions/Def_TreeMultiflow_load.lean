-- Prove2me | Definitions.Def_TreeMultiflow_load
-- name    : TreeMultiflow_load
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:58:55.116002+00:00
-- url     : https://prove2.me/theorems/75de4f2e-85ae-4535-ab42-3dc263942ab2
-- title:
--   Load $|\{f\in S : e\in\mathrm{Path}(f)\}|$ of a set of requests on an edge
-- statement:
--   Let $F$ be a finite set of labeled requests in a tree, request $f$ having endpoints $s_f,t_f$. For $S\subseteq F$ and an edge $e$, the **load of $S$ on $e$** is
--   $$
--   \operatorname{load}(S,e)=\bigl|\{f\in S : e\in\mathrm{Path}(f)\}\bigr|.
--   $$
--   For a collection of paths, its load on an edge is the number of its paths that use that edge.
--
--   Feasibility of a request set and the bounds of Theorems 2.1, 2.2 and 3.1 are stated with this quantity.
--
--   **Formalization Note** Requests are the elements of an index type with two endpoint maps, so several requests may have the same endpoints.
-- source:
--   Harb, Improved Integrality Gap for Multicommodity Flow on Trees, arXiv:2609.07949, Section 1, p.2 (the load of S on e)

import Mathlib
import Definitions.Def_TreeMultiflow_OnPath

namespace TreeMultiflow

open Classical in
/-- **Load of a set of requests on an edge.**
Harb, *Improved Integrality Gap for Multicommodity Flow on Trees*, arXiv:2609.07949, Section 1,
p.2: "We call the cardinality on the left the load of S on e. When we work directly with a
collection of paths, its load on an edge likewise means the number of its paths that use that
edge."

For labeled requests `F` with endpoints `src f`, `dst f` and a finite set `S ⊆ F`,
`load G src dst S e = |{f ∈ S : e ∈ Path(f)}|`.

**Formalization Note.** Requests are the elements of an index type `F` with endpoint maps, so
several requests may share endpoints (labeled requests). Decidability of `OnPath` is classical. -/
noncomputable def load {V F : Type*} (G : SimpleGraph V) (src dst : F → V) (S : Finset F)
    (e : Sym2 V) : ℕ :=
  (S.filter fun f => OnPath G (src f) (dst f) e).card

end TreeMultiflow


