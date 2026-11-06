-- Prove2me | Definitions.Def_ZeroOneExpansion_crossGraph
-- name    : ZeroOneExpansion_crossGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:22:09.513444+00:00
-- url     : https://prove2.me/theorems/1e411850-1246-41fd-8456-26be3b5f505f
-- title:
--   Cross-layer graph $(V_n,E_{\mathrm{cross}})$ of $P_n$
-- statement:
--   The **cross-layer graph** of $P_n$ has the vertices of $P_n$ as vertex set and the **cross-layer edges** as edges: the edges of $G_n$ whose endpoints lie in different layers (one with $t=0$, the other with $t=1$). Same-layer edges are excluded.
--
--   It is the graph whose connected components $V_{K,L}$ are described in Lemma 11.
-- source:
--   Yang, 0/1-Polytopes with Exponentially Small Edge Expansion, arXiv:2608.01870 (pdf sha256 53e57bdc2a5505f50b990dfb27d47df0f7d5e2feffc89b808f29d40cff38be53), §3, p.6, "Esame and Ecross"

import Mathlib
import Definitions.Def_ZeroOneExpansion_Pn

set_option autoImplicit false

namespace ZeroOneExpansion

/-- The **cross-layer graph** `(Vn, Ecross)` (arXiv:2608.01870, §3, p.6: "Let Esame and Ecross denote
the sets of same-layer and cross-layer edges of Pn"): the vertices of `Pn`, joined when they are
adjacent in `Gn` and lie in different layers (different last coordinate `t`).

**Formalization Note** Defined through `SimpleGraph.fromRel` of an already symmetric relation, so
its adjacency is exactly "adjacent in `Gn` with different layer coordinates". -/
noncomputable def crossGraph (n : ℕ) : SimpleGraph (Grunbaum2003.PolytopeVertex (Pn n)) :=
  SimpleGraph.fromRel fun u v => (Gn n).Adj u v ∧ layer n u.val ≠ layer n v.val

end ZeroOneExpansion


