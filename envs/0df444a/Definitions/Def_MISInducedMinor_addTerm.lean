-- Prove2me | Definitions.Def_MISInducedMinor_addTerm
-- name    : MISInducedMinor_addTerm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:19:15.743715+00:00
-- url     : https://prove2.me/theorems/198e7576-7a10-4be3-b208-be81886ee3de
-- title:
--   The additive term $\sum_{v_jv_{j'}\in E(F),\,j<j'}(j'-j)$
-- statement:
--   For a graph $F$ on the ordered vertices $v_1,\dots,v_n$, the **additive term** of Lemma 3.2 is
--
--   $$\sum_{\substack{v_jv_{j'}\in E(F)\\ j<j'}}(j'-j),$$
--
--   the sum, over all edges, of the distance between their endpoints in the vertex order. Lemma 3.2 states $\alpha(G_F)=\mathrm{MaxCut}(F)+2\sum(j'-j)$, and $|V(G_F)|=8\sum(j'-j)$.
--
--   **Formalization Note** The sum runs over the edge list, whose pairs $(a,b)$ satisfy $a<b$, so the natural-number difference $b-a$ is exact. With 0-based vertex indices the value is the same, since the term is shift-invariant.
-- source:
--   Bonnet, Chang, Max Independent Set Remains NP-hard when Excluding a Planar Induced Minor (and More), arXiv:2609.11285 (sha256 e378b906…), Lemma 3.2, p.7

import Definitions.Def_MISInducedMinor_edgeList

set_option autoImplicit false

namespace MISInducedMinor

/-- The sum `∑_{vⱼvⱼ′ ∈ E(F), j < j′} (j′ − j)` of Lemma 3.2: for every edge, the distance
between its endpoints in the vertex order. arXiv:2609.11285 (sha256 e378b906…), Lemma 3.2, p.7.

**Formalization Note.** The sum runs over `edgeList F`, whose entries `(a, b)` have `a < b`, so the
natural-number subtraction `b - a` is exact. The term is shift-invariant, so 0-based vertex
indices give the paper's value. -/
def addTerm {n : ℕ} (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] : ℕ :=
  ((edgeList F).map fun e => e.2.val - e.1.val).sum

end MISInducedMinor


