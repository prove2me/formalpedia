-- Prove2me | Definitions.Def_DetStreamClique_MaxClique_Supplement_InsDel
-- name    : DetStreamClique_MaxClique_Supplement_InsDel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:19:08.736639+00:00
-- url     : https://prove2.me/theorems/8dcf8f51-b12a-468f-b558-99e8071d61d1
-- title:
--   Correctness of insertion-deletion streaming algorithms for approximate clique and independent set
-- statement:
--   An **insertion-deletion graph stream** on $V=\operatorname{Fin}(n)$ is a finite list of updates $\mathrm{ins}(e)$ and $\mathrm{del}(e)$, where $e$ is an unordered pair of distinct vertices. Starting from the empty graph, an insertion adds $e$ and a deletion removes it; the stream is **legal** when every insertion adds an edge that is currently absent and every deletion removes an edge that is currently present. The **final graph** $G(w)$ of a stream $w$ is the graph of surviving edges. (These notions are the published dynamic graph stream model, which is reused unchanged.)
--
--   A deterministic streaming machine reading such updates is **correct for $\beta$-approximate Maximum Clique** when, on every legal insertion-deletion stream $w$, its output $U$ satisfies
--   $$U\text{ is a clique of }G(w),\qquad |U|\ge\omega(G(w))/\beta,$$
--   and **correct for $\beta$-approximate Maximum Independent Set** when, on every legal stream $w$, its output is an independent set of $G(w)$ of size at least $\alpha(G(w))/\beta$.
--
--   As in the paper's model, the output is required only at the end of the stream and must be valid for the final set of surviving edges; the length of the stream and the number of deletions and re-insertions are unrestricted.
--
--   **Formalization Note** The update type, legality and final graph come from the published definition `SpanForestStream_Unrestricted_Stream`; the clique predicate is the published `ApproxClique` and the independent-set predicate is `ApproxIndep` of this supplement.
-- source:
--   Adithya Diddapur, Deterministic Streaming Lower Bounds for Approximate Maximum Clique and Maximum Independent Set, STOC 2027 submission #248 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/248.pdf, §1 (insertion-deletion streams; β-approximation), p. 2; Appendix A, p. 25

import Mathlib
import Definitions.Def_DetStreamClique_MaxClique_Graphs
import Definitions.Def_DetStreamClique_MaxClique_Supplement_IndepSet
import Definitions.Def_SpanForestStream_Unrestricted_Stream

open scoped Classical

namespace DetStreamClique.MaxClique.Supplement

open DetStreamClique.MaxClique SpanForestStream.Unrestricted

/-- Correctness of a machine reading insertion-deletion updates, for β-approximate
Maximum Clique: on every legal stream, the output is valid for the final graph of
surviving edges (p. 2). -/
def InsDelCorrectClique {n : ℕ} {S : Type}
    (a : StreamingMachine (Update n) (Finset (Fin n)) S) (β : ℝ) : Prop :=
  ∀ w : List (Update n), IsLegal w → ApproxClique β (currentGraph w) (a.run w)

/-- The same for β-approximate Maximum Independent Set. -/
def InsDelCorrectIndep {n : ℕ} {S : Type}
    (a : StreamingMachine (Update n) (Finset (Fin n)) S) (β : ℝ) : Prop :=
  ∀ w : List (Update n), IsLegal w → ApproxIndep β (currentGraph w) (a.run w)

end DetStreamClique.MaxClique.Supplement


