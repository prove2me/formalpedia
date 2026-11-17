-- Prove2me | Definitions.Def_BipDijoin_Supplement_DecodesSourcePartialPM
-- name    : BipDijoin_Supplement_DecodesSourcePartialPM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:51:42.780897+00:00
-- url     : https://prove2.me/theorems/dba5ab12-c1ac-4278-89f3-27dd17e5e08c
-- title:
--   Output of Theorem 6.2: a partial relaxed end decomposition contracting only source strong ends, with a perfect matching
-- statement:
--   The output layout of Theorem 6.2. The words list a partial relaxed bipartite end decomposition of $G$ as records $s,\ |U|,\ U,\ |P|,\ P$ (vertices in current names, the $i$-th contracted vertex named $n+i$), followed by $|N|,\ N$ for a perfect matching $N$ of the final graph $H$. They are correct if the records form a partial relaxed end decomposition ending at $H$, **every record contracts a source strong end** ($s=0$), $N$ is a perfect matching of $H$, and
--   $$|V(H)|\le|V(G)|-\alpha(G),$$
--   where $\alpha(G)$ is the number of vertices left unmatched by a maximum matching of $G$.
--
--   It is the published layout of Theorem 3.5's output with the extra requirement that only source strong ends are contracted, which is what lets the decomposition of the $V_\infty$ part be reused inside the whole graph (proof of Theorem 3.5, p.26).
--
--   **Formalization Note** The inequality is written $|V(H)|+\alpha(G)\le|V(G)|$, to avoid natural-number subtraction.
-- source:
--   C. Nalam, T. Saranurak, Breaking the O(mn) Barrier for Minimum Bipartite Dijoin via Dynamic and Local Graph Algorithms, STOC 2027 submission (manuscript sha256 382f85e4bb71b51866bdfa1d09aa8a3e2f160dd4266b9f2c87827be49387fea6), Theorem 6.2, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_BipDijoin_BipGraph
import Definitions.Def_BipDijoin_IsMatching
import Definitions.Def_BipDijoin_IsPartialDecomp
import Definitions.Def_BipDijoin_ofInput

set_option autoImplicit false

namespace BipDijoin

namespace Supplement

/-!
# Output layout of Theorem 6.2: a partial decomposition contracting only source strong ends

Nalam–Saranurak, STOC 2027 submission (manuscript sha256 382f85e4…7fea6), Theorem 6.2, p.25
(PDF p.27): "outputs a partial relaxed end decomposition by contracting only source strong ends
and ending with a perfectly matchable graph H along with a certifying matching … We also have that
|V(H)| ≤ |V(G)| − α where α represents the number of unmatched vertices in the maximum matching
of G."

**Formalization Note.** The layout is the base `DecodesPartialPM` (records `s, |U|, U, |P|, P` in
current vertex names with representatives `n, n + 1, …`, then `|N|, N` for a perfect matching `N`
of the final graph `H`, and `|V(H)| + α(G) ≤ |V(G)|`), with the extra requirement that every record
is a source end (`left = true`, written `s = 0`). `α(G)`, the base `deficiency`, is the minimum
number of vertices left unmatched by a matching, that is, the number left unmatched by a maximum
matching.
-/

/-- The words `ws` encode a partial relaxed bipartite end decomposition of `G` (representatives
`n, n + 1, …`) contracting only source strong ends and ending at a graph `H`, a perfect matching
`N` of `H`, and `|V(H)| ≤ |V(G)| − α(G)`. -/
def DecodesSourcePartialPM (G : BipGraph) (n : ℕ) (ws : List ℕ) : Prop :=
  ∃ (recs : List Rec) (chunks : List (List ℕ)) (Nl : List ℕ) (H : BipGraph),
    List.Forall₂ RecWords recs chunks ∧ ws = recs.length :: chunks.flatten ++ (Nl.length :: Nl) ∧
    Nl.Nodup ∧ IsPartialDecomp false G n recs H ∧ H.IsPerfectMatching Nl.toFinset ∧
    H.V.card + G.deficiency ≤ G.V.card ∧ ∀ r ∈ recs, r.left = true

end Supplement

end BipDijoin


