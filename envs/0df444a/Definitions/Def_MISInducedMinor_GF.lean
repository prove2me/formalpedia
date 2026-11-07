-- Prove2me | Definitions.Def_MISInducedMinor_GF
-- name    : MISInducedMinor_GF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:19:28.323195+00:00
-- url     : https://prove2.me/theorems/1b306ee7-ab29-426d-b996-255e05387a70
-- title:
--   The retained rows $R_{e,s}$ and the graph $G_F$
-- statement:
--   Let $F$ be an $n$-vertex $m$-edge graph with vertices $v_1,\dots,v_n$, and let $G=G_{2m,2n-1}$ be the intermediate graph, in which the odd column $C_{2j-1}$ represents $v_j$. Every edge $e$ of $F$ has two reserved rows $e_0,e_1$. For $e=v_jv_{j'}$ with $j<j'$ and each side $s\in\{0,1\}$, row $e_s$ retains exactly
--
--   $$R_{e,s}=\{(e_s,2j-1,s),\,(e_s,2j'-1,1-s)\}\cup\{(e_s,\ell,t):2j-1<\ell<2j'-1,\ t\in\{0,1\}\},$$
--
--   that is, one endpoint vertex on side $s$ in the column of $v_j$, one on the other side in the column of $v_{j'}$, and both sides of every column strictly between. The graph
--
--   $$G_F=G\Bigl[\,\bigcup_{e\in E(F)}(R_{e,0}\cup R_{e,1})\Bigr]$$
--
--   is the subgraph of $G$ induced by all retained vertices. Its independence number determines $\mathrm{MaxCut}(F)$ (Lemma 3.2), and it excludes the $5\times5$ grid as an induced minor (Lemma 3.1).
--
--   **Formalization Note** Indices are 0-based: vertex $v_j$ is $j-1$ and its column $2j-1$ is column $2(j-1)$. Edge number $t$ of the edge list, $(a,b)$ with $a<b$, has rows $2t$ (side $0$) and $2t+1$ (side $1$); $1-s$ is the other side. The vertex type of $G_F$ is the subtype of retained vertices.
-- source:
--   Bonnet, Chang, Max Independent Set Remains NP-hard when Excluding a Planar Induced Minor (and More), arXiv:2609.11285 (sha256 e378b906…), §3, pp.6–7

import Definitions.Def_MISInducedMinor_bonnetG
import Definitions.Def_MISInducedMinor_edgeList

set_option autoImplicit false

namespace MISInducedMinor

/-- The **retained vertices** `⋃_{e ∈ E(F)} (R_{e,0} ∪ R_{e,1})` of §3, p.6 of arXiv:2609.11285
(sha256 e378b906…). For `e = vⱼvⱼ′` with `j < j′` and each side `s`, row `e_s` retains

`R_{e,s} = {(e_s, 2j − 1, s), (e_s, 2j′ − 1, 1 − s)} ∪ {(e_s, ℓ, t) : 2j − 1 < ℓ < 2j′ − 1, t ∈ {0, 1}}`.

Here edge number `t` of `edgeList F`, say `(a, b)` with `a < b`, has rows `2t` (side `s = 0`) and
`2t + 1` (side `s = 1`), and row `2t + s` retains `(2t + s, 2a, s)`, `(2t + s, 2b, s′)` with
`s′ ≠ s`, and every `(2t + s, ℓ, t′)` with `2a < ℓ < 2b`.

**Formalization Note.** Indices are 0-based: vertex `vⱼ` is `j - 1 : Fin n`, and its column
`2j − 1` is column `2(j − 1)`; `1 − s` is the other side `s′ ≠ s` of `Fin 2`. -/
def keep {n : ℕ} (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] :
    Set (Fin (2 * (edgeList F).length) × Fin (2 * n - 1) × Fin 2) :=
  {x | ∃ (t : Fin (edgeList F).length) (s : Fin 2),
    x.1.val = 2 * t.val + s.val ∧
      ((x.2.1.val = 2 * ((edgeList F).get t).1.val ∧ x.2.2 = s) ∨
        (x.2.1.val = 2 * ((edgeList F).get t).2.val ∧ x.2.2 ≠ s) ∨
        (2 * ((edgeList F).get t).1.val < x.2.1.val ∧
          x.2.1.val < 2 * ((edgeList F).get t).2.val))}

/-- The graph **`G_F = G[⋃_{e ∈ E(F)} (R_{e,0} ∪ R_{e,1})]`**: the subgraph of the intermediate
graph `G` with `2m` rows and `2n − 1` columns induced by the retained vertices.
arXiv:2609.11285 (sha256 e378b906…), §3, p.7.

**Formalization Note.** `m` is the number of edges of `F` (`(edgeList F).length`); the vertex type
of `G_F` is the subtype of retained vertices. -/
def GF {n : ℕ} (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] :
    SimpleGraph ↥(keep F) :=
  (bonnetG (2 * (edgeList F).length) (2 * n - 1)).induce (keep F)

end MISInducedMinor


