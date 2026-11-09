-- Prove2me | Definitions.Def_WeldedPath_bEdge
-- name    : WeldedPath_bEdge
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:00:04.48026+00:00
-- url     : https://prove2.me/theorems/0b0c5f62-e57c-49ad-85c3-463e8b968774
-- title:
--   Permuted edge classes $E_b$, $b\in B_{\mathrm{edge}}$, and the edge-color function $e_\alpha(v)$
-- statement:
--   Fix $l$ and the middle columns $B_{\mathrm{mid}}=[n-l,n+l]$. The **edge classes** are
--   $$
--   E_{\mathrm{tr},c,\alpha}=\{e\in E_{T_1}\cup E_{T_2}:\mathrm{col}(\mathrm{tail}(e))=c,\ \mathrm{Color}(e)=\alpha\},\qquad E_{\mathrm{wld},\alpha}=\{e\in E_W:\mathrm{Color}(e)=\alpha\},
--   $$
--   and the permuted classes are indexed by $B_{\mathrm{edge}}=\{(\mathrm{tr},c,\alpha):c\in B_{\mathrm{mid}},\alpha\in\mathcal C\}\cup\{(\mathrm{wld},\alpha):\alpha\in\mathcal C\}$. The **edge-cell indicator** $b_{\mathrm{edge}}(e)$ is $(\mathrm{tr},\mathrm{col}(\mathrm{tail}(e)),\mathrm{Color}(e))$ for a tree edge whose tail lies in $B_{\mathrm{mid}}$, $(\mathrm{wld},\mathrm{Color}(e))$ for a weld edge, and $\bot$ otherwise; $E_b$ is the set of edges with $b_{\mathrm{edge}}(e)=b$.
--
--   The **edge-color function** $e_\alpha(v)$ is the edge of color $\alpha$ containing $v$, or $\bot$ if there is none (for a vertex outside $V_n$, or the one color missing at a root).
--
--   **Formalization Note** For a proper coloring there is at most one edge of each color at a vertex, so $e_\alpha(v)$ is determined; it is chosen by `Classical.choose`.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912 (sha256 b31400a0…), pp.16–17, (20)–(22), (24) and the definition of b_edge

import Mathlib
import Definitions.Def_WeldedPath_WeldedInstance

namespace WeldedPath

/-- The labels `(tr, c, α)` and `(wld, α)` of the permuted edge classes (arXiv:2611.05912
(sha256 b31400a0…), §3.1, p.16). -/
inductive EdgeClass
  | tr (c : ℕ) (α : Fin 3)
  | wld (α : Fin 3)
  deriving DecidableEq

/-- `B_edge = {(tr, c, α) : c ∈ B_mid, α ∈ C} ∪ {(wld, α) : α ∈ C}`, with the middle columns
`B_mid = [n − l, n + l]` (arXiv:2611.05912 (sha256 b31400a0…), §3.1, pp.14 and 16). -/
def BEdge (n l : ℕ) : Finset EdgeClass :=
  ((Finset.Icc (n - l) (n + l)) ×ˢ (Finset.univ : Finset (Fin 3))).image
      (fun p => EdgeClass.tr p.1 p.2) ∪
    (Finset.univ : Finset (Fin 3)).image EdgeClass.wld

namespace WeldedInstance

variable {n : ℕ}

/-- The edge-cell indicator `b_edge(e)` (arXiv:2611.05912 (sha256 b31400a0…), p.17):
`(tr, col(tail(e)), Color(e))` for a tree edge with `col(tail(e)) ∈ B_mid`, `(wld, Color(e))` for a
weld edge, `⊥` (`none`) otherwise. -/
def bEdge (l : ℕ) (G : WeldedInstance n) : Edge → Option EdgeClass
  | .tree v =>
      if n - l ≤ col n v ∧ col n v ≤ n + l then some (.tr (col n v) (G.color (.tree v)))
      else none
  | .weld u w => some (.wld (G.color (.weld u w)))

/-- The edge class `E_b = {e ∈ E_n : b_edge(e) = b}`: `E_{tr,c,α}` (20)–(21) and `E_{wld,α}` (22)
(arXiv:2611.05912 (sha256 b31400a0…), p.16). -/
def classEdges (l : ℕ) (G : WeldedInstance n) (b : EdgeClass) : Finset Edge :=
  G.edges.filter fun e => G.bEdge l e = some b

/-- The edge-color function `e_α(v)` (24) (arXiv:2611.05912 (sha256 b31400a0…), p.17): the edge
of color `α` containing `v`, or `⊥` (`none`) if there is none.

**Formalization Note.** For a proper coloring there is at most one such edge, so the choice is
determined. -/
noncomputable def eAlpha (G : WeldedInstance n) (v : ℕ) (α : Fin 3) : Option Edge :=
  open Classical in
  if h : ∃ e ∈ G.edges, G.color e = α ∧ e.Incident n v then some (Classical.choose h) else none

end WeldedInstance

end WeldedPath


