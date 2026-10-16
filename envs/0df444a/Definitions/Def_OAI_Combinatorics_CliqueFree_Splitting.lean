-- Prove2me | Definitions.Def_OAI_Combinatorics_CliqueFree_Splitting
-- name    : OAI_Combinatorics_CliqueFree_Splitting
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T20:52:33.506464+00:00
-- url     : https://prove2.me/theorems/e73dfd4f-6ce1-4349-ba5f-f46ed604a13f
-- title:
--   The vertex-splitting graph on oriented edges and surviving triangles
-- statement:
--   Let $G$ be a simple graph on a finite vertex set $V$ with adjacency $\sim$, and let $\vec{E}(G)=\{(u,v)\in V\times V:\ u\sim v\}$ be its set of oriented edges, with $\mathrm{src}(u,v)=u$, $\mathrm{dst}(u,v)=v$ and reversal $\overline{(u,v)}=(v,u)$. Fix a map $F:\vec{E}(G)\to\vec{E}(G)$ that preserves sources, $\mathrm{src}(F(e))=\mathrm{src}(e)$ for every $e$, and a predicate "good" on $\vec{E}(G)$ marking admissible oriented edges.
--
--   1. **Split graph.** The simple graph $G_F$ with vertex set $\vec{E}(G)$ in which
--
--      $$a\sim_{G_F}b\iff\text{there is }e\in\vec{E}(G)\text{ with } e,\ \bar e\ \text{good},\ F(e)=a,\ F(\bar e)=b .$$
--
--      The relation is symmetric (replace $e$ by $\bar e$) and irreflexive, because $\mathrm{src}(a)=\mathrm{src}(e)\ne\mathrm{dst}(e)=\mathrm{src}(b)$.
--
--   2. **Surviving triangles.** An ordered triangle $t=(a,b,c)$ of $G$ (so $a\sim b$, $a\sim c$, $b\sim c$) survives if the three corner agreements
--
--      $$F(a,b)=F(a,c),\qquad F(b,a)=F(b,c),\qquad F(c,a)=F(c,b)$$
--
--      hold and all six oriented edges $(a,b),(b,a),(a,c),(c,a),(b,c),(c,b)$ are good.
--
--   The construction splits every vertex $u$ of $G$ into copies indexed by the oriented edges leaving $u$. The map $F$ assigns to each oriented edge $(u,v)$ the copy of $u$ that carries the edge $uv$, and an edge that is good in both directions is kept between the copies $F(u,v)$ and $F(v,u)$. A surviving triangle has all three edges kept and meeting at a single copy of each corner, so it reappears as a triangle of $G_F$. With the weight $w\circ\mathrm{src}$ on copies, the source map projects $G_F$ onto $G$ injectively on oriented edges; a suitable random choice of $F$ lowers neighbourhood masses while most of the weighted triangle mass survives.
--
--   **Formalization Note** The split graph is `Splitting.graph F hF good`, where `hF` is the proof that `F` preserves sources, and its vertex type is `EdgeState G`. `Splitting.Survives F good t` is phrased with the oriented edges `edge12`, `edge13`, `edge23` of the triangle state `t` and their reversals.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/Splitting.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/Splitting.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CliqueFreeLog mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
import Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw
import Definitions.Def_OAI_Combinatorics_CliqueFree_Deletion
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteEntropy
import Definitions.Def_OAI_Combinatorics_CliqueFree_EdgeState
import Definitions.Def_OAI_Combinatorics_CliqueFree_SparseMultipliers
import Definitions.Def_OAI_Combinatorics_CliqueFree_TriangleState
import Definitions.Def_OAI_Combinatorics_CliqueFree_Projection

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

attribute [local instance 10000] edgeStateDecEq

namespace Splitting
variable {G : SimpleGraph V}

noncomputable def graph (F : EdgeState G → EdgeState G)
    (hF : ∀ e, (F e).src = e.src) (good : EdgeState G → Prop) : SimpleGraph (EdgeState G) where
  Adj a b := ∃ e, good e ∧ good e.rev ∧ F e = a ∧ F e.rev = b
  symm := ⟨by
    rintro a b ⟨e, he, hr, ha, hb⟩
    exact ⟨e.rev, hr, by simpa using he, hb, by simpa using ha⟩⟩
  loopless := ⟨by
    rintro a ⟨e, he, hr, ha, hb⟩
    have heq : e.src = e.dst := by
      calc
        e.src = (F e).src := (hF e).symm
        _ = (F e.rev).src := congrArg EdgeState.src (ha.trans hb.symm)
        _ = e.dst := hF e.rev
    exact e.adj.ne heq⟩

/-- All three corner agreements and all six admissible incidences. -/
def Survives (F : EdgeState G → EdgeState G) (good : EdgeState G → Prop)
    (t : TriangleState G) : Prop :=
  F t.edge12 = F t.edge13 ∧
  F t.edge12.rev = F t.edge23 ∧
  F t.edge13.rev = F t.edge23.rev ∧
  good t.edge12 ∧ good t.edge12.rev ∧ good t.edge13 ∧ good t.edge13.rev ∧
  good t.edge23 ∧ good t.edge23.rev

end Splitting

end CliqueFreeIndependence.WeightedGraph

end

end OAI


