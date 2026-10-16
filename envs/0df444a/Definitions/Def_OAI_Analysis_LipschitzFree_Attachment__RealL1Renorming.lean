-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_Attachment__RealL1Renorming
-- name    : OAI_Analysis_LipschitzFree_Attachment__RealL1Renorming
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T12:01:41.649142+00:00
-- url     : https://prove2.me/theorems/1299a671-a9bb-48ce-b896-d5a41cad830e
-- title:
--   The short relation on metric-block points: near vertices and equal anchors
-- statement:
--   Let $G$ be a port graph with vertex set $X$ and port set $D$ (moves $(x,e)\mapsto x\cdot e$ along ports, extended to words $w$ of ports by $x\cdot w$), let $\chi:X\to C$ be a colouring by a finite set $C$, and let $\mathrm{cap},R\in\mathbb{N}$. The points of the associated metric block are $P=X\sqcup\mathcal{A}$, where $\mathcal{A}$ is the finite set of anchors, i.e. the vectors of capped colour distances $\lambda(x)\in\{0,\dots,\mathrm{cap}\}^C$ that occur for some vertex $x$.
--
--   For $n\in\mathbb{N}$ this file defines the **short relation** $u\approx_n v$ on $P$:
--
--   1. for vertices $x,y\in X$, $x\approx_n y$ holds if and only if $y$ is $n$-near to $x$, i.e.
--   $$x\approx_n y\iff \text{there is a word } w \text{ over } D \text{ with } |w|\le n \text{ and } x\cdot w=y;$$
--   2. for anchors $a,b\in\mathcal{A}$, $a\approx_n b$ holds if and only if $a=b$;
--   3. a vertex and an anchor are never related.
--
--   The relation expresses that two points of a metric block are close in the combinatorial sense: reachable by a short walk for vertices, identical for anchors. When the port set $D$ is finite, each point is related to only finitely many points, which makes it a convenient bookkeeping device for the attachment-length estimates of the construction.
--
--   **Formalization Note** The relation is `MetricBlock.ShortRelation G color cap R n`, defined by pattern matching on the sum type of points; it does not depend on $R$ beyond the type of points, and the vertex case is `PortGraph.Near n x y` (walks along arbitrary, not necessarily reduced, words).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/Attachment.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/Attachment.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RealL1Renorming mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Model__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Evaluation__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Coordinates__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Coefficients
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock__RealL1Renorming

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Attachment-length estimates and label compatibility
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped Classical
namespace PortGraph
variable {X D : Type*} (G : PortGraph X D)
end PortGraph

namespace MetricBlock
variable {X D C : Type*} [Fintype C] (G : PortGraph X D) (color : X → C) (cap R : ℕ)

def ShortRelation (n : ℕ) : Point G color cap R → Point G color cap R → Prop
  | Sum.inl x, Sum.inl y => G.Near n x y
  | Sum.inr a, Sum.inr b => a = b
  | _, _ => False

variable [Fintype D]

variable [Fact (0 < R)]

end MetricBlock
end DiscreteFree
end

end

end OAI


