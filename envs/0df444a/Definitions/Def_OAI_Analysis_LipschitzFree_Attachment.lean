-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_Attachment
-- name    : OAI_Analysis_LipschitzFree_Attachment
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T09:06:09.997125+00:00
-- url     : https://prove2.me/theorems/4f270181-c0b4-48bf-8348-9a810feb2022
-- title:
--   The short-range relation between points of a metric block
-- statement:
--   Consider a metric block: a port graph with vertex set $X$ and port set $D$ (moves $x\mapsto x\cdot e$, each undone by the reverse port), a colouring $\chi:X\to C$ by a finite set $C$, natural numbers $\mathrm{cap}$ and $R$, and the point set $P=X\sqcup\mathcal{A}$, the disjoint union of the vertices and of the finite set $\mathcal{A}$ of label anchors (the box labels $\lambda(x)\in\{0,\dots,\mathrm{cap}\}^C$ of capped distances from vertices $x$ to the colour classes).
--
--   For $n\in\mathbb{N}$ the short relation $\sim_n$ on $P$ is
--   $$u\sim_n v\iff\begin{cases} y=x\cdot w \text{ for some word } w \text{ of ports of length } |w|\le n, & \text{if } u=x\in X,\ v=y\in X,\\ a=b, & \text{if } u=a\in\mathcal{A},\ v=b\in\mathcal{A},\\ \text{never}, & \text{if one of } u,v \text{ is a vertex and the other an anchor.}\end{cases}$$
--   So two vertices are related when the second is reachable from the first by a walk of at most $n$ moves, two anchors only when they coincide, and a vertex is never related to an anchor.
--
--   The relation describes the block metric below the attachment length $R$: it is the comparison relation used to show that a point at block distance $n<R$ from $u$ is $\sim_n$-related to $u$, so that closed balls of radius $n<R$ are finite and have at most as many points as there are port words of length at most $n$.
--
--   **Formalization Note** `MetricBlock.ShortRelation G color cap R n` is defined on `Point G color cap R` by pattern matching on the two summands; the vertex case is `PortGraph.Near n x y`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/Attachment.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/Attachment.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DiscreteLipschitzFree mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DiscreteLipschitzFree
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs
import Definitions.Def_OAI_Analysis_LipschitzFree_RenormingModel
import Definitions.Def_OAI_Analysis_LipschitzFree_Model
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock

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


