-- Prove2me | Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTableModel
-- name    : OAI_MeasureTheory_DyadicAvoidance_WindowTableModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:23:32.931992+00:00
-- url     : https://prove2.me/theorems/50230aa8-e5b2-4e42-8306-cf5eb7e4ea28
-- title:
--   Window endpoints as reading resolutions of the selector and terminal tables
-- statement:
--   Fix $M, d, g, r_0 \in \mathbb{N}$ and window data $W$ for a tree with $q = M+1$ children per node (child $M$ being the default child), depth $d$, gap $g$ and length threshold $r_0$. Among other things, $W$ assigns to every word $P$ over $\{0,\dots,M\}$ a natural number $b_W(P)$, the right endpoint of the window of scale exponents attached to the edge ending at $P$. Nodes are words of length less than $d$ and leaves are words of length exactly $d$; $P\,i$ denotes $P$ followed by the letter $i$.
--
--   1. **Selector edge.** For a node $P$ and a nondefault child $i \in \{0,\dots,M-1\}$, the selector edge is the word $P\,i$, i.e. the edge from $P$ to its child $i$.
--
--   2. **Selector resolutions.** $b^{\mathrm{sel}}_W(P,i) = b_W(P\,i)$ for every node $P$ and every $i < M$.
--
--   3. **Terminal resolutions.** $b^{\mathrm{ter}}_W(L) = b_W(L)$ for every leaf $L$.
--
--   With these resolutions, the selector of child $i$ at node $P$ and the terminal label of leaf $L$ are read at a point $x$ through the dyadic keys
--   $$
--   \big\lfloor 2^{\,b_W(P\,i)+2}\,\{x\} \big\rfloor \qquad \text{and} \qquad \big\lfloor 2^{\,b_W(L)+2}\,\{x\} \big\rfloor,
--   $$
--   where $\{x\} = x - \lfloor x \rfloor$; that is, through the cell of mesh $2^{-(b_W(P\,i)+2)}$, respectively $2^{-(b_W(L)+2)}$, containing the fractional part of $x$.
--
--   This instantiates the abstract finite table model with concrete resolutions tied to the window geometry: each table is read at the scale at which the window of its incoming edge ends. The selector and terminal address sets, the product law of the tables and the routed random set of the main construction are all taken with these resolutions.
--
--   **Formalization Note** Here $W$ is a term of `WindowData (M + 1) d g r₀`, nondefault children are embedded into `Fin (M + 1)` by `castSucc`, and a leaf is used through its underlying list.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/WindowTableModel.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/WindowTableModel.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DyadicAvoidance mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterRouteExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ExceptionalCenters
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFailureBound
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteLabelMeasures
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RandomSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefaultSelection
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteLocalPredicate
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowData

namespace OAI

noncomputable section

namespace Problem310.FiniteTableModel

variable {M d g r₀ : ℕ}

/-- The nondefault child edge used by a selector table. -/
def selectorEdge (P : Node M d) (i : Fin M) : List (Child M) :=
  P.val ++ [i.castSucc]

/-- Canonical selector resolutions are the incoming window endpoints. -/
def selectorEndpoints (W : WindowData (M + 1) d g r₀) : Node M d → Fin M → ℕ :=
  fun P i => W.b (selectorEdge P i)

/-- Each terminal table uses its leaf's incoming-edge endpoint. -/
def terminalEndpoints (W : WindowData (M + 1) d g r₀) : Leaf M d → ℕ :=
  fun L => W.b L.val

end Problem310.FiniteTableModel

end

end OAI


