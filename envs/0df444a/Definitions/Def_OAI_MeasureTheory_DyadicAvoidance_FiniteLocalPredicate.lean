-- Prove2me | Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteLocalPredicate
-- name    : OAI_MeasureTheory_DyadicAvoidance_FiniteLocalPredicate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:20:09.326009+00:00
-- url     : https://prove2.me/theorems/e2d7f602-bc8d-4ee1-a3a2-4d5a83832b3e
-- title:
--   The leaf reached by routing from an intermediate node of a depth-$d$ tree
-- statement:
--   Fix $M, d \in \mathbb{N}$. Children are $0,1,\dots,M$, and a leaf is a word of length exactly $d$ over $\{0,\dots,M\}$; write $\mathcal{L}_{M,d}$ for the set of leaves. Let $\operatorname{ch}$ be a choice rule assigning to every word $P$ and every point $x \in \mathbb{R}$ a child $\operatorname{ch}(P,x)$, and let $R_r(P,x)$ be the word reached from $P$ after $r$ routing steps, $R_0(P,x) = P$ and $R_{k+1}(P,x) = R_k(P,x)\,\operatorname{ch}(R_k(P,x),x)$ (append the chosen child), so that $|R_r(P,x)| = |P| + r$.
--
--   Given $r \in \mathbb{N}$ and a word $P$ with $|P| + r = d$, the *local leaf* of $x$ below $P$ is
--   $$
--   L^{\operatorname{ch}}_{r}(P,x) = R_r(P,x) \in \mathcal{L}_{M,d},
--   $$
--   the leaf obtained by routing $x$ for the remaining $r$ steps starting from the node $P$ rather than from the root.
--
--   In the local analysis of the random router, one considers a node $U$ at which a centre takes the default child and a nondefault child $Ui$ of it; a nearby point is routed from $Ui$ down to depth $d$, and the terminal label of the resulting local leaf, together with the selector of child $i$ at $U$, decides whether the local trial attached to $(U,i)$ succeeds.
--
--   **Formalization Note** The hypothesis $|P| + r = d$ is an explicit argument, used together with the length formula for `routeFrom` to package the routed word as an element of `List.Vector (Fin (M + 1)) d`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/FiniteLocalPredicate.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/FiniteLocalPredicate.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace Problem310.FiniteLocalPredicate

-- [generator] trimmed: open RoutingPath GridSeparation LocalPredicateFactor FiniteTableModel
open RoutingPath GridSeparation FiniteTableModel

variable {M d : ℕ}

/-- The leaf reached from a local child, with its ambient-depth proof retained. -/
def localLeaf (choose : List (Child M) → ℝ → Child M)
    (r : ℕ) (P : List (Child M)) (hdepth : P.length + r = d) (x : ℝ) : Leaf M d :=
  ⟨routeFrom choose r P x, (length_routeFrom choose r P x).trans hdepth⟩

end Problem310.FiniteLocalPredicate

end

end OAI


