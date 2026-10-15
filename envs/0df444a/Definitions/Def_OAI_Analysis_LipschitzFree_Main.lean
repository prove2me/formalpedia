-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_Main
-- name    : OAI_Analysis_LipschitzFree_Main
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T09:47:19.293512+00:00
-- url     : https://prove2.me/theorems/78bb8e01-15e4-4615-bec7-0ebe3a195ffd
-- title:
--   The wedge of all metric blocks: a countable space whose Lipschitz-free space has the approximation property but not the bounded approximation property
-- statement:
--   For every $p\ge1$ the block construction provides a pointed metric space $(\mathcal{M}_p,o_p)$: a countable, infinite metric space whose distinct points are at distance at least $1$ and whose distances are at most $300p^2+150p+5$. It is obtained from a countable colored port graph (all colorings of the Cayley graphs of finite permutation groups of free-group balls, with $p$-dependent numbers of generators and colors) by adjoining finitely many anchor points, the label vectors of the vertices, and taking the shortest-path metric in which graph edges have length $1$, a vertex is joined to its own anchor by a step of length $R(p)=30p$, and all other steps are at least as long. The base point $o_p$ is one of the anchors.
--
--   The **wedge** of a sequence $(M_n,o_n)_{n\in\mathbb{N}}$ of pointed metric spaces is the set $\{*\}\sqcup\bigsqcup_n(M_n\setminus\{o_n\})$, in which all base points are identified with $*$, points of the same component keep their distance, $d(x,*)=d_n(x,o_n)$, and $d(x,y)=d_n(x,o_n)+d_m(y,o_m)$ for $x\in M_n$, $y\in M_m$ with $n\neq m$.
--
--   This module defines the final space.
--
--   1. **Positive radius.** For every $n\in\mathbb{N}$ the attachment radius satisfies $R(n+1)>0$, so the block metric of $\mathcal{M}_{n+1}$ is defined.
--   2. **Pieces.** The $n$-th piece is the block $\mathcal{M}_{n+1}$ with base point $o_{n+1}$ $(n=0,1,2,\dots)$.
--   3. **The space.**
--   $$
--   \mathbb{M}=\bigvee_{n\in\mathbb{N}}\bigl(\mathcal{M}_{n+1},o_{n+1}\bigr),
--   $$
--   the wedge of all blocks glued at their base points.
--   4. **Base point.** The common base point $*\in\mathbb{M}$.
--
--   The pointed space $(\mathbb{M},*)$ is the witness for the main statement of the mission: $\mathbb{M}$ is countable, its distinct points are at distance at least $1$, it is unbounded and not proper, its Lipschitz-free space has the approximation property, and for no $\Lambda\ge1$ does it have the bounded approximation property with constant $\Lambda$.
--
--   **Formalization Note** The objects are the instance `radius_fact n : Fact (0 < BlockParameters.R (n+1))`, `Piece n = BlockConstruction.Block (n+1)`, `pieceBase n = BlockConstruction.base (n+1)`, `Space = MetricWedge.Point Piece pieceBase` and `base`. Indexing the pieces by $n+1$ avoids the degenerate parameter $p=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/Main.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/Main.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment
import Definitions.Def_OAI_Analysis_LipschitzFree_Words
import Definitions.Def_OAI_Analysis_LipschitzFree_StatePaths
import Definitions.Def_OAI_Analysis_LipschitzFree_SignedTests
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphWalks
import Definitions.Def_OAI_Analysis_LipschitzFree_Evaluation
import Definitions.Def_OAI_Analysis_LipschitzFree_Coordinates
import Definitions.Def_OAI_Analysis_LipschitzFree_AffineWeights
import Definitions.Def_OAI_Analysis_LipschitzFree_LabelBumps
import Definitions.Def_OAI_Analysis_LipschitzFree_ScalarTests
import Definitions.Def_OAI_Analysis_LipschitzFree_FiniteQuotients
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphGirth
import Definitions.Def_OAI_Analysis_LipschitzFree_ColorCounting
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphColoring
import Definitions.Def_OAI_Analysis_LipschitzFree_BlockObstruction
import Definitions.Def_OAI_Analysis_LipschitzFree_Functor
import Definitions.Def_OAI_Analysis_LipschitzFree_Wedge
import Definitions.Def_OAI_Analysis_LipschitzFree_RetainedWedge
import Definitions.Def_OAI_Analysis_LipschitzFree_WedgeApproximation

namespace OAI

/-!
# A countable separated free space with AP and no finite BAP constant
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree.MainConstruction
open scoped Classical

instance radius_fact (n : ℕ) : Fact (0 < BlockParameters.R (n+1)) :=
  ⟨BlockParameters.R_pos (by omega)⟩

abbrev Piece (n : ℕ) := BlockConstruction.Block (n+1)
def pieceBase (n : ℕ) : Piece n := BlockConstruction.base (n+1)
abbrev Space := MetricWedge.Point Piece pieceBase
def base : Space := MetricWedge.base Piece pieceBase

end DiscreteFree.MainConstruction

namespace DiscreteFree

end DiscreteFree
end

namespace DiscreteFree

end DiscreteFree

end

end OAI


