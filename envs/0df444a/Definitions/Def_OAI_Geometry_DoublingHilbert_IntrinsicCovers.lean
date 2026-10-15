-- Prove2me | Definitions.Def_OAI_Geometry_DoublingHilbert_IntrinsicCovers
-- name    : OAI_Geometry_DoublingHilbert_IntrinsicCovers
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T07:02:38.69004+00:00
-- url     : https://prove2.me/theorems/7ef31b22-1310-49fd-9e1e-fbaa8f80d89f
-- title:
--   Ambient formulation of the doubling condition with centers in the set
-- statement:
--   Let $(B,d)$ be a metric space, $K\subseteq B$ a subset and $\Lambda\in\mathbb{N}$. The set $K$ satisfies the ambient doubling condition with constant $\Lambda$ if for every $x\in K$ and every radius $r>0$ there is a finite set $C\subseteq B$ of centers such that
--   $$
--   C\subseteq K,\qquad |C|\le\Lambda,\qquad \forall y\in K:\ \ d(y,x)<r\ \Longrightarrow\ \exists c\in C:\ d(y,c)<\frac r2 .
--   $$
--   In words: the points of $K$ in the open ball of radius $r$ around any point of $K$ are covered by at most $\Lambda$ open balls of radius $r/2$ whose centers lie in $K$.
--
--   This is the doubling bound used in the main statement, except that the centers form a finite subset of the ambient space $B$ that is required to lie in $K$, rather than a finite set of elements of the metric subspace $K$. The ambient form is more convenient for iterating covers and for combining the center sets of several pieces of a set.
--
--   **Formalization Note** The predicate is `AmbientDoubling K bound`, with `centers : Finset B`. Its equivalence with the subtype-based `DoublingAtMost K bound` of the mission statement is a separate theorem.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/IntrinsicCovers.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/IntrinsicCovers.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CompactBanach mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CompactBanach
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids
import Definitions.Def_OAI_Geometry_DoublingHilbert_SelectedSheets
import Definitions.Def_OAI_Geometry_DoublingHilbert_Energy
import Definitions.Def_OAI_Geometry_DoublingHilbert_Crossings
import Definitions.Def_OAI_Geometry_DoublingHilbert_Doubling
import Definitions.Def_OAI_Geometry_DoublingHilbert_CoordinateSupport
import Definitions.Def_OAI_Geometry_DoublingHilbert_CoordinateMap

namespace OAI

open Set Metric
open scoped BigOperators
noncomputable section
namespace CompactBanach

def AmbientDoubling {B : Type*} [MetricSpace B] (K : Set B) (bound : ℕ) : Prop :=
  ∀ x ∈ K, ∀ r : ℝ, 0 < r →
    ∃ centers : Finset B, (∀ c ∈ centers, c ∈ K) ∧ centers.card ≤ bound ∧
      ∀ y ∈ K, dist y x < r → ∃ c ∈ centers, dist y c < r / 2

                                                                                    
end CompactBanach
end

end OAI


