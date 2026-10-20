-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingEntropy_MinimalFace
-- name    : OAI_Combinatorics_MatchingEntropy_MinimalFace
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:39:41.838432+00:00
-- url     : https://prove2.me/theorems/7e6fdf88-9d83-4b9f-91eb-2b32afa80527
-- title:
--   Fractional coordinates of an edge vector
-- statement:
--   Let $E$ be a set (in applications, the edge set of a multigraph) and $x\in\mathbb{R}^E$. An index $e\in E$ is *fractional* for $x$ if
--   $$
--   0<x_e<1 .
--   $$
--
--   For a point $x$ of the perfect matching polytope of a loopless multigraph with edge set $E$ (the convex hull of the indicator vectors of perfect matchings), every coordinate lies in $[0,1]$, so the non-fractional edges are exactly those with $x_e\in\{0,1\}$. On these edges every random perfect matching with edge marginals $x$ behaves deterministically: it contains $e$ with probability one if $x_e=1$ and avoids $e$ with probability one if $x_e=0$. The fractional edges carry all the remaining freedom, and they span the subgraph on which the face structure of the polytope around $x$ is studied.
--
--   **Formalization Note** The predicate is `IsFractional x e`, a proposition about a function `x : E → ℝ` and an index `e`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingEntropy/MinimalFace.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingEntropy/MinimalFace.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TriangleFace mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TriangleFace
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Model
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Simplex
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Coupling
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Basic
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_OddCuts
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Contraction
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Polytope
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Face
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Entropy
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Duality
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_EdgeReduction

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds.Refined

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def IsFractional (x : E → ℝ) (e : E) : Prop := 0 < x e ∧ x e < 1

end MatchingEntropyBounds.Refined

end

end OAI


