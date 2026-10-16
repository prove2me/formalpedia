-- Prove2me | Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteCoupling
-- name    : OAI_Combinatorics_CliqueFree_FiniteCoupling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:06:20.67349+00:00
-- url     : https://prove2.me/theorems/a800e4a9-e0fa-4fdc-850c-4f3f4e00dd3a
-- title:
--   Finite probability vectors, total variation, pushforwards, mixtures and failure indicators
-- statement:
--   Let $I$ and $J$ be finite sets. The file defines the following elementary objects for finite couplings.
--
--   1. **Probability vector:** $p\in\mathbb{R}^I$ with $p_i\ge 0$ for all $i$ and $\sum_{i\in I}p_i=1$.
--
--   2. **Total variation distance** $d_{\mathrm{TV}}(p,q)=\tfrac12\sum_{i\in I}|p_i-q_i|$.
--
--   3. **Pushforward** of $p$ along a map $f:I\to J$, evaluated at $y\in J$:
--
--      $$(f_{*}p)(y)=\sum_{i\in I,\ f(i)=y}p_i .$$
--
--   4. **Mixture** of a family of vectors $Q(i,\cdot)\in\mathbb{R}^J$ with weights $p\in\mathbb{R}^I$:
--
--      $$(pQ)(y)=\sum_{i\in I}p_i\,Q(i,y),\qquad y\in J .$$
--
--   5. **Failure indicator** of a proposition $A$: the number $0$ if $A$ holds and $1$ otherwise.
--
--   These are the primitives of finite coupling constructions. In the surrounding development they are used to build a joint law of a random function $f:I\to J$ whose marginal at each $i$ is a prescribed probability vector $p_i$ on $J$ and in which $f(i)\ne f(j)$ with probability at most $2d/(1+d)$, where $d=d_{\mathrm{TV}}(p_i,p_j)$; the failure indicator counts the weighted triangles destroyed by such a random choice in vertex splitting.
--
--   **Formalization Note** In Lean, `FiniteCoupling.Law p` is a `Prop` (despite its name) asserting that `p` is a probability vector; the other definitions are `dist`, `push p f y`, `mix p q y` and `bad P`. A third finite type `E` with a classical decidable-equality instance appears in the variable context of the file but is not used by these definitions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/FiniteCoupling.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/FiniteCoupling.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_CliqueFree_Splitting
import Definitions.Def_OAI_Combinatorics_CliqueFree_Reach
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteKernel
import Definitions.Def_OAI_Combinatorics_CliqueFree_LocalWalk
import Definitions.Def_OAI_Combinatorics_CliqueFree_WalkEntropy

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence

universe u v

namespace FiniteCoupling
universe z
variable {I : Type u} {J : Type v} {E : Type z}
variable [Fintype I] [Fintype J] [Fintype E]
local instance instDecidableEq_oAI_2 : DecidableEq E := Classical.decEq E

abbrev Law (p : I → ℝ) : Prop := (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1
noncomputable def dist (p q : I → ℝ) : ℝ := (∑ i, |p i - q i|) / 2

def push (p : I → ℝ) (f : I → J) (y : J) : ℝ := ∑ i, if f i = y then p i else 0

def mix (p : I → ℝ) (q : I → J → ℝ) (y : J) : ℝ := ∑ i, p i * q i y

noncomputable def bad (p : Prop) : ℝ := if p then 0 else 1

end FiniteCoupling

end CliqueFreeIndependence

end

end OAI


