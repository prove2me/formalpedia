-- Prove2me | Definitions.Def_OAI_Combinatorics_CliqueFree_VertexSplitting
-- name    : OAI_Combinatorics_CliqueFree_VertexSplitting
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:08:47.829624+00:00
-- url     : https://prove2.me/theorems/2a1dfe30-0454-4c7b-8d9a-8e38174df6ae
-- title:
--   The vertex-splitting loss constant
-- statement:
--   For a real number $C$ (the constant in a cross-mass hypothesis on a vertex weight) define
--
--   $$C_{\mathrm{split}}(C)=6\bigl(C_{\mathrm{sm}}(C)+C_{\mathrm{ent}}(C)+1\bigr),$$
--
--   where $C_{\mathrm{exc}}(C)=42C^{2}+2C$, $C_{\mathrm{ent}}(C)=10+C_{\mathrm{exc}}(C)$ and $C_{\mathrm{sm}}(C)=2\sqrt{C_{\mathrm{ent}}(C)+1}$. Explicitly, with $s=42C^{2}+2C+11$ one has $C_{\mathrm{split}}(C)=6\,(s+2\sqrt{s})$.
--
--   This constant measures the relative loss of weighted triangle mass in one step of weighted vertex splitting. Here a vertex weight $w$ on a graph satisfies the cross-mass hypothesis with constant $C$ if any two vertex sets $A,B$ of weight at most $e^{x}$ (for any real $x\ge 1$) span weighted edge mass $\sum_{u\in A,\,v\in B,\,u\sim v}w(u)w(v)$ at most $C\,w(A)\bigl(x+\max\{0,\log(1/w(A))\}\bigr)$. In the surrounding development, at a scale $x\ge 32$ and under a lower bound $1/x$ on the common neighbourhood masses of adjacent pairs, a split graph keeps at least the fraction $1-C_{\mathrm{split}}(C)\log x/\sqrt{x}$ of the weighted triangle mass, while the largest weighted neighbourhood mass drops from at most $e^{x}$ to at most $e^{\sqrt{x}}$.
--
--   **Formalization Note** The Lean name is `splittingConstant C`, defined from `smoothingConstant` and `entropyConstant`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/VertexSplitting.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/VertexSplitting.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteCoupling

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

attribute [local instance 10000] edgeStateDecEq

noncomputable def splittingConstant (C : ℝ) : ℝ :=
  6 * (smoothingConstant C + entropyConstant C + 1)

end CliqueFreeIndependence.WeightedGraph

end

end OAI


