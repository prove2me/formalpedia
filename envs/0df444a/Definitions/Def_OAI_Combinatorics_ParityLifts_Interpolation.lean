-- Prove2me | Definitions.Def_OAI_Combinatorics_ParityLifts_Interpolation
-- name    : OAI_Combinatorics_ParityLifts_Interpolation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:26:08.97159+00:00
-- url     : https://prove2.me/theorems/224047be-d547-46c6-9a97-98db97d3474a
-- title:
--   Replacement sums: algebraic counterparts of the separate and joint refinement steps
-- statement:
--   Let $G$ and $H$ be simple graphs on finite sets $V$ and $W$, and let $\mathcal T_k=V^k\sqcup W^k$ be the set of $k$-tuples of either graph. For a tuple $x$ of one of the graphs, an index $i<k$ and a vertex $y$ of the same graph, $x[i\mapsto y]$ is the tuple obtained from $x$ by replacing its $i$-th entry by $y$.
--
--   1. **Replacement sum.** For $i\in\{0,\dots,k-1\}$ and $f:\mathcal T_k\to\mathbb{Q}$,
--   $$
--   (\Sigma^{\mathrm{rep}}_i f)(x)=\sum_{y\in V}f(x[i\mapsto y])\quad(x\in V^k),\qquad(\Sigma^{\mathrm{rep}}_i f)(x)=\sum_{y\in W}f(x[i\mapsto y])\quad(x\in W^k).
--   $$
--
--   2. **Replacement embedding.** For $i<k$, the map $\iota_i:\{0,\dots,k-1\}\to\{0,\dots,k\}$ sends $i$ to the new last index $k$ and fixes every $j\neq i$. If $(x,y)$ denotes the $(k+1)$-tuple extending $x$ by $y$ in the last position, then $(x,y)\circ\iota_i=x[i\mapsto y]$.
--
--   3. **Joint replacement sum.** For a family $f_0,\dots,f_{k-1}:\mathcal T_k\to\mathbb{Q}$,
--   $$
--   J(f_0,\dots,f_{k-1})(x)=\sum_{y}\ \prod_{i=0}^{k-1}f_i(x[i\mapsto y]),
--   $$
--   where $y$ ranges over $V$ for $x\in V^k$ and over $W$ for $x\in W^k$.
--
--   These operators are the algebraic counterparts of the two Weisfeiler–Leman refinement steps used in the parity reduction. If $f$ is the indicator of a colour class, then $\Sigma^{\mathrm{rep}}_if(x)$ counts the vertices $y$ for which $x[i\mapsto y]$ lies in that class, as in the separate refinement. If each $f_i$ is the indicator of a class $d_i$, then $J(f_0,\dots,f_{k-1})(x)$ counts the vertices $y$ for which the whole vector of colours of $x[0\mapsto y],\dots,x[k-1\mapsto y]$ equals $(d_0,\dots,d_{k-1})$, as in the joint refinement. The embedding $\iota_i$ is used to realize the joint replacement sum by passing to $(k+1)$-tuples, multiplying, and summing out the last entry.
--
--   **Formalization Note** The definitions are `replacementSum`, `replaceEmbedding` (built from `Fin.last k` and `Fin.castSucc`) and `jointReplacementSum`; $x[i\mapsto y]$ is `Function.update x i y`, and functions on $\mathcal T_k$ are functions on `TuplePair V W k`. That these operators preserve the span of rooted test counts is proved in separate results.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/Interpolation.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/Interpolation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ParityLifts mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
import Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual
import Definitions.Def_OAI_Combinatorics_ParityLifts_Masses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BaseLabels
import Definitions.Def_OAI_Combinatorics_ParityLifts_BalancedBags
import Definitions.Def_OAI_Combinatorics_ParityLifts_DecompositionCuts
import Definitions.Def_OAI_Combinatorics_ParityLifts_Witnesses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BagTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_TagSizes
import Definitions.Def_OAI_Combinatorics_ParityLifts_Detection
import Definitions.Def_OAI_Combinatorics_ParityLifts_RankedTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_RootedTests
import Definitions.Def_OAI_Combinatorics_ParityLifts_GlueTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_GlueVertices
import Definitions.Def_OAI_Combinatorics_ParityLifts_Rerooting
import Definitions.Def_OAI_Combinatorics_ParityLifts_TestAlgebra

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace ParityWL

open scoped BigOperators

section FiniteInterpolation

open scoped Classical

end FiniteInterpolation

section RefinementOperators

open scoped Classical

variable {V W : Type} [Fintype V] [Fintype W]
variable (G : SimpleGraph V) (H : SimpleGraph W)

noncomputable def replacementSum {k : ℕ} (i : Fin k) (f : TuplePair V W k → ℚ) :
    TuplePair V W k → ℚ :=
  Sum.elim (fun x => ∑ y : V, f (.inl (Function.update x i y)))
    (fun x => ∑ y : W, f (.inr (Function.update x i y)))

def replaceEmbedding {k : ℕ} (i j : Fin k) : Fin (k + 1) :=
  if j = i then Fin.last k else j.castSucc

noncomputable def jointReplacementSum {k : ℕ} (f : Fin k → TuplePair V W k → ℚ) :
    TuplePair V W k → ℚ :=
  Sum.elim (fun x => ∑ y : V, ∏ i : Fin k, f i (.inl (Function.update x i y)))
    (fun x => ∑ y : W, ∏ i : Fin k, f i (.inr (Function.update x i y)))

end RefinementOperators

end ParityWL

end OAI


