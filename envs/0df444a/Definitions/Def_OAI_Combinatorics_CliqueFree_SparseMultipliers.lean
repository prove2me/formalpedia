-- Prove2me | Definitions.Def_OAI_Combinatorics_CliqueFree_SparseMultipliers
-- name    : OAI_Combinatorics_CliqueFree_SparseMultipliers
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T20:48:18.241663+00:00
-- url     : https://prove2.me/theorems/e345a63d-238b-445a-b0ae-a2f2d08eb44c
-- title:
--   The multiplier bound $b_{k+2}(\varepsilon)=2^{(k+2)k}/\varepsilon^{k}$
-- statement:
--   For a natural number $k$ and a real number $\varepsilon$ define
--
--   $$b_{k+2}(\varepsilon)=\frac{2^{(k+2)k}}{\varepsilon^{k}} .$$
--
--   The index $k+2$ is the size of the excluded clique, so $k$ is its excess over $2$. For $k=0$ the bound is $b_2(\varepsilon)=1$, and for fixed $k\ge 1$ it grows like $\varepsilon^{-k}$ as $\varepsilon\to 0^{+}$.
--
--   This is the uniform upper bound on multipliers in a sparse-multiplier lemma of the surrounding development: if a graph $G$ on a finite set $V$ has no clique of size $k+2$ inside a set $A\subseteq V$, $w:V\to\mathbb{R}$ is positive and $0<\varepsilon\le\tfrac12$, then there is a finitely supported random multiplier vector $m:V\to[0,b_{k+2}(\varepsilon)]$, vanishing outside $A$, with $\mathbb{E}[m(v)]=1$ for $v\in A$, whose expected weighted edge mass $\mathbb{E}\bigl[\sum_{\{u,v\}\in E(G)}w(u)m(u)\,w(v)m(v)\bigr]$ is at most $\varepsilon\,w(A)^2$, where $w(A)=\sum_{v\in A}w(v)$. In later estimates the bound enters only through logarithms, and $\log b_{k+2}(\varepsilon)=k(k+2)\log 2+k\log(1/\varepsilon)$.
--
--   **Formalization Note** The Lean name is `multiplierBound k ε`. For $\varepsilon=0$ and $k\ge 1$ Lean's convention for division by zero gives the value $0$; this case is excluded in the applications, which take $\varepsilon>0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/SparseMultipliers.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/SparseMultipliers.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph
open Lottery
universe u
variable {V : Type u} [Fintype V]

/-- The bound `b_(k+2)(ε)`, indexed by the excess clique size. -/
noncomputable def multiplierBound (k : ℕ) (ε : ℝ) : ℝ := 2^((k+2)*k) / ε^k

end CliqueFreeIndependence.WeightedGraph

end

end OAI


