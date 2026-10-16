-- Prove2me | Definitions.Def_OAI_Combinatorics_CliqueFree_Reach
-- name    : OAI_Combinatorics_CliqueFree_Reach
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T20:55:40.151934+00:00
-- url     : https://prove2.me/theorems/479c022a-5e7c-41c7-b1ef-199ff2b21b5b
-- title:
--   Reach sets by iterated mass-threshold enlargement, bad neighbour sets and explicit constants
-- statement:
--   Let $G$ be a simple graph on a finite vertex set $V$ with adjacency $\sim$ and neighbourhoods $N(y)=\{u:\ y\sim u\}$, let $w:V\to\mathbb{R}$ be a vertex weight and write $w(A)=\sum_{v\in A}w(v)$. Let $t,b,C\in\mathbb{R}$. The file defines the following.
--
--   1. **Enlargement** of a set $A\subseteq V$ at threshold $t$:
--
--      $$\mathrm{Enl}_t(A)=A\cup\{y\in V:\ w\bigl(A\cap N(y)\bigr)\ge t\},$$
--
--      which adds every vertex having weighted neighbourhood mass at least $t$ inside $A$.
--
--   2. **Reach sets** of a vertex $v$: $R^{0}_t(v)=N(v)$ and $R^{n+1}_t(v)=\mathrm{Enl}_t\bigl(R^{n}_t(v)\bigr)$ for $n\ge 0$, an increasing sequence of sets.
--
--   3. **Bad set.** For an assignment $S$ of a set $S(v)\subseteq V$ to every vertex $v$, a threshold $b$ and a vertex $v$,
--
--      $$\mathrm{Bad}_{S,b}(v)=\{u\in N(v):\ w\bigl(S(v)\cap N(u)\bigr)>b\},$$
--
--      the neighbours of $v$ with more than $b$ weighted neighbourhood mass inside $S(v)$.
--
--   4. **Constants.** For $C\in\mathbb{R}$: $C_{\mathrm{exc}}(C)=42C^{2}+2C$, $C_{\mathrm{ent}}(C)=10+C_{\mathrm{exc}}(C)$ and $C_{\mathrm{sm}}(C)=2\sqrt{C_{\mathrm{ent}}(C)+1}$.
--
--   These objects localise a random walk inside neighbourhoods: the reach sets, taken at the threshold $t=1/(e^{x}x^{6})$ for a scale $x$ and with at most $2x$ enlargement steps, contain most of the mass of the walk. In the surrounding development, for $S(u)=R^{n}_t(u)$ and $b=x^{8}$, the cross mass $\sum_{u\in\mathrm{Bad}(v),\,z\in N(v),\,u\sim z}w(u)w(z)$ is bounded by $C_{\mathrm{exc}}(C)\,x^{-4}$ times the local triangle mass $\sum_{u\in N(v)}w(u)\,w\bigl(N(u)\cap N(v)\bigr)$ under a cross-mass hypothesis with constant $C$, and $C_{\mathrm{ent}}$ and $C_{\mathrm{sm}}$ are the constants of the entropy and smoothing estimates for the walk.
--
--   **Formalization Note** The Lean names are `enlarge G w t A`, `reach G w t v n`, `badSet G w S b v`, `exceptionalConstant`, `entropyConstant` and `smoothingConstant`. The enlargement uses the non-strict inequality $t\le w(A\cap N(y))$, the bad set the strict inequality $b<w(S(v)\cap N(u))$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/Reach.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/Reach.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

attribute [local instance 10000] edgeStateDecEq

/-- Whole-graph sets that contain most of the walk. -/
noncomputable def enlarge (G : SimpleGraph V) (w : V → ℝ) (t : ℝ) (A : Finset V) : Finset V :=
  A ∪ univ.filter (fun y ↦ t ≤ mass w (A ∩ neighbors G y))

noncomputable def reach (G : SimpleGraph V) (w : V → ℝ) (t : ℝ) (v : V) : ℕ → Finset V
  | 0 => neighbors G v
  | n+1 => enlarge G w t (reach G w t v n)

noncomputable def badSet (G : SimpleGraph V) (w : V → ℝ) (S : V → Finset V)
    (b : ℝ) (v : V) : Finset V :=
  (neighbors G v).filter (fun u ↦ b < mass w (S v ∩ neighbors G u))

noncomputable def exceptionalConstant (C : ℝ) : ℝ := 42 * C ^ 2 + 2 * C
noncomputable def entropyConstant (C : ℝ) : ℝ := 10 + exceptionalConstant C
noncomputable def smoothingConstant (C : ℝ) : ℝ := 2 * Real.sqrt (entropyConstant C + 1)

end CliqueFreeIndependence.WeightedGraph

end

end OAI


