-- Prove2me | Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
-- name    : OAI_Combinatorics_CliqueFree_Optimizer
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T20:42:45.678991+00:00
-- url     : https://prove2.me/theorems/95e2a360-e72c-49d3-86ad-f2fb0192005d
-- title:
--   An entropy-type vertex potential and its maximisers on the nonnegative orthant
-- statement:
--   Let $G$ be a simple graph on a finite vertex set $V$ with adjacency $u\sim v$; vectors are real functions on $V$, and $\log$ is the natural logarithm. The file defines the following.
--
--   1. **Directed bilinear edge form.** For $a,b:V\to\mathbb{R}$,
--
--      $$\mathcal{E}_G(a,b)=\sum_{u\in V}\ \sum_{v\in V,\ u\sim v}a(u)\,b(v)=a^{\top}A_G\,b,$$
--
--      where $A_G$ is the adjacency matrix. On the diagonal, $\mathcal{E}_G(w,w)=2E_w(G)$ with the edge mass $E_w(G)=\sum_{\{u,v\}\in E(G)}w(u)\,w(v)$.
--
--   2. **Spike.** For a vertex $v$ and $t\in\mathbb{R}$, the vector $t\,\mathbf{1}_{\{v\}}$, equal to $t$ at $v$ and to $0$ at every other vertex.
--
--   3. **Vertex potential** $\varphi(t)=t\,(1-\log t)$, with $\varphi(0)=0$.
--
--   4. **Potential** of a weight vector $w$:
--
--      $$\Phi_G(w)=\sum_{v\in V}w(v)\bigl(1-\log w(v)\bigr)-\sum_{\{u,v\}\in E(G)}w(u)\,w(v).$$
--
--   5. **Optimizer.** A vector $w$ is an optimizer for $G$ if $w(v)\ge 0$ for every $v$ and $\Phi_G(q)\le\Phi_G(w)$ for every $q:V\to\mathbb{R}$ with $q(v)\ge 0$ for all $v$; that is, $w$ is a global maximiser of $\Phi_G$ on the closed nonnegative orthant.
--
--   The potential is the variational functional of the argument: its supremum over nonnegative vectors is compared with the size of an independent set, and maximisers carry rigid structure. In the surrounding development it is shown that an optimizer is strictly positive and satisfies the stationarity equation $\log\bigl(1/w(v)\bigr)=\sum_{u\sim v}w(u)$, hence $w(v)\le 1$, and that on a graph without cliques of a fixed size it obeys a cross-mass bound. The bilinear form and the spikes are used to expand $\Phi_G$ around a maximiser and to perturb single coordinates.
--
--   **Formalization Note** The Lean names are `edgeForm`, `spike` (which needs decidable equality on $V$), `vertexPotential`, `potential` and `IsOptimizer`; the edge-mass term is `edgeMass G w`, half the full ordered cross mass. Mathlib's convention `Real.log 0 = 0` gives $\varphi(0)=0$, which agrees with the continuous extension of $t(1-\log t)$ at $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/Optimizer.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/Optimizer.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CliqueFreeLog mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph
universe u
variable {V : Type u} [Fintype V]

/-- The directed bilinear edge form (twice the quadratic mass on the diagonal). -/
noncomputable def edgeForm (G : SimpleGraph V) (a b : V → ℝ) : ℝ :=
  ∑ u, ∑ v, if G.Adj u v then a u * b v else 0

noncomputable def spike [DecidableEq V] (v : V) (t : ℝ) : V → ℝ := fun u ↦ if u = v then t else 0

/-- The vertex summand, with Mathlib's log(0)=0 convention. -/
def vertexPotential (t : ℝ) : ℝ := t * (1-Real.log t)

noncomputable def potential (G : SimpleGraph V) (w : V → ℝ) : ℝ :=
  ∑ v, vertexPotential (w v) - edgeMass G w

def IsOptimizer (G : SimpleGraph V) (w : V → ℝ) : Prop :=
  (∀ v, 0 ≤ w v) ∧ ∀ q : V → ℝ, (∀ v, 0 ≤ q v) → potential G q ≤ potential G w

end CliqueFreeIndependence.WeightedGraph

end

end OAI


