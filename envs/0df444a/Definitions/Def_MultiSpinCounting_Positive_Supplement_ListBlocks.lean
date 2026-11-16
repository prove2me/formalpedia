-- Prove2me | Definitions.Def_MultiSpinCounting_Positive_Supplement_ListBlocks
-- name    : MultiSpinCounting_Positive_Supplement_ListBlocks
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:23:22.704206+00:00
-- url     : https://prove2.me/theorems/b18fe1ca-4071-4d16-9a53-8c71f78f5cf3
-- title:
--   List-coloring instances, permissive blocks and block marginals
-- statement:
--   A list-coloring instance $\Phi$ has a finite simple graph $G_\Phi$ and a list $L_\Phi(v)\subseteq[q]$ at each vertex. Its proper list-colorings are the published set
--   $$\Omega(\Phi)=\{x: x_v\in L_\Phi(v),\ x_u\ne x_v\text{ on every edge}\}.$$
--   Feasibility means $\Omega(\Phi)\ne\varnothing$. A proper partial list-coloring on $B$ is a proper list-coloring of the induced graph on $B$, with the restricted lists; extendability is not assumed.
--   The edge boundary is $\partial_E B=\{(u,v):u\in B,v\notin B,uv\in E(G_\Phi)\}$. A block $B$ is permissive when its induced graph is connected and every $(u,v)\in\partial_E B$ satisfies $|L_\Phi(v)|>\deg_{G_\Phi}(v)+1$. For a partial coloring $\sigma$ on $B$ the uniform marginal is
--   $$\mu_\Phi(B\leftarrow\sigma)=\frac{|\{x\in\Omega(\Phi):x|_B=\sigma\}|}{|\Omega(\Phi)|}.$$
--   The graph and lists belong to the current instance. The boundary counts edges once, oriented from inside to outside. These are the objects of Proposition 5.2.
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #268 (October 2026), p. 18–19, §5.1; Proposition 5.2

import Mathlib
import Definitions.Def_ConeL2G_properColorings

noncomputable section
open scoped Classical

namespace MultiSpinCounting.Positive.Supplement

/-- A list-coloring instance on its actual vertex carrier (§5.1). -/
structure ListInstance (n q : ℕ) where
  graph : SimpleGraph (Fin n)
  lists : Fin n → Finset (Fin q)

/-- Reuse the published general proper-list-coloring set. -/
def listColorings {n q : ℕ} (Φ : ListInstance n q) : Finset (Fin n → Fin q) :=
  ConeL2G.properColorings Φ.graph Φ.lists

def Feasible {n q : ℕ} (Φ : ListInstance n q) : Prop := (listColorings Φ).Nonempty

/-- Proper on B only; extendability is a conclusion of Proposition 5.2. -/
def PartialProper {n q : ℕ} (Φ : ListInstance n q) (B : Finset (Fin n))
    (σ : B → Fin q) : Prop :=
  σ ∈ ConeL2G.properColorings (Φ.graph.induce (↑B : Set (Fin n)))
    (fun v => Φ.lists v.val)

/-- Exactly one orientation of each crossing edge, from inside to outside. -/
def boundaryEdges {n q : ℕ} (Φ : ListInstance n q) (B : Finset (Fin n)) :
    Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun e => e.1 ∈ B ∧ e.2 ∉ B ∧ Φ.graph.Adj e.1 e.2)

/-- The degree and lists are those of the current graph, not the original graph. -/
def Permissive {n q : ℕ} (Φ : ListInstance n q) (B : Finset (Fin n)) : Prop :=
  (Φ.graph.induce (↑B : Set (Fin n))).Connected ∧
  ∀ e ∈ boundaryEdges Φ B, Φ.graph.degree e.2 + 1 < (Φ.lists e.2).card

/-- Uniform Gibbs marginal on Ω(Φ). Feasible instances have a positive denominator. -/
def blockMarginal {n q : ℕ} (Φ : ListInstance n q) (B : Finset (Fin n))
    (σ : B → Fin q) : ℝ :=
  (((listColorings Φ).filter (fun τ => ∀ u : B, τ u.val = σ u)).card : ℝ) /
    (listColorings Φ).card

end MultiSpinCounting.Positive.Supplement


