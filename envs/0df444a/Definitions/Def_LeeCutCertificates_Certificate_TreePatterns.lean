-- Prove2me | Definitions.Def_LeeCutCertificates_Certificate_TreePatterns
-- name    : LeeCutCertificates_Certificate_TreePatterns
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:46:01.181808+00:00
-- url     : https://prove2.me/theorems/25e40e1f-11b0-4e2c-9a36-96c94343faa4
-- title:
--   Public query shores determined by a labelled tree
-- statement:
--   Label $V$ by $0,\ldots,n-1$ and give distinct pairs the fixed signed costs $a_{uv}=2^{un+v}$ for $u<v$, $a_{vu}=-a_{uv}$, and $a_{uu}=0$. For a spanning tree $T$ of the complete graph, let $p_T$ be the normalized potential with $p_T(0)=0$ and $p_T(u)-p_T(v)=a_{uv}$ on its edges. Put $\rho_T(u,v)=a_{uv}-p_T(u)+p_T(v)$ and
--
--   $$O_T(v)=\{u\ne v:uv\notin T,\ \rho_T(v,u)<0\}.$$
--
--   The tree query family contains every singleton shore, the two-endpoint shore of each tree edge, and $O_T(v)$ and $O_T(v)\cup\{v\}$ for each vertex $v$. The family depends only on the tree and vertex labels. It is the specific family in the first clause of Lemma 2, with its cardinality and certificate soundness left to that theorem.
--
--   **Formalization Note** Trees are Mathlib simple graphs on all of `Fin n`; they have no support relationship to the input graph, so zero-capacity pairs can be tree edges. The normalized potential is selected from its defining equations using classical choice; on trees the solution is unique. On an inconsistent system for a non-tree input, the function returns zero. Only spanning trees with $n\ge2$ are used by the theorem. Unions of finite families remove duplicate shores automatically; neither a query budget nor certificate soundness is bundled into a tree or potential validity assumption.
-- source:
--   Troy Lee, Finding and Certifying Weighted Minimum Cuts with Cut Queries, STOC 2027 submission #474 (October 2026), §7.1, fixed costs, normalized potentials, outgoing sets and query family, printed pp.18–19 (PDF pp.19–20); pinned PDF sha256 853e2745e72c36e8e0567917faa6eedd8dfe99b4078a34a70d8d4b81516c372d (citation_basis: published, submission artifact, not an acceptance claim).

import Mathlib
import Definitions.Def_LeeCutCertificates_Certificate_Flows

set_option autoImplicit false
open SunMinCut.Cactus
open Classical

namespace LeeCutCertificates.Certificate

/-- Fixed signed pair costs of §7.1, independent of graph capacities and divergence. -/
def pairCost {n : ℕ} (u v : Fin n) : ℝ :=
  if u < v then (2 : ℝ) ^ (u.val * n + v.val)
  else if v < u then -((2 : ℝ) ^ (v.val * n + u.val)) else 0

/-- The normalized potential specified by the tree equations. The zero fallback
only makes this total on non-trees; the lemma uses spanning trees on n ≥ 2 vertices. -/
noncomputable def treePotential {n : ℕ} (T : SimpleGraph (Fin n)) : Fin n → ℝ :=
  if h : ∃ p : Fin n → ℝ, (∀ v, v.val = 0 → p v = 0) ∧
      ∀ u v, T.Adj u v → p u - p v = pairCost u v
  then Classical.choose h else fun _ => 0

/-- Reduced pair cost determined by the labelled tree. -/
noncomputable def reducedCost {n : ℕ} (T : SimpleGraph (Fin n)) (u v : Fin n) : ℝ :=
  pairCost u v - treePotential T u + treePotential T v

/-- Prescribed outgoing non-tree neighbors; a negative reduced cost means saturation outward. -/
noncomputable def outgoing {n : ℕ} (T : SimpleGraph (Fin n)) (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun u => u ≠ v ∧ ¬ T.Adj v u ∧ reducedCost T v u < 0

/-- Singletons, tree endpoint pairs, and O_T(v), O_T(v) ∪ {v}.
A simple graph on the full Fin n carrier is a subgraph of the complete labelled graph;
no relation to the support of the input is imposed. -/
noncomputable def treeQueries {n : ℕ} (T : SimpleGraph (Fin n)) : Finset (Finset (Fin n)) :=
  (Finset.univ.image fun v : Fin n => ({v} : Finset (Fin n))) ∪
  ((Finset.univ.filter fun uv : Fin n × Fin n => T.Adj uv.1 uv.2).image
    fun uv => ({uv.1, uv.2} : Finset (Fin n))) ∪
  (Finset.univ.biUnion fun v : Fin n => ({outgoing T v, insert v (outgoing T v)} :
    Finset (Finset (Fin n))))

end LeeCutCertificates.Certificate


