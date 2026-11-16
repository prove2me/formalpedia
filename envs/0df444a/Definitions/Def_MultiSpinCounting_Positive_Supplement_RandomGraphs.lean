-- Prove2me | Definitions.Def_MultiSpinCounting_Positive_Supplement_RandomGraphs
-- name    : MultiSpinCounting_Positive_Supplement_RandomGraphs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:24:08.948404+00:00
-- url     : https://prove2.me/theorems/2da02e52-3132-4016-84a4-66e5613c3814
-- title:
--   Exceptional components and weighted ordered simple paths
-- statement:
--   For a simple graph $G$ on $n$ labeled vertices, use the §5 parameters $D=\lfloor(d+q)/3\rfloor$ and $\gamma=(q-D-1)^{-1}$. Define the exceptional vertices and their induced graph by
--   $$H_D=\{v:\deg_G(v)>D\},\qquad G[H_D].$$
--   Each connected component is represented by its full vertex set in the original graph. In particular, incident volumes use degrees in $G$.
--   Give a vertex weight $w(v)=\gamma$ when $\deg_G(v)\le D$, and $w(v)=1$ otherwise. For length $\ell$, define
--   $$W_\ell(G)=\sum_{(v_0,\ldots,v_\ell)\text{ ordered simple path}}\ \prod_{i=1}^{\ell}w(v_i).$$
--   The vertices are distinct, adjacent successive vertices form edges, and the weight excludes $v_0$. Both orientations of each undirected path occur. The published Erdős–Rényi law assigns each unordered pair an edge independently with probability $d/n$; it is used without redefining the probability space. These objects supply Lemmas 5.8–5.10.
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #268 (October 2026), p. 23–26, (5.11); §5.3.1; Lemmas 5.8–5.10

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting
import Definitions.Def_MultiSpinCounting_Positive_Supplement_Parameters

noncomputable section
open scoped Classical

namespace MultiSpinCounting.Positive.Supplement

/-- (5.11), degree in the original whole graph. -/
def exceptional {n : ℕ} (G : SimpleGraph (Fin n)) (d : ℝ) (q : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => (Dcut d q : ℝ) < (G.degree v : ℝ))

def exceptionalGraph {n : ℕ} (G : SimpleGraph (Fin n)) (d : ℝ) (q : ℕ) :=
  G.induce (↑(exceptional G d q) : Set (Fin n))

/-- Component carrier projected back to the original vertex labels. -/
def componentVertices {n : ℕ} (G : SimpleGraph (Fin n)) (d : ℝ) (q : ℕ)
    (C : (exceptionalGraph G d q).ConnectedComponent) : Finset (Fin n) :=
  C.supp.toFinset.image Subtype.val

/-- §5.3.1. -/
def vertexWeight {n : ℕ} (G : SimpleGraph (Fin n)) (d : ℝ) (q : ℕ) (v : Fin n) : ℝ :=
  if (G.degree v : ℝ) ≤ Dcut d q then gamma5 d q else 1

/-- Ordered simple paths, weighted at v₁,…,v_ℓ, excluding v₀. -/
def pathWeight {n : ℕ} (G : SimpleGraph (Fin n)) (d : ℝ) (q ℓ : ℕ) : ℝ :=
  ∑ f ∈ Finset.univ.filter (fun f : Fin (ℓ + 1) → Fin n =>
    Function.Injective f ∧ ∀ i : Fin ℓ, G.Adj (f i.castSucc) (f i.succ)),
    ∏ i : Fin ℓ, vertexWeight G d q (f i.succ)

end MultiSpinCounting.Positive.Supplement


