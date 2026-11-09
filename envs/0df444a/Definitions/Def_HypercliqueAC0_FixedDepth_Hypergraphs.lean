-- Prove2me | Definitions.Def_HypercliqueAC0_FixedDepth_Hypergraphs
-- name    : HypercliqueAC0_FixedDepth_Hypergraphs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T19:09:14.942466+00:00
-- url     : https://prove2.me/theorems/b91a35d9-26dd-4dc2-8a85-133ba83ad99b
-- title:
--   Edge variables, hypercliques, planting, and the constant $c_r$
-- statement:
--   Let $m,r,\ell$ be natural numbers. Vertices are the elements of a set of size $m$, and an edge is an $r$-element subset. An input $x$ assigns a Boolean value to each edge. The hyperclique function is
--
--   $$\ell\text{-}\mathsf{Clique}^r_m(x)=1\iff \exists Q\subseteq[m],\ |Q|=\ell,\ \forall e\subseteq Q,\ |e|=r\Rightarrow x_e=1.$$
--
--   A hypergraph records its vertex set as well as its edge set. The complete hypergraph $K_B$ retains every vertex of $B$, even when $|B|<r$ and there are no edges. Unions combine both vertex and edge sets. The vertices touched by a set of edges are their union. Relabeling a hypergraph on $v$ labeled vertices along an injection retains all $v$ vertices. Planting $K_A$ in $G$ adds every edge inside $A$.
--
--   The good planting event says both that every $\ell$-hyperclique of $G\cup K_A$ equals $A$ and that each vertex of $A$ belongs to an edge of $K_A$ absent from $G$. For $r\ge2$ the exponent constant is
--
--   $$c_r=\left(1-\frac1r\right)r^{-1/(r-1)}.$$
--
--   These definitions supply the combinatorial objects used throughout the mission.
--
--   **Formalization Note** $[m]$ is represented by `Fin m`, with labels starting at zero; changing the labels preserves every instance. No condition $r\le\ell$ or $\ell\le m$ is built into the Boolean function. The constant uses the printed closed form, rather than a real supremum.
-- source:
--   Nikolai Chukhin, Exhaustive Search Is Hard to Beat in Constant Depth for Hyperclique and Orthogonal Vectors, STOC 2027 submission #830 (October 2026), source.pdf SHA-256 bd73fd887fe562527226e0ea2da24a55552a73cf89c2e90406a28965424a12de, p.18 (PDF p.20), §1.3 p.4 (PDF p.6), §4.1 p.13 (PDF p.15), Lemma 4.6 and §5 definition of c_r; explicit definition: For an integer $r \ge 2$, put $c_r = \max_{\gamma \ge 0}(\gamma - \gamma^r) = (1 - 1/r)r^{-1/(r-1)}$.

import Mathlib

noncomputable section
namespace HypercliqueAC0.FixedDepth
attribute [local instance] Classical.propDecidable Classical.decEq

/-- The r-element subsets of the m vertices. -/
abbrev Edge (m r : ℕ) := {e : Finset (Fin m) // e.card = r}

/-- The Boolean hyperclique function, including the usual empty-range conventions. -/
def hyperclique (m r ℓ : ℕ) (x : Edge m r → Bool) : Bool :=
  decide (∃ Q : Finset (Fin m), Q.card = ℓ ∧ ∀ e : Edge m r, e.val ⊆ Q → x e = true)

/-- The explicit constant printed above Theorem 5.1. -/
def c (r : ℕ) : ℝ := (1 - 1 / (r : ℝ)) * (r : ℝ) ^ (-(1 : ℝ) / ((r : ℝ) - 1))

/-- Vertex sets are retained even when they contain isolated vertices. -/
structure Hypergraph (m r : ℕ) where
  vertices : Finset (Fin m)
  edges : Finset (Edge m r)
  supported : ∀ e ∈ edges, e.val ⊆ vertices

/-- The complete r-uniform hypergraph on B. -/
def complete {m : ℕ} (r : ℕ) (B : Finset (Fin m)) : Hypergraph m r where
  vertices := B
  edges := Finset.univ.filter (fun e => e.val ⊆ B)
  supported := by simp

/-- Union includes both vertex sets, rather than just vertices lying on edges. -/
def hypergraphUnion {m r : ℕ} (H J : Hypergraph m r) : Hypergraph m r where
  vertices := H.vertices ∪ J.vertices
  edges := H.edges ∪ J.edges
  supported := by
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact (H.supported e he).trans Finset.subset_union_left
    · exact (J.supported e he).trans Finset.subset_union_right

/-- Vertices touched by a set of edge variables. -/
def verticesOf {m r : ℕ} (E : Finset (Edge m r)) : Finset (Fin m) :=
  E.biUnion (fun e => e.val)

/-- Relabel an edge along an injection. -/
def mapEdge {v m r : ℕ} (ι : Fin v ↪ Fin m) (e : Edge v r) : Edge m r :=
  ⟨e.val.map ι, by simpa using e.property⟩

/-- H₀ has all v labeled vertices, including its isolated ones. -/
def imageHypergraph {v m r : ℕ} (H₀ : Finset (Edge v r)) (ι : Fin v ↪ Fin m) :
    Hypergraph m r where
  vertices := Finset.univ.map ι
  edges := H₀.image (mapEdge ι)
  supported := by
    intro e he
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
    exact Finset.map_subset_map.mpr (Finset.subset_univ _)

/-- The planted input G ∪ K_A. -/
def plant {m r : ℕ} (G : Edge m r → Bool) (A : Finset (Fin m)) : Edge m r → Bool :=
  fun e => G e || decide (e.val ⊆ A)

/-- Both clauses of the good event of Lemma 4.6. -/
def plantedGood {m r : ℕ} (ℓ : ℕ) (A : Finset (Fin m)) (G : Edge m r → Bool) : Prop :=
  (∀ Q : Finset (Fin m), Q.card = ℓ →
    (∀ e : Edge m r, e.val ⊆ Q → plant G A e = true) → Q = A) ∧
  (∀ u ∈ A, ∃ e : Edge m r, e.val ⊆ A ∧ u ∈ e.val ∧ G e = false)

end HypercliqueAC0.FixedDepth


