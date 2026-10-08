-- Prove2me | Definitions.Def_EdmondsMatching65_Polyhedron_BlossomSequence
-- name    : EdmondsMatching65_Polyhedron_BlossomSequence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T14:24:12.930451+00:00
-- url     : https://prove2.me/theorems/9bb5132b-44e1-4677-81d6-474eb170bbbc
-- title:
--   The sequence {G_i} of Theorem (M): shrinking blossoms with node and edge weights, conditions (a)–(k)
-- statement:
--   Let $G$ be a finite graph with real edge weights $c$ and a matching $M$. A **sequence $\{G_i\}$, $i=0,\dots,n$**, as in Edmonds' Theorem (M), consists of graphs $G_i$, each with a matching $M_i$, a weight $w(e^i)$ on each edge $e^i$ of $G_i$ and a weight $w(v^i)$ on each node $v^i$ of $G_i$, such that:
--
--   - (a) $G_0=G$ with edge weights $w(e)=c_e$ and $M_0=M$;
--   - (b) $w(v^i)\ge0$ for every node of $G_i$ and $w(v^i_1)+w(v^i_2)\ge w(e^i)$ for every edge $e^i$ of $G_i$ with ends $v^i_1,v^i_2$;
--   - (c) for $i<n$, $G_i$ contains a circuit (simple closed path) $B_i$, the **blossom**, with $2a_i+1$ edges, $a_i$ of them in $M_i$;
--   - (d) $w(v^i_1)+w(v^i_2)=w(e^i)$ for each edge $e^i$ of $B_i$;
--   - (e) a node of $B_i$ meeting no edge of $M_i$ has the smallest weight $w(q^i)$ in $B_i$;
--   - (f) $G_{i+1}$ is obtained by shrinking $B_i$, with all edges having both ends in $B_i$, to a single node $u^{i+1}$, which becomes the end of the edges having one end in $B_i$; $M_{i+1}=M_i\cap G_{i+1}$;
--   - (g) weights in $G_{i+1}$ equal those in $G_i$ except at $u^{i+1}$ and on edges meeting $u^{i+1}$;
--   - (h) $w(u^{i+1})\le w(q^i)$, where $w(q^i)$ is the minimum node weight on $B_i$;
--   - (i) every edge $e^{i+1}$ meeting $u^{i+1}$, coming from an edge $e^i$ of $G_i$ that meets the node $v^i$ of $B_i$, has
--   $$w(e^{i+1})=w(e^i)-w(v^i)+w(q^i);$$
--   - (j) $w(v^n_1)+w(v^n_2)=w(e^n)$ for every $e^n\in M_n$;
--   - (k) every node of $G_n$ meeting no edge of $M_n$ has weight $0$.
--
--   This structure is the combinatorial certificate of optimality produced by Edmonds' weighted matching algorithm; Theorem (M) states that it exists exactly for maximum matchings.
--
--   **Formalization Note** Each contracted graph $G_i$ is represented by a partition of the original node set into *blocks*: a node of $G_i$ is the set of original nodes absorbed into it, $G_0$ has the singleton blocks, and an original edge is an edge of $G_i$ exactly when its two ends lie in different blocks (its ends in $G_i$ are those blocks). The blossom $B_i$ is listed as distinct blocks $X_{i,0},\dots,X_{i,2a_i}$ with edges $f_{i,j}$ of $G_i$ joining $X_{i,j}$ and $X_{i,j+1\bmod 2a_i+1}$. Each $M_i$ is required to be a matching **of $G_i$** (its edges are edges of $G_i$ and no block meets two of them), as the page says. The minimum $w(q^i)$ is a finite minimum over the blossom's nodes. Weights of non-nodes and non-edges of $G_i$ are unconstrained and never read.
-- source:
--   Edmonds, Maximum Matching and a Polyhedron With 0,1-Vertices, J. Res. NBS 69B (1965), p. 127, §4, Theorem (M), conditions (a)–(k); §5 (nodes absorbed into the nodes of B_i)

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph

namespace EdmondsMatching65.Polyhedron

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-! A contracted graph `Gᵢ` of Theorem (M) (§4, p. 127) is encoded by a partition `B` of the nodes
of `G` into *blocks*: each node of `Gᵢ` is the block of original nodes that has been absorbed into it
(§5, p. 127). An edge `e` of `G` is an edge of `Gᵢ` iff no block contains both of its ends, and its
ends in `Gᵢ` are the blocks containing its two ends in `G`. -/

/-- `e` is an edge of the contracted graph with blocks `B`: no block of `B` contains both ends of
`e`. -/
def IsContractedEdge (G : Graph V E) (B : Finset (Finset V)) (e : E) : Prop :=
  ∀ X ∈ B, G.ends e ∉ X.sym2

instance (G : Graph V E) (B : Finset (Finset V)) (e : E) :
    Decidable (IsContractedEdge G B e) := by
  unfold IsContractedEdge; infer_instance

/-- The edge `e` meets the block `X` (in the contracted graph): some end of `e` lies in `X`. -/
def Meets (G : Graph V E) (e : E) (X : Finset V) : Prop :=
  ∃ v ∈ X, v ∈ G.ends e

/-- The edge `e` joins the blocks `X` and `Y`: one end of `e` lies in `X` and the other in `Y`. -/
def Joins (G : Graph V E) (e : E) (X Y : Finset V) : Prop :=
  ∃ a ∈ X, ∃ b ∈ Y, G.ends e = s(a, b)

/-- The nodes of `G₀ = G`: the singleton blocks `{v}`. -/
def singletonBlocks : Finset (Finset V) :=
  Finset.univ.image (fun v : V => ({v} : Finset V))

/-- A sequence `{Gᵢ}`, `i = 0, …, n`, as in Theorem (M) (Edmonds 1965, §4, p. 127), for the graph `G`
with edge weights `c` and the matching `M`. For `i ≤ n`, `Gᵢ` has node set `blocks i`, edge set the
edges of `G` with ends in different blocks, matching `mat i`, node weights `wN i` and edge weights
`wE i`. For `i < n`, the blossom `Bᵢ` is the circuit through the blocks
`X i 0, …, X i (2 aᵢ)` with edges `f i 0, …, f i (2 aᵢ)`, `f i j` joining `X i j` and
`X i (j + 1 mod 2aᵢ + 1)`. -/
structure BlossomSequence (G : Graph V E) (c : E → ℝ) (M : Finset E) where
  /-- the index of the last graph `Gₙ` -/
  n : ℕ
  /-- the nodes of `Gᵢ`, as blocks of nodes of `G` -/
  blocks : ℕ → Finset (Finset V)
  /-- the matching `Mᵢ` of `Gᵢ` -/
  mat : ℕ → Finset E
  /-- the node weights `w(vⁱ)` of `Gᵢ`, read on blocks -/
  wN : ℕ → Finset V → ℝ
  /-- the edge weights `w(eⁱ)` of `Gᵢ`, read on edges of `Gᵢ` -/
  wE : ℕ → E → ℝ
  /-- the blossom `Bᵢ` has `2 aᵢ + 1` edges -/
  a : ℕ → ℕ
  /-- the blocks (nodes of `Gᵢ`) on the blossom `Bᵢ`, in circuit order -/
  X : ℕ → ℕ → Finset V
  /-- the edges of the blossom `Bᵢ`, in circuit order -/
  f : ℕ → ℕ → E
  /-- each `Mᵢ` is a matching of `Gᵢ`: its edges are edges of `Gᵢ`, and no node of `Gᵢ` meets two
  distinct edges of `Mᵢ` -/
  mat_edges : ∀ i ≤ n, ∀ e ∈ mat i, IsContractedEdge G (blocks i) e
  mat_matching : ∀ i ≤ n, ∀ e ∈ mat i, ∀ e' ∈ mat i, e ≠ e' →
    ∀ Y ∈ blocks i, ¬ (Meets G e Y ∧ Meets G e' Y)
  /-- (a) `G₀` is `G` with edge weights `c` and matching `M₀ = M` -/
  blocks_zero : blocks 0 = singletonBlocks
  wE_zero : ∀ e, wE 0 e = c e
  mat_zero : mat 0 = M
  /-- (b) node weights are nonnegative, and `w(v₁ⁱ) + w(v₂ⁱ) ≥ w(eⁱ)` for every edge of `Gᵢ` -/
  wN_nonneg : ∀ i ≤ n, ∀ Y ∈ blocks i, 0 ≤ wN i Y
  edge_le : ∀ i ≤ n, ∀ e, IsContractedEdge G (blocks i) e →
    ∀ Y₁ ∈ blocks i, ∀ Y₂ ∈ blocks i, Joins G e Y₁ Y₂ → wE i e ≤ wN i Y₁ + wN i Y₂
  /-- (c) `Bᵢ` is a circuit of `Gᵢ` with `2 aᵢ + 1` edges, `aᵢ` of them in `Mᵢ` -/
  X_mem : ∀ i < n, ∀ j < 2 * a i + 1, X i j ∈ blocks i
  X_injective : ∀ i < n, ∀ j < 2 * a i + 1, ∀ j' < 2 * a i + 1, X i j = X i j' → j = j'
  f_edge : ∀ i < n, ∀ j < 2 * a i + 1, IsContractedEdge G (blocks i) (f i j)
  f_joins : ∀ i < n, ∀ j < 2 * a i + 1,
    Joins G (f i j) (X i j) (X i ((j + 1) % (2 * a i + 1)))
  f_mat_card : ∀ i < n,
    ((Finset.range (2 * a i + 1)).filter (fun j => f i j ∈ mat i)).card = a i
  /-- (d) `w(v₁ⁱ) + w(v₂ⁱ) = w(eⁱ)` for every edge `eⁱ` of `Bᵢ` -/
  blossom_tight : ∀ i < n, ∀ j < 2 * a i + 1,
    wN i (X i j) + wN i (X i ((j + 1) % (2 * a i + 1))) = wE i (f i j)
  /-- (e) a node of `Bᵢ` meeting no edge of `Mᵢ` has the smallest weight in `Bᵢ` -/
  exposed_min : ∀ i < n, ∀ j < 2 * a i + 1, (∀ e ∈ mat i, ¬ Meets G e (X i j)) →
    ∀ j' < 2 * a i + 1, wN i (X i j) ≤ wN i (X i j')
  /-- (f) `Gᵢ₊₁` is `Gᵢ` with `Bᵢ` shrunk to the single node `uⁱ⁺¹ = ⋃ⱼ X i j`, and
  `Mᵢ₊₁ = Mᵢ ∩ Gᵢ₊₁` -/
  blocks_succ : ∀ i < n, blocks (i + 1) =
    insert ((Finset.range (2 * a i + 1)).biUnion (X i))
      ((blocks i).filter (fun Y => ∀ j < 2 * a i + 1, Y ≠ X i j))
  mat_succ : ∀ i < n,
    mat (i + 1) = (mat i).filter (fun e => IsContractedEdge G (blocks (i + 1)) e)
  /-- (g) weights in `Gᵢ₊₁` are those of `Gᵢ` except at `uⁱ⁺¹` and on edges meeting `uⁱ⁺¹` -/
  wN_succ : ∀ i < n, ∀ Y ∈ blocks (i + 1),
    Y ≠ (Finset.range (2 * a i + 1)).biUnion (X i) → wN (i + 1) Y = wN i Y
  wE_succ : ∀ i < n, ∀ e, IsContractedEdge G (blocks (i + 1)) e →
    ¬ Meets G e ((Finset.range (2 * a i + 1)).biUnion (X i)) → wE (i + 1) e = wE i e
  /-- (h) `w(uⁱ⁺¹) ≤ w(qⁱ)`, where `w(qⁱ)` is the minimum node weight in `Bᵢ` -/
  wN_new_le : ∀ i < n,
    wN (i + 1) ((Finset.range (2 * a i + 1)).biUnion (X i)) ≤
      (Finset.range (2 * a i + 1)).inf' (by simp) (fun j => wN i (X i j))
  /-- (i) for each edge `eⁱ⁺¹` of `Gᵢ₊₁` meeting `uⁱ⁺¹` through the node `vⁱ = X i j` of `Bᵢ`:
  `w(eⁱ⁺¹) = w(eⁱ) − w(vⁱ) + w(qⁱ)` -/
  wE_new : ∀ i < n, ∀ e, IsContractedEdge G (blocks (i + 1)) e →
    ∀ j < 2 * a i + 1, Meets G e (X i j) →
      wE (i + 1) e = wE i e - wN i (X i j) +
        (Finset.range (2 * a i + 1)).inf' (by simp) (fun j' => wN i (X i j'))
  /-- (j) in `Gₙ`, `w(v₁ⁿ) + w(v₂ⁿ) = w(eⁿ)` for every `eⁿ ∈ Mₙ` -/
  mat_tight : ∀ e ∈ mat n, ∀ Y₁ ∈ blocks n, ∀ Y₂ ∈ blocks n, Joins G e Y₁ Y₂ →
    wN n Y₁ + wN n Y₂ = wE n e
  /-- (k) in `Gₙ`, a node meeting no edge of `Mₙ` has weight `0` -/
  exposed_zero : ∀ Y ∈ blocks n, (∀ e ∈ mat n, ¬ Meets G e Y) → wN n Y = 0

end EdmondsMatching65.Polyhedron


