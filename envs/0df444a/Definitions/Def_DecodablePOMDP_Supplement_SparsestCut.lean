-- Prove2me | Definitions.Def_DecodablePOMDP_Supplement_SparsestCut
-- name    : DecodablePOMDP_Supplement_SparsestCut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:44:54.555207+00:00
-- url     : https://prove2.me/theorems/089e96e8-7502-462d-bddf-77eed8c46655
-- title:
--   Uniform sparsest-cut value $\phi(G)$ (Definition 5), graph inputs and kernel codes
-- statement:
--   Let $G=(V,E)$ be a simple graph with vertex set $V=\{0,\dots,n-1\}$. For $A\subseteq V$ let $\partial A$ be the set of edges with exactly one endpoint in $A$. The **uniform sparsest-cut value** of $G$ is
--
--   $$\phi(G)=\min_{\emptyset\ne A\subsetneq V}\frac{|\partial A|}{|A|\,(n-|A|)}.$$
--
--   A **graph input** is $n$ together with the adjacency matrix of $G$ (symmetric, zero diagonal); $m=|E|$ is the number of adjacent pairs $i<j$. Its binary code is the self-delimiting binary code of $n$ followed by the $n^2$ bits of the adjacency matrix in row-major order. An output kernel $K\in\mathbb Q^{V\times[O]}$, $K(y\mid s)=$ `K s y`, is coded as the binary code of $O$ followed by the codes of all entries (sign, numerator, denominator) in index order.
--
--   These are the objects of Theorem 7, which builds from a graph an observation kernel whose optimal $\ell_1$-observability parameter is $\frac n{2m}\phi(G)$.
--
--   **Formalization Note** $|\partial A|$ counts the ordered pairs $(i,j)$ with $i\in A$, $j\notin A$ adjacent, i.e. each boundary edge once. $\phi(G)$ is a real infimum over the finitely many nonempty proper subsets, a minimum when $n\ge2$; Lean returns $0$ for $n\le1$, a case never used. The codes reuse the published `encodeNat` and `encodeRat` of the base mission. The adjacency matrix is the standard graph encoding; its length is at least $n^2$, so "polynomial time" is polynomial in the number of vertices, as it must be for a construction with one column per vertex.
-- source:
--   Dobson, Jog, Shiu, Quasipolynomial-Time Planning for Decodable POMDPs (preprint, sha256 c1256cbe…3584b), Definition 5, p.28; Theorem 7, p.28 (input and output of the construction)

import Mathlib
import Definitions.Def_ExponomialAssortment_FPTAS_Machine

namespace DecodablePOMDP.Supplement

open ExponomialAssortment.FPTAS

/-- **Number of boundary edges** `|∂A|` of a vertex set `A` in a simple graph `G` on `Fin n`: the
edges with exactly one endpoint in `A`, counted once each as the ordered pairs `(i, j)` with
`i ∈ A`, `j ∉ A` and `G.Adj i j`.

Dobson, Jog, Shiu, *Quasipolynomial-Time Planning for Decodable POMDPs* (preprint, sha256
c1256cbe…3584b), Definition 5, p.28: "∂A is the set of edges with exactly one endpoint in A." -/
noncomputable def boundaryCount {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : ℕ := by
  classical
  exact ((A ×ˢ Aᶜ).filter (fun p => G.Adj p.1 p.2)).card

/-- **Uniform sparsest-cut value** (Definition 5, p.28):
`ϕ(G) = min_{∅ ≠ A ⊊ V} |∂A| / (|A| (n − |A|))`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), Definition 5, p.28: "Let G = (V, E) be a graph
with n vertices. Define the uniform sparsest-cut value of G by ϕ(G) := min_{∅≠A⊊V}
|∂A| / (|A|(n − |A|))".

**Formalization Note.** `V = Fin n`. A real infimum over the finite set of nonempty proper subsets,
hence a minimum whenever `n ≥ 2` (the index set is then nonempty); for `n ≤ 1` the index set is
empty and Lean's value is `0`. Every use in this mission assumes `n ≥ 2`. -/
noncomputable def sparsestCut {n : ℕ} (G : SimpleGraph (Fin n)) : ℝ :=
  ⨅ A : {A : Finset (Fin n) // A.Nonempty ∧ A ≠ Finset.univ},
    (boundaryCount G A.1 : ℝ) / ((A.1.card : ℝ) * ((n : ℝ) - (A.1.card : ℝ)))

/-- **Graph input** of Theorem 7 (p.28): the number of vertices `n` and the adjacency matrix
`adj : Fin n → Fin n → Bool` of a graph on `V = Fin n`. -/
structure GraphInput where
  n : ℕ
  adj : Fin n → Fin n → Bool

/-- A graph input is **valid** if its adjacency matrix is symmetric with zero diagonal, i.e. it is
the adjacency matrix of a simple graph. -/
def GraphInput.IsValid (I : GraphInput) : Prop :=
  (∀ i j, I.adj i j = I.adj j i) ∧ (∀ i, I.adj i i = false)

/-- The simple graph on `Fin n` with adjacency `adj` (for a valid input, `G.Adj i j ↔ adj i j`). -/
def GraphInput.toGraph (I : GraphInput) : SimpleGraph (Fin I.n) :=
  SimpleGraph.fromRel (fun i j => I.adj i j = true)

/-- The number of edges `m = |E|`: the pairs `i < j` with `adj i j`. -/
def GraphInput.numEdges (I : GraphInput) : ℕ :=
  (Finset.univ.filter (fun p : Fin I.n × Fin I.n => p.1 < p.2 ∧ I.adj p.1 p.2 = true)).card

/-- **Binary code of a graph input**: `encodeNat n` followed by the `n²` bits of the adjacency
matrix in row-major order. Its length is the input size of Theorem 7.

**Formalization Note.** `encodeNat` is `ExponomialAssortment.FPTAS.encodeNat`, the base mission's
code. The adjacency matrix is the standard encoding of a graph: its length is at least `n²`, so
"polynomial time" is polynomial in the number of vertices, as it must be for a construction whose
output has a column per vertex. (Coding `n` in binary next to an edge list would make the input of a
graph with many isolated vertices logarithmically short in `n`.) -/
def encodeGraph (I : GraphInput) : List Bool :=
  encodeNat I.n ++ (List.ofFn (fun i => List.ofFn (fun j => I.adj i j))).flatten

/-- **Binary code of an output kernel** `K : Fin n → Fin O → ℚ` (`K s y = K(y | s)`): `encodeNat O`
followed by every entry `encodeRat (K s y)` in index order (`s` outer, `y` inner).

**Formalization Note.** `encodeRat` is `ExponomialAssortment.FPTAS.encodeRat` (sign, binary
numerator, binary denominator). The code is self-delimiting, so it determines `O` and `K`. -/
def encodeKernel {n O : ℕ} (K : Fin n → Fin O → ℚ) : List Bool :=
  encodeNat O ++ (List.ofFn (fun s => (List.ofFn (fun y => encodeRat (K s y))).flatten)).flatten

end DecodablePOMDP.Supplement


