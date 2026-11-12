-- Prove2me | Definitions.Def_AbelianCayleySC_Subexp_RegularGraph
-- name    : AbelianCayleySC_Subexp_RegularGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T06:40:25.299032+00:00
-- url     : https://prove2.me/theorems/0c9c3bb5-02f0-4219-a3c2-719ad30a8593
-- title:
--   Regular graphs with self-loops: cut size, sparsity $\psi$, conductance $\phi$, normalized Laplacian and $\mathrm{mul}_\tau(G)$
-- statement:
--   Let $G$ be a graph on a finite vertex set $V$, $n=|V|$, given by a relation $i\sim j$ meaning that $\{i,j\}$ is an edge; $i\sim i$ is a self-loop. $G$ is **undirected** when $\sim$ is symmetric, and **$d$-regular** when every vertex has exactly $d$ neighbours (a loop counts as one neighbour). This is the paper's standing convention (§3): all graphs are undirected, $d$-regular, and may have self-loops.
--
--   For $Q\subseteq V$, $|E(Q,V\setminus Q)|$ is the number of edges $\{i,j\}$ with $i\in Q$, $j\notin Q$, counted as the ordered pairs $(i,j)$ with $i\in Q$, $j\notin Q$, $i\sim j$ (a crossing edge is never a loop and has exactly one endpoint in $Q$). The **sparsity** and **conductance** of $Q$ are
--
--   $$\psi_G(Q)=\frac{n\,|E(Q,V\setminus Q)|}{d\,|Q|\,|V\setminus Q|},\qquad \phi_G(Q)=\frac{|E(Q,V\setminus Q)|}{d\,|Q|},$$
--
--   and $\psi(G)=\min_{\emptyset\ne Q\ne V}\psi_G(Q)$, $\phi(G)=\min_{0<|Q|\le n/2}\phi_G(Q)$.
--
--   The **normalized adjacency matrix** is $A(G)_{ij}=1/d$ if $i\sim j$ and $0$ otherwise, and the **normalized Laplacian** is $L(G)=I-A(G)$. For $\tau\in\mathbb R$, $\mathrm{mul}_\tau(G)$ is the number of eigenvalues of $L(G)$ that are at most $\tau$, counted with multiplicity.
--
--   These are the objects of the sparsest cut problem studied in the paper, and of the cited eigenspace-enumeration guarantee (Theorem 2.1).
--
--   **Formalization Note** The minima are infima over the finite families of admissible sets; the families are non-empty exactly when $n\ge2$, and every theorem using them assumes $n\ge2$. Division is Lean's real division ($x/0=0$), so $d=0$ or an excluded $Q$ gives the value $0$; no theorem relies on those values except where noted. The structural lemma `normLap_isHermitian` records that $L(G)$ is symmetric for an undirected graph, which is what makes its eigenvalue list (Mathlib's `Matrix.IsHermitian.eigenvalues`, with multiplicity) available.
-- source:
--   Jake Ruotolo, Sparsest Cut on Abelian Cayley Graphs, STOC 2027 submission #1724 (October 2026), p.1 (ψ, φ); §3 p.5 (A(G), L(G), standing convention); Definition 3.1 p.6; §2 p.3 and Theorem 2.1 p.3 (mul_τ(G))

import Mathlib

namespace AbelianCayleySC.Subexp

open Finset

/-!
# Regular graphs with loops: cut size, sparsity, conductance, normalized Laplacian

Jake Ruotolo, *Sparsest Cut on Abelian Cayley Graphs*, STOC 2027 submission #1724 (October 2026),
§1 p.1 (sparsity ψ and conductance φ), §3 p.5 (normalized adjacency and Laplacian, standing
convention: undirected, `d`-regular, self-loops allowed), Definition 3.1 p.6 (conductance).

A graph on a finite vertex type `V` is a relation `adj : V → V → Prop` (`adj i j` means
`{i, j}` is an edge; `adj i i` is a self-loop). Graphs are undirected when `adj` is symmetric,
and `d`-regular when every vertex has exactly `d` neighbours (a loop counts once, as in the
paper's Cayley graphs, where a vertex `x` is adjacent to `x + s` for each `s ∈ S`).
-/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The graph is undirected: the adjacency relation is symmetric. -/
def IsUndirected (adj : V → V → Prop) : Prop := ∀ i j : V, adj i j → adj j i

/-- Every vertex has exactly `d` neighbours (a self-loop counts as one neighbour). -/
def IsRegular (adj : V → V → Prop) [DecidableRel adj] (d : ℕ) : Prop :=
  ∀ i : V, (univ.filter (fun j => adj i j)).card = d

/-- `|E(Q, V ∖ Q)|`: the number of edges `{i, j}` with `i ∈ Q` and `j ∉ Q`. Such an edge is never
a loop and has exactly one endpoint in `Q`, so it is counted once as the ordered pair `(i, j)`
with `i ∈ Q`, `j ∉ Q`. -/
def edgeBoundary (adj : V → V → Prop) [DecidableRel adj] (Q : Finset V) : ℕ :=
  ((Q ×ˢ Qᶜ).filter (fun p => adj p.1 p.2)).card

/-- The sparsity `ψ_G(Q) = n·|E(Q, V∖Q)| / (d·|Q|·|V∖Q|)` of the cut `(Q, V ∖ Q)` (p.1),
with `n = |V|`. -/
noncomputable def sparsity (adj : V → V → Prop) [DecidableRel adj] (d : ℕ) (Q : Finset V) : ℝ :=
  (Fintype.card V : ℝ) * (edgeBoundary adj Q : ℝ) /
    ((d : ℝ) * (Q.card : ℝ) * ((Qᶜ).card : ℝ))

/-- The sparsity of the graph, `ψ(G) = min_{∅ ≠ Q ≠ V} ψ_G(Q)` (p.1). The index type is finite,
and nonempty exactly when `|V| ≥ 2`; every theorem using it assumes `|V| ≥ 2`. -/
noncomputable def sparsestCut (adj : V → V → Prop) [DecidableRel adj] (d : ℕ) : ℝ :=
  ⨅ Q : {Q : Finset V // Q.Nonempty ∧ Q ≠ univ}, sparsity adj d Q.1

/-- The conductance `φ_G(Q) = |E(Q, V∖Q)| / (d·|Q|)` of a set of vertices (Definition 3.1). -/
noncomputable def conductanceSet (adj : V → V → Prop) [DecidableRel adj] (d : ℕ)
    (Q : Finset V) : ℝ :=
  (edgeBoundary adj Q : ℝ) / ((d : ℝ) * (Q.card : ℝ))

/-- The conductance of the graph, `φ(G) = min_{0 < |Q| ≤ |V|/2} φ_G(Q)` (p.1, Definition 3.1).
The index type is finite, and nonempty exactly when `|V| ≥ 2`. -/
noncomputable def conductance (adj : V → V → Prop) [DecidableRel adj] (d : ℕ) : ℝ :=
  ⨅ Q : {Q : Finset V // 0 < Q.card ∧ (Q.card : ℝ) ≤ (Fintype.card V : ℝ) / 2},
    conductanceSet adj d Q.1

/-- The normalized adjacency matrix `A(G)_{ij} = 1/d` if `{i, j} ∈ E(G)`, else `0` (§3, p.5). -/
noncomputable def normAdj (adj : V → V → Prop) [DecidableRel adj] (d : ℕ) : Matrix V V ℝ :=
  fun i j => if adj i j then 1 / (d : ℝ) else 0

/-- The normalized Laplacian `L(G) = I − A(G)` (§3, p.5). -/
noncomputable def normLap (adj : V → V → Prop) [DecidableRel adj] (d : ℕ) : Matrix V V ℝ :=
  1 - normAdj adj d

omit [Fintype V] in
/-- For an undirected graph the normalized Laplacian is symmetric (structural lemma). -/
theorem normLap_isHermitian (adj : V → V → Prop) [DecidableRel adj] (hsymm : IsUndirected adj)
    (d : ℕ) : (normLap adj d).IsHermitian := by
  have hA : (normAdj adj d).IsHermitian := by
    ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, normAdj]
    by_cases h : adj i j
    · simp [h, hsymm i j h]
    · have h' : ¬ adj j i := fun h'' => h (hsymm j i h'')
      simp [h, h']
  exact Matrix.isHermitian_one.sub hA

/-- `mul_τ(G)`: the number of eigenvalues of the normalized Laplacian `L(G)` that are at most `τ`,
counted with multiplicity (§2, p.3; Theorem 2.1; §5 p.14). -/
noncomputable def mulLap (adj : V → V → Prop) [DecidableRel adj] (hsymm : IsUndirected adj)
    (d : ℕ) (τ : ℝ) : ℕ :=
  Fintype.card {i : V // (normLap_isHermitian adj hsymm d).eigenvalues i ≤ τ}

end AbelianCayleySC.Subexp


