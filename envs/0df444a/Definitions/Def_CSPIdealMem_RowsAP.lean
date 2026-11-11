-- Prove2me | Definitions.Def_CSPIdealMem_RowsAP
-- name    : CSPIdealMem_RowsAP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:29:48.392545+00:00
-- url     : https://prove2.me/theorems/0cf2fabf-dae9-405c-8c6b-709b8136e6bf
-- title:
--   Bipartite edge spans and the linear system $A_P$
-- statement:
--   For a finite bipartite graph with vertex classes $A$, $B$ and edge set $E$, let $L=\mathrm{span}_{\mathbb Q}\{(e_a,e_b): ab\in E\}\subseteq\mathbb Q^A\times\mathbb Q^B$.
--
--   For $R\subseteq D^X$ and distinct $S,T\in S_d$, the graph $G_{S,T}$ has left vertices $(S,a)$, $a\in D^S$, right vertices $(T,b)$, $b\in D^T$, and an edge joining $(S,c|_S)$ and $(T,c|_T)$ for every $c\in\pi_{S\cup T}R$. The matrix $A_P$ (for $R=\mathrm{Sol}(P)$) stacks the rows
--
--   1. $z_{S,a}=0$ for every $S\in S_d$ and $a\notin\pi_SR$;
--   2. for every pair of distinct $S,T$ and every connected component $K$ of $G_{S,T}$ containing an edge, $\sum_{(S,a)\in K} z_{S,a}-\sum_{(T,b)\in K} z_{T,b}=0$.
--
--   $\ker A_P$ is the set of $z\in B_d$ satisfying all these equations.
--
--   This is the linear system of the Taylor algorithm (§4.2).
--
--   **Formalization Note** The bipartite graph is a simple graph on the disjoint union $A\oplus B$. $A_P$ is represented by its set of rows (linear functionals on $B_d$), and its kernel by the intersection of their kernels.
-- source:
--   Rafiey–Soleymani–Jaillet, A Dichotomy Theorem for CSP-Based Ideal Membership, STOC 2027 submission manuscript (held version, sha256 c7140009133170c893c7b31cf2279f3dda0264d867825a8beb7cc6963f50f109), Lemma 4.1, p.23 (PDF 23); §4.2, pp.24–25 (PDF 24–25)

import Mathlib
import Definitions.Def_CSPIdealMem_Indicator

namespace CSPIdealMem

/-! # Bipartite edge spans and the linear system `A_P`

Rafiey–Soleymani–Jaillet, *A Dichotomy Theorem for CSP-Based Ideal Membership*, STOC 2027
submission manuscript (held version, sha256 c7140009…f50f109): the bipartite graph and its edge
span, Lemma 4.1, p.23 (PDF 23); the graphs `G_{S,T}` and the rows of the matrix `A_P`, §4.2,
pp.24–25 (PDF 24–25).

**Formalization Note.** A finite bipartite graph with vertex classes `A`, `B` and edge set
`E ⊆ A × B` is the simple graph `edgeGraph E` on `A ⊕ B` (left vertex `inl a`, right vertex
`inr b`). The matrix `A_P` is represented by its set of rows, each a linear functional on `B_d`;
its kernel is the intersection of their kernels. The edges of `G_{S,T}` are
`(c|_S, c|_T)` for `c ∈ π_{S∪T} R`, i.e. `(φ|_S, φ|_T)` for `φ ∈ R`. -/

open Classical

variable {α : Type}

/-- The bipartite graph with vertex classes `A`, `B` and edge set `E` (Lemma 4.1, p.23), as a
simple graph on `A ⊕ B`. -/
def edgeGraph {A B : Type} (E : Set (A × B)) : SimpleGraph (A ⊕ B) :=
  SimpleGraph.fromRel fun x y => ∃ a b, x = Sum.inl a ∧ y = Sum.inr b ∧ (a, b) ∈ E

/-- `L := span_ℚ {(e_a, e_b) : ab ∈ E} ⊆ ℚ^A × ℚ^B` (Lemma 4.1, p.23). -/
noncomputable def edgeSpan {A B : Type} (E : Set (A × B)) :
    Submodule ℚ ((A → ℚ) × (B → ℚ)) :=
  Submodule.span ℚ ((fun e : A × B => (Pi.single e.1 (1 : ℚ), Pi.single e.2 (1 : ℚ))) '' E)

/-- The edge set of `G_{S,T}` (p.24): an edge joining `(S, c|_S)` and `(T, c|_T)` for every
`c ∈ π_{S∪T} R`. -/
def pairEdges {n : ℕ} (R : Set (Fin n → α)) (S T : Finset (Fin n)) :
    Set ((↥S → α) × (↥T → α)) :=
  (fun φ => (restr S φ, restr T φ)) '' R

/-- The coordinate functional `z ↦ z_{S,a}` on `B_d`. -/
noncomputable def blockCoord {n d : ℕ} (S : Sd n d) (a : ↥S.1 → α) : Bd α n d →ₗ[ℚ] ℚ :=
  (LinearMap.proj (R := ℚ) (φ := fun _ : ↥S.1 → α => ℚ) a).comp
    (LinearMap.proj (R := ℚ) (φ := fun S : Sd n d => (↥S.1 → α) → ℚ) S)

/-- The balance row of a connected component `K` of `G_{S,T}` (p.24):
`z ↦ ∑_{(S,a) ∈ K} z_{S,a} − ∑_{(T,b) ∈ K} z_{T,b}`. -/
noncomputable def balanceRow [Fintype α] {n d : ℕ} (R : Set (Fin n → α)) (S T : Sd n d)
    (K : (edgeGraph (pairEdges R S.1 T.1)).ConnectedComponent) : Bd α n d →ₗ[ℚ] ℚ :=
  (∑ a ∈ Finset.univ.filter
      (fun a => (edgeGraph (pairEdges R S.1 T.1)).connectedComponentMk (Sum.inl a) = K),
      blockCoord S a) -
  (∑ b ∈ Finset.univ.filter
      (fun b => (edgeGraph (pairEdges R S.1 T.1)).connectedComponentMk (Sum.inr b) = K),
      blockCoord T b)

/-- The rows of `A_P` for `R` (pp.24–25): the equations `z_{S,a} = 0` for every `S ∈ S_d` and
`a ∉ π_S R`, and, for every pair of distinct `S, T ∈ S_d` and every connected component `K` of
`G_{S,T}` containing an edge, the balance equation of `K`. -/
def rowsAP [Fintype α] {n : ℕ} (d : ℕ) (R : Set (Fin n → α)) : Set (Bd α n d →ₗ[ℚ] ℚ) :=
  {ρ | ∃ (S : Sd n d) (a : ↥S.1 → α), a ∉ proj S.1 R ∧ ρ = blockCoord S a} ∪
  {ρ | ∃ (S T : Sd n d), S ≠ T ∧
    ∃ K : (edgeGraph (pairEdges R S.1 T.1)).ConnectedComponent,
      (∃ e ∈ pairEdges R S.1 T.1,
        (edgeGraph (pairEdges R S.1 T.1)).connectedComponentMk (Sum.inl e.1) = K) ∧
      ρ = balanceRow R S T K}

/-- `ker A_P` (p.25): the vectors of `B_d` on which every row of `A_P` vanishes. -/
noncomputable def kerAP [Fintype α] {n : ℕ} (d : ℕ) (R : Set (Fin n → α)) :
    Submodule ℚ (Bd α n d) :=
  ⨅ ρ ∈ rowsAP d R, LinearMap.ker ρ

end CSPIdealMem


