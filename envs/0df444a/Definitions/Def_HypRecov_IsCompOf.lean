-- Prove2me | Definitions.Def_HypRecov_IsCompOf
-- name    : HypRecov_IsCompOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:35:56.568089+00:00
-- url     : https://prove2.me/theorems/907a98c8-df3f-4d02-a90b-c18eda8cfd7c
-- title:
--   Components of $G-R$, full components and minimal clique separators
-- statement:
--   Let $G$ be a graph on $V$ and $R\subseteq V$. A set $L$ is a **component of $G-R$** if it is disjoint from $R$, induces a connected subgraph, and every neighbour of a vertex of $L$ lies in $L$ or in $R$. Its **neighbourhood** $N_G(L)$ is the set of vertices outside $L$ with a neighbour in $L$; the component is **full** if $N_G(L)=R$.
--
--   $R$ is a **minimal clique separator** if it induces a clique and $G-R$ has two distinct full components. The paper defines a minimal separator as one that is inclusion-minimal for some pair of separated vertices and states this two-full-components form as equivalent (p.13); the mission uses the latter.
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), §6.1, p.13 (PDF p.14); Lemma 6.1, p.13

import Mathlib

namespace HypRecov

open Classical in
/-- The open neighbourhood `N_G(L) = {v ∉ L : v has a neighbour in L}` of a vertex set. Zhang, Chen,
Shen, *Hypergraph Recovery from Anonymous Projection Streams*, STOC 2027 submission (manuscript
sha256 719dcfff…), Lemma 6.1, p.13 (PDF p.14). -/
noncomputable def nbhd {n : ℕ} (G : SimpleGraph (Fin n)) (L : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun v => v ∉ L ∧ ∃ u ∈ L, G.Adj u v)

/-- **A component of `G − R`** (ibid., Lemma 6.1, p.13; Lemma 6.3, p.15): `L` is nonempty, avoids `R`,
induces a connected subgraph, and is closed under adjacency in `G − R`. -/
def IsCompOf {n : ℕ} (G : SimpleGraph (Fin n)) (R L : Finset (Fin n)) : Prop :=
  Disjoint L R ∧ (G.induce (L : Set (Fin n))).Connected ∧
    ∀ u ∈ L, ∀ v : Fin n, G.Adj u v → v ∈ L ∨ v ∈ R

/-- **Minimal clique separator.** Ibid., §6.1, p.13: "Recall that a separator is minimal if it is
inclusion-minimal for some pair of separated vertices. Equivalently, deleting it leaves two components
whose neighborhoods are the whole separator. Such a component is called full. A minimal clique
separator is a minimal separator that induces a clique."

**Formalization Note.** The paper's stated equivalent form is used: `R` is a clique of `G` and `G − R`
has two distinct full components. -/
def IsMinCliqueSep {n : ℕ} (G : SimpleGraph (Fin n)) (R : Finset (Fin n)) : Prop :=
  G.IsClique (R : Set (Fin n)) ∧
    ∃ L₁ L₂ : Finset (Fin n), L₁ ≠ L₂ ∧ IsCompOf G R L₁ ∧ IsCompOf G R L₂ ∧
      nbhd G L₁ = R ∧ nbhd G L₂ = R

end HypRecov


