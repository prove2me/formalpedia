-- Prove2me | Definitions.Def_ThinningSprinkling306_ToughCycles_Cuts
-- name    : ThinningSprinkling306_ToughCycles_Cuts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:26:45.718921+00:00
-- url     : https://prove2.me/theorems/d06cba3c-2bbd-4de7-b9cd-498f66577b4e
-- title:
--   Induced components, cut-component toughness and seeded components
-- statement:
--   Let $G$ be a finite simple undirected graph and $W,A$ be vertex sets. The component of a vertex in $G[W]$ is its reachable vertex set, or the empty set if it is absent. The collection of components contains each nonempty component once. A component is seeded when it meets $A$. The external neighborhood of $A$ consists of vertices outside $A$ adjacent to a vertex in $A$.
--
--   For a real parameter $t$, the induced graph $G[W]$ is $t$-tough precisely when
--   $$
--   \forall S\subseteq W,\qquad r=c(G[W\setminus S])\ge2\ \Longrightarrow\ |S|\ge tr.
--   $$
--   Here $c$ is the number of connected components. Global toughness takes $W=V(G)$. Complete graphs, including empty and singleton graphs, satisfy the predicate for every finite $t$; no finite supremum is used.
--
--   These predicates provide the common graph interface for all sampling and cycle statements. Finite labels encode arbitrary finite graphs without connectedness or nonemptiness assumptions.
-- source:
--   Micha Christoph, Zach Hunter, Benny Sudakov, STOC 2027 submission #306 (October 2026), p. 3, toughness definition; Section 2, pp. 4–6 (PDF pp. 6–8) (PDF p. 5); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/306.pdf

import Mathlib

namespace ThinningSprinkling306.ToughCycles

/-- The vertex component in the actual induced graph; empty if the vertex is absent. -/
noncomputable def component {n : ℕ} (G : SimpleGraph (Fin n))
    (W : Finset (Fin n)) (v : Fin n) : Finset (Fin n) := by
  classical
  exact W.filter fun u => ∃ (hv : v ∈ W) (hu : u ∈ W),
    (G.induce (W : Set (Fin n))).Reachable ⟨v, hv⟩ ⟨u, hu⟩

/-- Distinct nonempty components, as their vertex sets. -/
noncomputable def components {n : ℕ} (G : SimpleGraph (Fin n))
    (W : Finset (Fin n)) : Finset (Finset (Fin n)) := by
  classical
  exact W.image (component G W)

/-- Toughness of G[W], testing only cuts leaving at least two components. -/
noncomputable def ToughOn {n : ℕ} (G : SimpleGraph (Fin n))
    (W : Finset (Fin n)) (t : ℝ) : Prop :=
  ∀ S : Finset (Fin n), S ⊆ W →
    2 ≤ (components G (W \ S)).card →
    t * (components G (W \ S)).card ≤ (S.card : ℝ)

noncomputable def Tough {n : ℕ} (G : SimpleGraph (Fin n)) (t : ℝ) : Prop :=
  ToughOn G Finset.univ t

noncomputable def seededComponents {n : ℕ} (G : SimpleGraph (Fin n))
    (W A : Finset (Fin n)) : Finset (Finset (Fin n)) := by
  classical
  exact (components G W).filter fun C => (C ∩ A).Nonempty

/-- External, rather than closed, neighborhood. -/
noncomputable def externalNeighbors {n : ℕ} (G : SimpleGraph (Fin n))
    (A : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun v => v ∉ A ∧ ∃ u ∈ A, G.Adj u v

end ThinningSprinkling306.ToughCycles


