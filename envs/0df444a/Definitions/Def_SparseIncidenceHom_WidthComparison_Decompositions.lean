-- Prove2me | Definitions.Def_SparseIncidenceHom_WidthComparison_Decompositions
-- name    : SparseIncidenceHom_WidthComparison_Decompositions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:19:57.463091+00:00
-- url     : https://prove2.me/theorems/9f0823a1-125e-49ac-bffb-a119996f4aac
-- title:
--   Vertex-bag tree decompositions and independently optimized widths
-- statement:
--   For a finite covered hypergraph $H=(V,E)$, a tree decomposition consists of a finite nonempty tree $T$ and vertex bags $B_t\subseteq V$. Every edge is contained in a bag; every vertex occurs in a nonempty connected set of tree nodes. Empty bags are allowed. Connectivity of an occurrence set means that any two of its nodes can be joined by a tree walk staying in that occurrence set.
--
--   For a real set function $b$ write
--   $$\operatorname{width}_b(T,B)=\max_{t\in V(T)}b(B_t),\quad
--   \operatorname{opt}_H(b)=\min_{(T,B)}\operatorname{width}_b(T,B).$$
--   The two widths are defined independently by
--   $$\operatorname{adw}(H)=\sup_{w\in M_H}\operatorname{opt}_H(b_w),\qquad
--   \operatorname{fhw}(H)=\operatorname{opt}_H(\rho_H^*).$$
--   The adaptive supremum is outside the decomposition minimum. No special hypertree condition or edge ownership condition is imposed.
--
--   These are the width notions compared by the goal. Trees use a carrier $\operatorname{Fin}(n+1)$ for arbitrary $n$, which represents every finite nonempty tree up to relabeling. The minimum is encoded as an infimum of attained finite costs; for finite vertex sets, only finitely many bag subsets, and hence bag-cost maxima, occur. The one-bag decomposition supplies feasibility even for an empty hypergraph.
-- source:
--   Matthias Lanzinger, STOC 2027 submission #662 (October 2026), p. 8, Section 2.2, Equation (1) and definitions of adaptive and fractional hypertree width

import Mathlib
import Definitions.Def_SparseIncidenceHom_WidthComparison_Covers

namespace SparseIncidenceHom.WidthComparison

/-- Section 2.2, p. 8: every finite nonempty tree can be relabelled by Fin (n+1). -/
structure TreeDecomposition {V : Type} (H : FiniteHypergraph V) (n : ℕ) where
  tree : SimpleGraph (Fin (n + 1))
  isTree : tree.IsTree
  bag : Fin (n + 1) → Set V
  edge_covered : ∀ e : Edge H, ∃ t, e.val ⊆ bag t
  vertex_covered : ∀ v : V, ∃ t, v ∈ bag t
  vertex_connected : ∀ (v : V) (s t : Fin (n + 1)), v ∈ bag s → v ∈ bag t →
    ∃ p : tree.Walk s t, ∀ u ∈ p.support, v ∈ bag u

noncomputable def decompositionWidth {V : Type} {H : FiniteHypergraph V} {n : ℕ}
    (D : TreeDecomposition H n) (b : Set V → ℝ) : ℝ := sSup (Set.range (fun t => b (D.bag t)))

noncomputable def optimalWidth {V : Type} (H : FiniteHypergraph V) (b : Set V → ℝ) : ℝ :=
  sInf {c | ∃ (n : ℕ) (D : TreeDecomposition H n), c = decompositionWidth D b}

/-- Supremum over modular weights OUTSIDE the minimum over decompositions. -/
noncomputable def adaptiveWidth {V : Type} [Fintype V] (H : FiniteHypergraph V) : ℝ :=
  sSup {c | ∃ w : V → ℝ, IsModularWeight H w ∧ c = optimalWidth H (modularCost w)}

/-- Independently defined from the fractional-cover bag function. -/
noncomputable def fractionalHypertreeWidth {V : Type} [Fintype V] (H : FiniteHypergraph V) : ℝ :=
  optimalWidth H (setCoverCost H)

end SparseIncidenceHom.WidthComparison


