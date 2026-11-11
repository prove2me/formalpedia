-- Prove2me | Definitions.Def_MinDilationTree_Sublinear_GeometricGraph
-- name    : MinDilationTree_Sublinear_GeometricGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:24:24.315451+00:00
-- url     : https://prove2.me/theorems/5836e154-3408-4098-86ae-e9cf509854e4
-- title:
--   Euclidean graph distances, dilation and minimum dilation
-- statement:
--   Let $p_0,\ldots,p_{n-1}\in\mathbb R^2$ be point coordinates, and let $G$ be an undirected simple graph on their labels. Each edge $ij$ has length $\|p_i-p_j\|_2$. A walk has the sum of its edge lengths. The graph distance $d_G(i,j)$ is the infimum of these lengths, with value $+\infty$ when no walk exists. For injective coordinates and distinct labels, define
--
--   $$
--   \operatorname{dil}_G(i,j)=\frac{d_G(i,j)}{\|p_i-p_j\|_2},\qquad
--   \operatorname{dil}(G)=\max_{i\ne j}\operatorname{dil}_G(i,j),\qquad
--   \operatorname{Opt}(p)=\min_{T\text{ spanning tree on }\{0,\ldots,n-1\}}\operatorname{dil}(T).
--   $$
--
--   The minimization includes every spanning tree, without requiring its edges to belong to a Delaunay graph. The Euclidean MST predicate specializes the published minimum-total-weight spanning-tree definition to all unordered point pairs with Euclidean weights. This objective is distinct from minimum dilation.
--
--   **Formalization Note** Distances and dilation take values in $[0,+\infty]$. The minimum is represented by an infimum; for a nonempty finite input there are finitely many trees and the minimum is attained. Empty maxima at $n\le1$ are zero; an infimum over no trees is $+\infty$. A pair with identical coordinates has a total Lean quotient, but statements using pair dilation require distinct labels and injective coordinates. The plane is `EuclideanSpace ℝ (Fin 2)`. The shared logarithm is $\log_2 n=\log n/\log 2$ (R4).
-- source:
--   Sarita de Berg, Jacobus Conradi, Peter Kramer, André Nusser, Sampson Wong, STOC 2027 submission #185 (October 2026), p. 3 (PDF p. 4), §2; p. 4 (PDF p. 5), §3 MST upper bound [26]; p. 10 (PDF p. 11), logarithm convention R4

import Mathlib
import Definitions.Def_DoublingMST_IsMSTOf

open scoped ENNReal

set_option autoImplicit false

namespace MinDilationTree.Sublinear

/-- The Euclidean plane, with its Euclidean norm. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- §2, p.3 (PDF 4): the length of a geometric graph walk. -/
noncomputable def walkLength {n : ℕ} (p : Fin n → Plane) (G : SimpleGraph (Fin n))
    {i j : Fin n} (w : G.Walk i j) : ℝ≥0∞ :=
  match w with
  | .nil => 0
  | .cons (u := u) (v := v) _ w' => ENNReal.ofReal ‖p u - p v‖ + walkLength p G w'

/-- Infimum of all walk lengths; the empty infimum is +∞, including disconnected pairs. -/
noncomputable def graphDistance {n : ℕ} (p : Fin n → Plane) (G : SimpleGraph (Fin n))
    (i j : Fin n) : ℝ≥0∞ :=
  ⨅ w : G.Walk i j, walkLength p G w

/-- Pair dilation. Statements using it require distinct labels and an injective point map. -/
noncomputable def pairDilation {n : ℕ} (p : Fin n → Plane) (G : SimpleGraph (Fin n))
    (i j : Fin n) : ℝ≥0∞ :=
  graphDistance p G i j / ENNReal.ofReal ‖p i - p j‖

/-- Maximum over distinct point pairs, represented in the complete lattice [0,+∞].
The empty maximum for n ≤ 1 is 0. -/
noncomputable def dilation {n : ℕ} (p : Fin n → Plane) (G : SimpleGraph (Fin n)) : ℝ≥0∞ :=
  ⨆ i : Fin n, ⨆ j : Fin n, ⨆ (_ : i ≠ j), pairDilation p G i j

/-- §2: the optimum ranges over all spanning trees of the complete geometric graph.
It is +∞ if no spanning tree exists, and 0 on the one-point instance. -/
noncomputable def opt {n : ℕ} (p : Fin n → Plane) : ℝ≥0∞ :=
  ⨅ T : SimpleGraph (Fin n), ⨅ (_ : T.IsTree), dilation p T

/-- The edge set of a simple graph, for the published MST predicate. -/
noncomputable def graphEdges {n : ℕ} (G : SimpleGraph (Fin n)) : Finset (Sym2 (Fin n)) := by
  classical
  exact G.edgeFinset

/-- Specialization of the published minimum-total-weight spanning-tree predicate to
all unordered pairs with Euclidean weights. It imposes no general-position condition. -/
noncomputable def IsEuclideanMST {n : ℕ} (p : Fin n → Plane)
    (G : SimpleGraph (Fin n)) : Prop :=
  DoublingMST.IsMSTOf (fun i j => ‖p i - p j‖) Finset.univ (graphEdges G)

/-- R4: all logarithms in explicit constants have base two. -/
noncomputable def log₂ (n : ℕ) : ℝ := Real.log (n : ℝ) / Real.log 2

end MinDilationTree.Sublinear


