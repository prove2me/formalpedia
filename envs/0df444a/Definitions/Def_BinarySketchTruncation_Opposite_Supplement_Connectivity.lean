-- Prove2me | Definitions.Def_BinarySketchTruncation_Opposite_Supplement_Connectivity
-- name    : BinarySketchTruncation_Opposite_Supplement_Connectivity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:05:38.999217+00:00
-- url     : https://prove2.me/theorems/32fcf9b3-d0ab-4186-acdc-2bd79f4b75e8
-- title:
--   Spanning bipartite edge graphs and connectivity communication error
-- statement:
--   Fix nonnegative integers a and b. Use the disjoint union of a left vertices and b right vertices as the whole vertex set, and pairs (i,j) as its a·b possible bipartite edges. For z ∈ 𝔽₂^{a·b}, G(z) has the edge {i,j} precisely when z(i,j)=1; same-side vertices are never adjacent. All vertices, including isolated vertices, remain present. Let f(z) be the Boolean connectivity predicate and let q(z) be its real indicator.
--
--   For a deterministic message map φ, a deterministic Boolean decoder g, and any fixed simple graph H on the same vertices, define
--
--   $$
--   \widetilde e_H(\varphi,g)=\Pr_{Z\ \mathrm{uniform}}
--    \{g(\varphi(Z),H)\ne\mathbf1_{\{G(Z)\cup H\ \mathrm{connected}\}}\}.
--   $$
--
--   The probability is over the edge vector alone. The graph H can contain arbitrary edges, including edges within either part. The same message map and decoder must serve every H in Theorem 3. These objects supply the error functional of Eq. (7) and the indicator used in Lemma 3.
--
--   **Formalization Note** Graphs are Mathlib SimpleGraphs. The vertex type is Fin a ⊕ Fin b, the edge type is Fin a × Fin b, and graph union is the lattice supremum. The connectivity convention for an empty vertex type is Mathlib's (not connected); the indicator is constant in every zero-edge case, so Lemma 3 remains valid.
-- source:
--   Robinson D.H. Cung, Adway Girish, Emre Telatar, STOC 2027 submission #341 (October 2026), pp. 11–12 (PDF pp. 12–13), §5, Eq. (7), Theorem 3, Lemma 3; pp. 18–20 (PDF pp. 19–21), Appendix A

import Mathlib
import Definitions.Def_BinarySketchTruncation_Opposite_Supplement_UniformFinite

namespace BinarySketchTruncation.Opposite.Supplement

/-- The spanning subgraph of K_{a,b} selected by its complete edge vector.
All a+b vertices remain in the vertex type, including isolated vertices. -/
def edgeGraph {a b : ℕ} (z : (Fin a × Fin b) → Bit) :
    SimpleGraph (Fin a ⊕ Fin b) where
  Adj x y := match x, y with
    | Sum.inl i, Sum.inr j => z (i, j) = 1
    | Sum.inr j, Sum.inl i => z (i, j) = 1
    | _, _ => False
  symm := ⟨by intro x y; cases x <;> cases y <;> simp_all⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

/-- Connectivity on the whole vertex set, as a Boolean function of the edge vector. -/
noncomputable def connectivityBool {a b : ℕ} (z : (Fin a × Fin b) → Bit) : Bool := by
  classical
  exact decide (edgeGraph z).Connected

/-- The real-valued indicator used in the variance reduction lemma. -/
noncomputable def connectivityIndicator {a b : ℕ} (z : (Fin a × Fin b) → Bit) : ℝ :=
  if connectivityBool z then 1 else 0

/-- Equation (7): error over uniform Z only; H is a fixed, arbitrary simple graph.
Both the message map and decoder are deterministic functions. -/
noncomputable def connectivityError {a b : ℕ} {M : Type}
    (φ : ((Fin a × Fin b) → Bit) → M)
    (g : M → SimpleGraph (Fin a ⊕ Fin b) → Bool)
    (H : SimpleGraph (Fin a ⊕ Fin b)) : ℝ := by
  classical
  exact uniformProbability (fun z =>
    g (φ z) H ≠ decide ((edgeGraph z ⊔ H).Connected))

end BinarySketchTruncation.Opposite.Supplement


