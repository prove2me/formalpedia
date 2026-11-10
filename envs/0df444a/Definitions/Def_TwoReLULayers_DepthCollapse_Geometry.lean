-- Prove2me | Definitions.Def_TwoReLULayers_DepthCollapse_Geometry
-- name    : TwoReLULayers_DepthCollapse_Geometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T10:33:40.013978+00:00
-- url     : https://prove2.me/theorems/3160c59e-33ce-46d3-916f-9976db690c83
-- title:
--   Polytopes, paramids, relative geometric exceptions and finite spans
-- statement:
--   A nonempty polytope $P\subseteq E_n$ is the real convex hull of a nonempty finite set. It is over $R$ when such vertices can all be chosen in $R^n$. Its affine dimension is the dimension of the direction space of its affine hull. The support function uses the published definition $h_P(x)=\max_{p\in P}\langle x,p\rangle$; no new supremum definition is introduced.
--
--   For an affine space $A$, a predicate holds geometrically almost everywhere if it holds outside a finite union of proper affine subspaces of $A$. Write
--   $$L(A,d)=\operatorname{span}_{\mathbb R}\{h_Q:Q\subseteq A\text{ nonempty polytope},\ \dim Q\le d\},\qquad f\equiv g\iff f-g\in L(E_n,n-2).$$
--   Integer dimension cutoffs retain the empty generator class at cutoff $-1$. A separate rational span restricts vertices to $\mathbb Q$ and scalar coefficients to $\mathbb Q$; a rational affine space is the affine hull of a nonempty finite set of rational points. The module defines finite Minkowski sums and the box $a+\sum_i[0,e_i]$. A paramid is the convex hull of such a box with an apex, with the edges $e_i$ linearly independent; a point base is allowed.
--
--   These geometric definitions support the valuation and induction statements. Spans mean finite algebraic combinations, with no topological closure.
--
--   **Formalization Note** The prime real subfield `⊥` is $\mathbb Q$. On nonempty finite convex hulls, the imported support supremum is an attained finite maximum. Affine dimension is a natural number, but all potentially negative bounds are in $\mathbb Z$.
-- source:
--   Kilian Rueß, Florestan Brunck, Christoph Hertrich, Jack Stade, Amir Yehudayoff, Two ReLU layers is all you need, STOC 2027 submission #980 (October 2026), p. 20, Section 5; paramids in Section 1.1, p. 4

import Definitions.Def_TwoReLULayers_DepthCollapse_Model
import Definitions.Def_VertexSampleCSP_supportFn

namespace TwoReLULayers.DepthCollapse

noncomputable section

/-- The published support function, directly on the same Euclidean carrier. -/
abbrev support {n : ℕ} (P : Set (E n)) : E n → ℝ := VertexSampleCSP.supportFn P

/-- Polytopes are nonempty finite convex hulls, with no integrality restriction. -/
def IsPolytope {n : ℕ} (P : Set (E n)) : Prop :=
  ∃ S : Finset (E n), S.Nonempty ∧ P = convexHull ℝ (S : Set (E n))

def Over (R : Subfield ℝ) {n : ℕ} (x : E n) : Prop := ∀ i, x i ∈ R

/-- Rational polytopes use R = bottom, the prime (rational) subfield of the reals. -/
def IsPolytopeOver (R : Subfield ℝ) {n : ℕ} (P : Set (E n)) : Prop :=
  ∃ S : Finset (E n), S.Nonempty ∧ (∀ x ∈ S, Over R x) ∧
    P = convexHull ℝ (S : Set (E n))

/-- Affine dimension, used only with nonempty sets. Integer cutoffs avoid d-1 truncation. -/
def affineDim {n : ℕ} (P : Set (E n)) : ℕ :=
  Module.finrank ℝ (affineSpan ℝ P).direction

/-- Outside a finite union of proper affine subspaces relative to A, not ambient a.e. -/
def GeomAE {n : ℕ} (A : AffineSubspace ℝ (E n)) (p : E n → Prop) : Prop :=
  ∃ k : ℕ, ∃ B : Fin k → AffineSubspace ℝ (E n),
    (∀ j, B j < A) ∧ ∀ x ∈ A, (∀ j, x ∉ B j) → p x

/-- Real linear span, finite algebraic combinations, never a closure. -/
def lowerSpanOn {n : ℕ} (A : Set (E n)) (d : ℤ) : Submodule ℝ (E n → ℝ) :=
  Submodule.span ℝ {f | ∃ Q : Set (E n), IsPolytope Q ∧ Q ⊆ A ∧
    (affineDim Q : ℤ) ≤ d ∧ f = support Q}

def lowerSpan (n : ℕ) : Submodule ℝ (E n → ℝ) :=
  lowerSpanOn Set.univ ((n : ℤ) - 2)

def Congr {n : ℕ} (f g : E n → ℝ) : Prop := f - g ∈ lowerSpan n

/-- The rational specialization records rational vertices AND rational linear coefficients. -/
def rationalSpanOn {n : ℕ} (A : Set (E n)) (d : ℤ) : Submodule ℚ (E n → ℝ) :=
  Submodule.span ℚ {f | ∃ Q : Set (E n), IsPolytopeOver (⊥ : Subfield ℝ) Q ∧
    Q ⊆ A ∧ (affineDim Q : ℤ) ≤ d ∧ f = support Q}

def RationalAffine {n : ℕ} (A : AffineSubspace ℝ (E n)) : Prop :=
  ∃ S : Finset (E n), S.Nonempty ∧ (∀ x ∈ S, Over (⊥ : Subfield ℝ) x) ∧
    A = affineSpan ℝ (S : Set (E n))

def indicator {n : ℕ} (P : Set (E n)) (x : E n) : ℝ := by
  classical
  exact if x ∈ P then 1 else 0

/-- A finite Minkowski sum, with empty sum {0}. -/
def minkowskiSum {n : ℕ} (S : Finset (Fin n)) (P : Fin n → Set (E n)) : Set (E n) :=
  {x | ∃ z : Fin n → E n, (∀ i ∈ S, z i ∈ P i) ∧ x = ∑ i ∈ S, z i}

/-- A translated k-dimensional parallelepiped when its edges are independent. -/
def box {n k : ℕ} (a : E n) (e : Fin k → E n) : Set (E n) :=
  {x | ∃ t : Fin k → ℝ, (∀ i, 0 ≤ t i ∧ t i ≤ 1) ∧ x = a + ∑ i, t i • e i}

def IsParamid {n : ℕ} (P : Set (E n)) : Prop :=
  ∃ k : ℕ, ∃ a : E n, ∃ e : Fin k → E n, ∃ apex : E n,
    LinearIndependent ℝ e ∧ P = convexHull ℝ (insert apex (box a e))

end
end TwoReLULayers.DepthCollapse


