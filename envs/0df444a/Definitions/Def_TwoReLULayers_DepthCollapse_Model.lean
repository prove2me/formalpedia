-- Prove2me | Definitions.Def_TwoReLULayers_DepthCollapse_Model
-- name    : TwoReLULayers_DepthCollapse_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T10:33:02.972258+00:00
-- url     : https://prove2.me/theorems/94d99444-9c82-4398-8d8d-d03876fbfe60
-- title:
--   Real-subfield affine networks and geometric CPWL functions
-- statement:
--   Let $R$ be a subfield of $\mathbb R$ and let $E_n=\mathbb R^n$. An $R$-affine scalar map has the form $b+\sum_i w_i x_i$, with $b,w_i\in R$; inputs remain real. A two-hidden-layer network has arbitrary finite widths $m_1,m_2$, two affine vector maps and a final affine scalar map. Its output is
--   $$T^{(2)}(\operatorname{ReLU}(T^{(1)}(\operatorname{ReLU}(T^{(0)}(x))))),\qquad \operatorname{ReLU}(t)=\max(0,t).$$
--   $\operatorname{ReLU2}(R,n)$ is the set of these output functions. Independently, $\operatorname{CPWL}(R,n)$ consists of continuous functions admitting a finite closed polyhedral cover of $E_n$ and an $R$-affine formula on each cell. Each polyhedron is an intersection of finitely many real affine halfspaces; cell inequalities need not have coefficients in $R$. A second predicate records affine formulas on all closed cells of a finite hyperplane arrangement, for the partition-refinement bridge. The module also defines the coordinate dot product, maximum and signs $\pm1$.
--
--   These independent definitions specify the two sides of the depth-collapse theorem. No representation theorem is part of either definition.
--
--   **Formalization Note** $E_n$ is Euclidean space on `Fin n`. Width zero is permitted. `maxCoord` is the supremum of the finite coordinate image; it is used as a maximum only at positive arity (its empty-coordinate default is zero). Every real subfield contains the rational numbers.
-- source:
--   Kilian Rueß, Florestan Brunck, Christoph Hertrich, Jack Stade, Amir Yehudayoff, Two ReLU layers is all you need, STOC 2027 submission #980 (October 2026), p. 2, Section 1, definitions and Eq. (1)

import Mathlib

namespace TwoReLULayers.DepthCollapse

noncomputable section

/-- Real inputs; only affine coefficients are restricted to a subfield. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A scalar affine map with all coefficients in R. -/
structure AffineScalar (R : Subfield ℝ) (n : ℕ) where
  weight : Fin n → R
  bias : R

def AffineScalar.eval {R : Subfield ℝ} {n : ℕ} (a : AffineScalar R n) (x : E n) : ℝ :=
  (a.bias : ℝ) + ∑ i, (a.weight i : ℝ) * x i

/-- An m-output affine map is a family of m scalar affine maps. -/
abbrev AffineR (R : Subfield ℝ) (n m : ℕ) := Fin m → AffineScalar R n

def affineEval {R : Subfield ℝ} {n m : ℕ} (a : AffineR R n m) (x : E n) : E m :=
  WithLp.toLp 2 (fun j => (a j).eval x)

def relu {n : ℕ} (x : E n) : E n := WithLp.toLp 2 (fun i => max 0 (x i))

/-- Two hidden layers and three affine maps, with arbitrary finite widths. -/
structure Network2 (R : Subfield ℝ) (n : ℕ) where
  width₁ : ℕ
  width₂ : ℕ
  first : AffineR R n width₁
  second : AffineR R width₁ width₂
  output : AffineScalar R width₂

def Network2.eval {R : Subfield ℝ} {n : ℕ} (N : Network2 R n) (x : E n) : ℝ :=
  N.output.eval (relu (affineEval N.second (relu (affineEval N.first x))))

def ReLU2 (R : Subfield ℝ) (n : ℕ) : Set (E n → ℝ) :=
  {f | ∃ N : Network2 R n, ∀ x, f x = N.eval x}

def dot {n : ℕ} (a x : E n) : ℝ := ∑ i, a i * x i

/-- Closed real affine halfspaces; no coefficient restriction on cell inequalities. -/
def IsPolyhedron {n : ℕ} (P : Set (E n)) : Prop :=
  ∃ k : ℕ, ∃ a : Fin k → E n, ∃ b : Fin k → ℝ,
    P = {x | ∀ j, dot (a j) x ≤ b j}

/-- Independent geometric definition: continuous, with a finite closed polyhedral cover
on each of whose cells f has an R-affine formula. Arrangement refinement is a theorem. -/
def CPWL (R : Subfield ℝ) (n : ℕ) : Set (E n → ℝ) :=
  {f | Continuous f ∧ ∃ k : ℕ, ∃ P : Fin k → Set (E n),
    ∃ a : Fin k → AffineScalar R n,
    (∀ j, IsPolyhedron (P j)) ∧ (∀ x, ∃ j, x ∈ P j) ∧
      ∀ j x, x ∈ P j → f x = (a j).eval x}

/-- A hyperplane arrangement gives a face-to-face closed polyhedral partition.
Every Boolean choice selects one closed side of each hyperplane. -/
def ArrangementCPWL (R : Subfield ℝ) (n : ℕ) (f : E n → ℝ) : Prop :=
  Continuous f ∧ ∃ k : ℕ, ∃ a : Fin k → E n, ∃ b : Fin k → ℝ,
    ∃ L : (Fin k → Bool) → AffineScalar R n,
      ∀ s x, (∀ j, if s j then dot (a j) x ≤ b j else b j ≤ dot (a j) x) →
        f x = (L s).eval x

/-- The empty-coordinate default is zero; every MAX target has positive arity. -/
def maxCoord {n : ℕ} (x : E n) : ℝ := sSup (Set.range fun i : Fin n => x i)

def IsSign (s : ℝ) : Prop := s = 1 ∨ s = -1

end
end TwoReLULayers.DepthCollapse


