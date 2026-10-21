-- Prove2me | Definitions.Def_IsodiamVar_Simplex_Defs
-- name    : IsodiamVar_Simplex_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:46:37.198019+00:00
-- url     : https://prove2.me/theorems/b68fc5ce-ece7-427e-9980-2cb9eae9d6e6
-- title:
--   Generalized variance, radius, simplex vertices, and supported probabilities
-- statement:
--   Let $E_n=\mathbb R^n$ with Euclidean distance. For a nonnegative convex function $V:E_n\to[0,\infty)$ and a Borel probability measure $\mu$, define the **generalized variance** by
--
--   $$
--   \operatorname{Var}_V(\mu)=\inf_{z\in E_n}\int_{E_n}V(x-z)\,d\mu(x).
--   $$
--
--   The file also defines $r_n=\sqrt{n/(2n+2)}$, families of $k+1$ vertices at a common positive side length $d$, their equal-mass measure, the class $\mathcal P(K)$ of Borel probability measures carried by $K$, and coercivity through compact nonnegative sublevel sets. These objects are shared by the geometric bounds and equality statements.
--
--   **Formalization Note** A regular simplex is represented by its vertex family; the closed convex hull of that family is the simplex as a set. The infimum ranges over every center.
-- source:
--   Lim & McCann, Geometrical bounds for the variance and recentered moments, arXiv:2001.11851v1, pp. 2, 4–6, (1.8), Definition 1.8(b)–(c), Remark 1.9

import Mathlib

open MeasureTheory

namespace IsodiamVar.Simplex

/-- Euclidean `ℝⁿ`, equipped with its Euclidean norm and Borel σ-algebra. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Equation (1.8): the infimum is over every center, not only barycenters. -/
noncomputable def varV {n : ℕ} (V : E n → ℝ) (μ : Measure (E n)) : ℝ :=
  ⨅ z : E n, ∫ x, V (x - z) ∂μ

/-- Circumradius of the unit regular `n`-simplex. -/
noncomputable def rn (n : ℕ) : ℝ := Real.sqrt ((n : ℝ) / (2 * n + 2))

/-- The vertices of a regular `k`-simplex of side length `d`. -/
def IsRegularSimplex {n k : ℕ} (x : Fin (k + 1) → E n) (d : ℝ) : Prop :=
  0 < d ∧ ∀ i j, i ≠ j → dist (x i) (x j) = d

/-- Equal mass on each of the `k + 1` simplex vertices. -/
noncomputable def uniformVertexMeasure {n k : ℕ} (x : Fin (k + 1) → E n) : Measure (E n) :=
  ∑ i, ((k : ENNReal) + 1)⁻¹ • Measure.dirac (x i)

/-- The Borel probability measures carried by `K`. -/
def InP {n : ℕ} (K : Set (E n)) (μ : Measure (E n)) : Prop :=
  IsProbabilityMeasure μ ∧ μ Kᶜ = 0

/-- Every nonnegative sublevel set of `V` is compact. -/
def Coercive {n : ℕ} (V : E n → ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → IsCompact {x | V x ≤ t}

end IsodiamVar.Simplex


