-- Prove2me | Definitions.Def_Kall1976_Distribution
-- name    : Kall1976_Distribution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:51:18.86886+00:00
-- url     : https://prove2.me/theorems/0556d70e-4688-4406-8dd1-a75de767c6ef
-- title:
--   Affine random linear programs and basis regions
-- statement:
--   An affine random linear-program model, its selected-column basis matrix, the raw and ordered disjoint basis regions, and the corresponding basis objective value.
-- source:
--   Peter Kall, Stochastic Linear Programming, Springer, 1976, Chapter II, model (5) printed p. 27 / PDF33, Assumption A1 printed p. 28 / PDF34, and Theorem 8 printed p. 29 / PDF35. https://doi.org/10.1007/978-3-642-66252-2.

import Definitions.Def_KallMayer_Recourse_LPValue

open MeasureTheory

namespace Kall1976

/-- The affine random LP data of Chapter II (5), printed p. 27. -/
structure AffineLP (r m n : ℕ) where
  A : (Fin r → ℝ) →ᵃ[ℝ] Matrix (Fin m) (Fin n) ℝ
  b : (Fin r → ℝ) →ᵃ[ℝ] (Fin m → ℝ)
  c : (Fin r → ℝ) →ᵃ[ℝ] (Fin n → ℝ)

variable {r m n q : ℕ}

/-- The square submatrix with selected columns, in their original order. -/
def basisMatrix (D : AffineLP r m n) (σ : Fin m → Fin n) (t : Fin r → ℝ) :
    Matrix (Fin m) (Fin m) ℝ := fun i j => D.A t i (σ j)

/-- Raw optimality region A_i, including the source's zero-inverse convention
at singular matrices. Mathlib's nonsingular matrix inverse has that convention. -/
noncomputable def rawRegion (D : AffineLP r m n) (T : Set (Fin r → ℝ))
    (σ : Fin m → Fin n) : Set (Fin r → ℝ) :=
  {t | t ∈ T ∧
    (∀ i, 0 ≤ Matrix.mulVec (basisMatrix D σ t)⁻¹ (D.b t) i) ∧
    (∀ j, 0 ≤ D.c t j -
      ∑ k, D.c t (σ k) * ((basisMatrix D σ t)⁻¹ * D.A t) k j)}

/-- The ordered disjointification B_i of the raw regions (printed p. 29). -/
noncomputable def basisRegion (D : AffineLP r m n) (T : Set (Fin r → ℝ))
    (σ : Fin q → Fin m → Fin n) (i : Fin q) : Set (Fin r → ℝ) :=
  rawRegion D T (σ i) \ {t | ∃ j : Fin q, j < i ∧ t ∈ rawRegion D T (σ j)}

/-- γ_i = c_Bᵀ B⁻¹ b, with the source's totalization at singular bases. -/
noncomputable def basisValue (D : AffineLP r m n) (σ : Fin m → Fin n)
    (t : Fin r → ℝ) : ℝ :=
  dotProduct (fun k => D.c t (σ k)) (Matrix.mulVec (basisMatrix D σ t)⁻¹ (D.b t))

end Kall1976


