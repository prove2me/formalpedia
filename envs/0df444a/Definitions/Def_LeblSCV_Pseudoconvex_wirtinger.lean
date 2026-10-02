-- Prove2me | Definitions.Def_LeblSCV_Pseudoconvex_wirtinger
-- name    : LeblSCV_Pseudoconvex_wirtinger
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T03:53:41.548824+00:00
-- url     : https://prove2.me/theorems/12048c5d-6082-4d92-a5d6-3983c00888ce
-- title:
--   Wirtinger derivatives $\partial/\partial z_\ell$ and $\partial/\partial \bar z_\ell$ on $\mathbb{C}^n$
-- statement:
--   Write $z_\ell = x_\ell + i y_\ell$ for the coordinates of $\mathbb{C}^n$. For a (real-)differentiable $g : \mathbb{C}^n \to \mathbb{C}$, the **Wirtinger derivatives** are
--   $$\frac{\partial g}{\partial z_\ell} = \frac{1}{2}\left(\frac{\partial g}{\partial x_\ell} - i \frac{\partial g}{\partial y_\ell}\right), \qquad \frac{\partial g}{\partial \bar z_\ell} = \frac{1}{2}\left(\frac{\partial g}{\partial x_\ell} + i \frac{\partial g}{\partial y_\ell}\right).$$
--
--   They are the building blocks of the complex Hessian.
--
--   **Formalization Note.** The real partial derivatives are the Fréchet derivative over $\mathbb{R}$, applied to the vectors $e_\ell$ and $i e_\ell$ of `EuclideanSpace ℂ (Fin n)`.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), §1.1 (Wirtinger operators), used on p. 85

import Mathlib

namespace LeblSCV.Pseudoconvex

/-- Wirtinger derivative `∂g/∂z_ℓ = ½ (∂g/∂x_ℓ − i ∂g/∂y_ℓ)` at `z`, where `z_ℓ = x_ℓ + i y_ℓ`
(Lebl, §1.1). The real partials are Fréchet derivatives over `ℝ` in the directions `e_ℓ` and
`i e_ℓ` of `ℂⁿ = EuclideanSpace ℂ (Fin n)`. -/
noncomputable def wirtingerZ {n : ℕ} (g : EuclideanSpace ℂ (Fin n) → ℂ) (l : Fin n)
    (z : EuclideanSpace ℂ (Fin n)) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ g z (EuclideanSpace.single l 1) -
    Complex.I * fderiv ℝ g z (EuclideanSpace.single l Complex.I))

/-- Wirtinger derivative `∂g/∂z̄_ℓ = ½ (∂g/∂x_ℓ + i ∂g/∂y_ℓ)` at `z`. -/
noncomputable def wirtingerZbar {n : ℕ} (g : EuclideanSpace ℂ (Fin n) → ℂ) (l : Fin n)
    (z : EuclideanSpace ℂ (Fin n)) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ g z (EuclideanSpace.single l 1) +
    Complex.I * fderiv ℝ g z (EuclideanSpace.single l Complex.I))

end LeblSCV.Pseudoconvex


