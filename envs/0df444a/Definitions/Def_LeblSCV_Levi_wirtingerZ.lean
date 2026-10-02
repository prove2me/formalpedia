-- Prove2me | Definitions.Def_LeblSCV_Levi_wirtingerZ
-- name    : LeblSCV_Levi_wirtingerZ
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:26:06.311867+00:00
-- url     : https://prove2.me/theorems/0267c616-9b37-4b27-8b06-a16de501909a
-- title:
--   Wirtinger derivatives $\partial/\partial z_\ell$ and $\partial/\partial\bar z_\ell$ on $\mathbb{C}^n$
-- statement:
--   Write the coordinates of $\mathbb{C}^n$ as $z_\ell = x_\ell + i y_\ell$, $\ell = 1, \dots, n$. For a real-differentiable function $g : \mathbb{C}^n \to \mathbb{C}$ the **Wirtinger derivatives** at a point $z$ are
--   $$\frac{\partial g}{\partial z_\ell}(z) = \frac{1}{2}\left(\frac{\partial g}{\partial x_\ell}(z) - i\,\frac{\partial g}{\partial y_\ell}(z)\right), \qquad \frac{\partial g}{\partial \bar z_\ell}(z) = \frac{1}{2}\left(\frac{\partial g}{\partial x_\ell}(z) + i\,\frac{\partial g}{\partial y_\ell}(z)\right).$$
--   They are the coordinate expressions of the holomorphic and antiholomorphic vectors $\frac{\partial}{\partial z_\ell}\big|_z$, $\frac{\partial}{\partial \bar z_\ell}\big|_z$ used to define $T^{(1,0)}_p$ and the Levi form.
--
--   **Formalization Note.** $\mathbb{C}^n$ is `Fin n → ℂ`; indices are 0-based. The real partials $\partial g/\partial x_\ell$ and $\partial g/\partial y_\ell$ are the real Fréchet derivative `fderiv ℝ g z` applied to the vectors $e_\ell$ and $i e_\ell$ (`Pi.single l 1`, `Pi.single l I`). The file defines both `wirtingerZ` and `wirtingerZbar`.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), pp. 62–64 (∂/∂z_k, ∂/∂z̄_k), with the Wirtinger operators of §1.1

import Mathlib

namespace LeblSCV.Levi

/-- Wirtinger derivative `∂g/∂z_ℓ = ½ (∂g/∂x_ℓ − i ∂g/∂y_ℓ)` at `z`, where `z_ℓ = x_ℓ + i y_ℓ`
(Lebl, §1.1, used on p. 64–66). Real partials are Fréchet derivatives over `ℝ` in the
directions `e_ℓ` and `i e_ℓ`. -/
noncomputable def wirtingerZ {n : ℕ} (g : (Fin n → ℂ) → ℂ) (l : Fin n) (z : Fin n → ℂ) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ g z (Pi.single l 1) - Complex.I * fderiv ℝ g z (Pi.single l Complex.I))

/-- Wirtinger derivative `∂g/∂z̄_ℓ = ½ (∂g/∂x_ℓ + i ∂g/∂y_ℓ)` at `z`. -/
noncomputable def wirtingerZbar {n : ℕ} (g : (Fin n → ℂ) → ℂ) (l : Fin n) (z : Fin n → ℂ) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ g z (Pi.single l 1) + Complex.I * fderiv ℝ g z (Pi.single l Complex.I))

end LeblSCV.Levi


