-- Prove2me | Definitions.Def_LeblSCV_Levi_complexHessian
-- name    : LeblSCV_Levi_complexHessian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:26:40.213145+00:00
-- url     : https://prove2.me/theorems/3bc9cf64-4205-4b48-9fea-5c5a56ef41e0
-- title:
--   Complex Hessian $\partial^2 r/\partial\bar z_k\partial z_\ell$ of a real function
-- statement:
--   For a smooth real-valued function $r$ on an open subset of $\mathbb{C}^n$ and a point $p$, the **complex Hessian** of $r$ at $p$ is the $n \times n$ matrix with entries
--   $$\left.\frac{\partial^2 r}{\partial \bar z_k \partial z_\ell}\right|_p = \frac{\partial}{\partial \bar z_k}\left(\frac{\partial r}{\partial z_\ell}\right)(p), \qquad k, \ell = 1, \dots, n.$$
--   It is the matrix whose restriction to holomorphic tangent vectors of a hypersurface is the Levi form.
--
--   **Formalization Note.** `complexHessian r p k l` is the $(k,\ell)$ entry, computed with the Wirtinger derivatives `wirtingerZ`/`wirtingerZbar` of `r` viewed as a complex-valued function.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 66 (complex Hessian, after Definition 2.3.5)

import Mathlib
import Definitions.Def_LeblSCV_Levi_wirtingerZ

namespace LeblSCV.Levi

/-- The complex Hessian entry `∂²r/∂z̄_k∂z_ℓ` at `p` of a real function `r` (Lebl, p. 66):
`∂/∂z̄_k` applied to `∂r/∂z_ℓ`. -/
noncomputable def complexHessian {n : ℕ} (r : (Fin n → ℂ) → ℝ) (p : Fin n → ℂ) (k l : Fin n) : ℂ :=
  wirtingerZbar (wirtingerZ (fun z => (r z : ℂ)) l) k p

end LeblSCV.Levi


