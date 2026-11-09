-- Prove2me | Definitions.Def_KSPolySign_hess
-- name    : KSPolySign_hess
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:39:44.646021+00:00
-- url     : https://prove2.me/theorems/c89d0443-d227-427e-9cc5-3e2a5740517e
-- title:
--   The Hessian $\nabla^2 P(y)$ in the active coordinates
-- statement:
--   For $y\in[-1,1]^k$ and coordinates $i,j$,
--   $$\nabla^2_{ij} P(y) = \frac{\partial^2}{\partial x_i\,\partial x_j} P(\mathrm{faceProj}(y,x))\Big|_{x=y},$$
--   the second partial derivatives in the active coordinates; rows and columns of signed coordinates vanish.
--
--   **Formalization Note** Written as the derivative in direction $e_i$ of $x\mapsto\partial_jP$, both via Fréchet derivatives. By Lemma 3.7(c) these are the true second partials and the matrix is symmetric.
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), §3.1, p.17 (PDF p.17); Lemma 2.7, p.11 (PDF p.11)

import Mathlib
import Definitions.Def_KSPolySign_faceFun
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **The Hessian `∇²P(y)` on the face of `y`.** `hess C F ρ y i j = ∂²P/∂y_i∂y_j (y)`, second partial
derivatives in the active coordinates, the other coordinates and `F` held fixed; rows and columns of
fixed coordinates are `0`. Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), §3.1, p.17 (PDF p.17): "∇²f denotes its Hessian, the matrix of its
second partial derivatives"; Lemma 2.7, p.11.

**Formalization Note** The derivative in direction `e_i` of `x ↦ ∂_j P(x)`, both through `fderiv`
of `faceFun`. By Lemma 3.7(c) the potential is `C²` on each open face, so these are the true second
partial derivatives, and the matrix is symmetric. -/
noncomputable def hess {n k : ℕ} (C : Fin k → Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin n) ℂ)
    (ρ : ℝ) (y : Fin k → ℝ) (i j : Fin k) : ℝ :=
  fderiv ℝ (fun x => fderiv ℝ (faceFun C F ρ y) x (Pi.single j 1)) y (Pi.single i 1)

end KSPolySign


