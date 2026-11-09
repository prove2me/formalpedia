-- Prove2me | Definitions.Def_KSPolySign_grad
-- name    : KSPolySign_grad
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:39:30.45324+00:00
-- url     : https://prove2.me/theorems/0cb60a95-f16b-4ee4-83a5-cbae7031e9e9
-- title:
--   The gradient $\nabla P(y)$ in the active coordinates
-- statement:
--   For $y\in[-1,1]^k$ and a coordinate $i$,
--   $$\nabla_i P(y) = \frac{\partial}{\partial x_i} P(\mathrm{faceProj}(y,x))\Big|_{x=y},$$
--   the partial derivative of the potential in an active coordinate, the other coordinates and $F$ held fixed; it is $0$ in a signed coordinate.
--
--   **Formalization Note** Written with the Fréchet derivative. By Lemma 3.7(c) the potential is $C^2$ on each open face, so this is the true partial derivative.
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), §3.1, p.17 (PDF p.17); Lemma 2.7, p.11 (PDF p.11)

import Mathlib
import Definitions.Def_KSPolySign_faceFun
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **The gradient `∇P(y)` on the face of `y`.** `grad C F ρ y i = ∂P/∂y_i (y)`, the partial derivative of
the potential in an active coordinate, the other coordinates and `F` held fixed; it is `0` in a fixed
coordinate. Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), §3.1, p.17 (PDF p.17): "∇f denotes its gradient"; Lemma 2.7, p.11.

**Formalization Note** Written with Mathlib's Fréchet derivative of `faceFun` at `y` in direction
`e_i`. `fderiv` is `0` where the function is not differentiable; Lemma 3.7(c) shows that `P` is `C²` on
each open face, so at every `y` of the cube this is the true partial derivative. -/
noncomputable def grad {n k : ℕ} (C : Fin k → Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin n) ℂ)
    (ρ : ℝ) (y : Fin k → ℝ) (i : Fin k) : ℝ :=
  fderiv ℝ (faceFun C F ρ y) y (Pi.single i 1)

end KSPolySign


