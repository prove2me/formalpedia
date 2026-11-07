-- Prove2me | Definitions.Def_QPSpinParisi_hessPsi
-- name    : QPSpinParisi_hessPsi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:17:47.308786+00:00
-- url     : https://prove2.me/theorems/42dfe262-0e79-4fe3-93b5-a4f60bba54f8
-- title:
--   The Hessian $\nabla^2\Phi$ of $\Phi=\Psi_{\xi,\gamma}$
-- statement:
--   The matrix of second derivatives in $x$ of the value function $\Phi=\Psi_{\xi,\gamma}$, in the standard basis.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), Lemma 3.7, p.23 (PDF p.23)

import Mathlib
import Definitions.Def_QPSpinParisi_Psi

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The Hessian `∇²Φ(t, x)` of `Φ = Ψ_{ξ,γ}` in `x` (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), Lemma 3.7, p.23, PDF p.23), as a matrix in the standard basis. -/
noncomputable def hessPsi {c : ℕ → ℝ} (W : BrownianNoise c) (γ : Ico (0 : ℝ) 1 → ℝ) (t : ℝ) (x : E3) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => iteratedFDeriv ℝ 2 (Psi W γ t) x
    ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]

end QPSpinParisi


