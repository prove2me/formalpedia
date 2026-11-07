-- Prove2me | Definitions.Def_QPSpinParisi_d3Psi
-- name    : QPSpinParisi_d3Psi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:17:23.363907+00:00
-- url     : https://prove2.me/theorems/d6ea7692-b2c4-4c1a-a584-ad604e697ac1
-- title:
--   The third derivatives $\partial_k\nabla^2\Phi$
-- statement:
--   The entry $(i,j)$ of $\partial_{x_k}\nabla^2\Phi(t,x)$, for the value function $\Phi=\Psi_{\xi,\gamma}$.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), Lemma 3.7, p.23 (PDF p.23)

import Mathlib
import Definitions.Def_QPSpinParisi_Psi

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The entry `(i, j)` of `∂_{x_k} ∇²Φ(t, x)` for `Φ = Ψ_{ξ,γ}` (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), Lemma 3.7, p.23, PDF p.23). -/
noncomputable def d3Psi {c : ℕ → ℝ} (W : BrownianNoise c) (γ : Ico (0 : ℝ) 1 → ℝ) (t : ℝ) (x : E3) (k i j : Fin 3) : ℝ :=
  iteratedFDeriv ℝ 3 (Psi W γ t) x
    ![EuclideanSpace.single k 1, EuclideanSpace.single i 1, EuclideanSpace.single j 1]

end QPSpinParisi


