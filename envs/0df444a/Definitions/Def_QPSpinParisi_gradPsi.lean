-- Prove2me | Definitions.Def_QPSpinParisi_gradPsi
-- name    : QPSpinParisi_gradPsi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:17:06.306527+00:00
-- url     : https://prove2.me/theorems/c5d10d35-1ac9-4ab2-b568-5e00cc4b8cd6
-- title:
--   The gradient $\nabla\Phi$ of $\Phi=\Psi_{\xi,\gamma}$
-- statement:
--   The gradient in $x$ of the value function $\Phi(t,x)=\Psi_{\xi,\gamma}(t,x)$, as a vector of $\mathbb R^3$. It is the optimal feedback control of (2.3).
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), Lemma 3.7, p.23 (PDF p.23)

import Mathlib
import Definitions.Def_QPSpinParisi_Psi

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The gradient `∇Φ(t, x)` of `Φ = Ψ_{ξ,γ}` in `x` (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), Lemma 3.7, p.23, PDF p.23). -/
noncomputable def gradPsi {c : ℕ → ℝ} (W : BrownianNoise c) (γ : Ico (0 : ℝ) 1 → ℝ) (t : ℝ) (x : E3) : E3 :=
  gradient (Psi W γ t) x

end QPSpinParisi


