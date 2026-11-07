-- Prove2me | Definitions.Def_QPSpinParisi_BrownianNoise_noise
-- name    : QPSpinParisi_BrownianNoise_noise
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:03:53.80188+00:00
-- url     : https://prove2.me/theorems/fe1f9ef4-a13b-49a0-9e23-0c6d8c56bca8
-- title:
--   The vector $\int_0^t\sqrt\zeta\,dB$
-- statement:
--   The $\mathbb R^3$-valued process $t\mapsto\int_0^t\sqrt{\zeta(r)}\,dB_r$. The integral over $[s,1]$ in (2.3) is its increment between $s$ and $1$.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), (2.3), p.4 (PDF p.4)

import Mathlib
import Definitions.Def_QPSpinParisi_BrownianNoise
import Definitions.Def_QPSpinParisi_E3

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The vector `∫₀ᵗ √ζ(r) dB_r ∈ ℝ³` of a noise (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), (2.3), p.4, PDF p.4).

**Formalization Note** The integral over `[s, 1]` in (2.3) is `W.noise 1 - W.noise s`. -/
noncomputable def BrownianNoise.noise {c : ℕ → ℝ} (W : BrownianNoise c) (t : ℝ≥0) (ω : W.Ω) : E3 :=
  WithLp.toLp 2 fun a : Fin 3 => W.N a t ω

end QPSpinParisi


