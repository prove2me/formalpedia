-- Prove2me | Definitions.Def_QPSpinParisi_ctrlJ
-- name    : QPSpinParisi_ctrlJ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:06:47.535136+00:00
-- url     : https://prove2.me/theorems/81b579f4-f640-4c4e-9b11-0964d0fe3c34
-- title:
--   The objective of the control problems (2.3), (3.23)
-- statement:
--   For a terminal function $f$, a drift weight $\kappa$ and a control $u\in D[s,1]$, the objective is
--   $$\mathbb E\Big[f\Big(x+\int_s^1\sqrt{\zeta(r)}\,dB_r+\int_s^1\kappa(r)u_r\,dr\Big)-\frac12\int_s^1\kappa(r)\|u_r\|^2\,dr\Big].$$
--   With $f=\|\cdot\|$, $\kappa=\zeta\gamma$ it is the objective of (2.3). With $f=g_\beta(\|\cdot\|)$, $\kappa=\beta\zeta\alpha$ it is that of (3.23).
--
--   **Formalization Note** (3.23) prints the expectation separately on the two terms, which is the same by Fubini.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), (2.3), p.4 (PDF p.4); (3.23), p.19 (PDF p.19)

import Mathlib
import Definitions.Def_QPSpinParisi_BrownianNoise_noise
import Definitions.Def_QPSpinParisi_E3

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The objective of the control problems (2.3) and (3.23) (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), p.4, PDF p.4; p.19, PDF p.19), for a terminal function
`f` and a drift weight `κ`:
`E[ f(x + ∫_s^1 √ζ dB + ∫_s^1 κ(r) u_r dr) - (1/2) ∫_s^1 κ(r) ‖u_r‖² dr ]`.

**Formalization Note** (2.3) is the case `f = ‖·‖`, `κ = ζγ`. (3.23) is the case `f = g_β(‖·‖)`, `κ = βζα`, where
`(1/2) κ = (β/2) ζα`; the printed `E` split over the two terms of (3.23) is the same by Fubini. -/
noncomputable def ctrlJ {c : ℕ → ℝ} (W : BrownianNoise c) (f : E3 → ℝ) (κ : ℝ → ℝ) (s : ℝ) (x : E3)
    (u : ℝ≥0 → W.Ω → E3) : ℝ :=
  ∫ ω, (f (x + W.noise 1 ω - W.noise s.toNNReal ω + ∫ r in s..1, κ r • u r.toNNReal ω)
    - (1 / 2) * ∫ r in s..1, κ r * ‖u r.toNNReal ω‖ ^ 2) ∂W.P

end QPSpinParisi


