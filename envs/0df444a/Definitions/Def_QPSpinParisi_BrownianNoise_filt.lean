-- Prove2me | Definitions.Def_QPSpinParisi_BrownianNoise_filt
-- name    : QPSpinParisi_BrownianNoise_filt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:04:02.857512+00:00
-- url     : https://prove2.me/theorems/584f4772-dbf0-4e0e-9be7-3065c0e925bc
-- title:
--   The filtration of a noise
-- statement:
--   The Brownian filtration of the noise: the completed natural filtration of its Brownian motion $B$. Controls in (2.3) are progressively measurable with respect to it.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), §2.1, p.4 (PDF p.4)

import Mathlib
import Definitions.Def_QPSpinParisi_BrownianNoise

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The Brownian filtration of a noise (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), §2.1, p.4, PDF p.4). -/
noncomputable def BrownianNoise.filt {c : ℕ → ℝ} (W : BrownianNoise c) : Filtration ℝ≥0 W.mΩ :=
  brownVecFiltration W.P W.B

end QPSpinParisi


