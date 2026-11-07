-- Prove2me | Definitions.Def_QPSpinParisi_AY
-- name    : QPSpinParisi_AY
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:04:27.027864+00:00
-- url     : https://prove2.me/theorems/9862acdf-f181-436b-9aac-674af0692afd
-- title:
--   The free energy $A^Y_n(\beta)$
-- statement:
--   The free energy of a realization of $Y_n$, defined as for $X_n$:
--   $$A^Y_n(\beta)=\frac1n\mathbb E\log\int_{(S^2)^n}\exp\{\beta Y_n(s)\}\,\nu^{\otimes n}(ds).$$
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), p.11 (PDF p.11)

import Mathlib
import Definitions.Def_QPSpinParisi_OverlapField

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The free energy `A^Y_n(β)`, "defined analogously" to `A^X_n(β)` (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), p.11, PDF p.11), for a realization `F` of
the field `Y_n`. -/
noncomputable def AY {c : ℕ → ℝ} {n : ℕ} (F : OverlapField c n) (β : ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∫ ω, Real.log (∫ s, Real.exp (β * F.Y s ω) ∂(RGGDetect.prior n 3)) ∂F.P

end QPSpinParisi


