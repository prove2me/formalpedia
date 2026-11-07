-- Prove2me | Definitions.Def_QPSpinParisi_mY
-- name    : QPSpinParisi_mY
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:04:35.740617+00:00
-- url     : https://prove2.me/theorems/616949b4-c2fc-4119-984c-3fe1c4417e50
-- title:
--   The ground-state energy $m^Y_n$
-- statement:
--   The normalized expected maximum of a realization of $Y_n$:
--   $$m^Y_n=\frac1n\mathbb E\max_{s\in(S^2)^n}Y_n(s).$$
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), p.13 (PDF p.13)

import Mathlib
import Definitions.Def_QPSpinParisi_OverlapField

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The ground-state energy `m^Y_n = (1/n) E max_{s ∈ (S²)ⁿ} Y_n(s)` (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), p.13, PDF p.13), for a realization `F` of
`Y_n`.

**Formalization Note** Almost every path is continuous on a compact set, so the real `sSup` is almost surely the
maximum. -/
noncomputable def mY {c : ℕ → ℝ} {n : ℕ} (F : OverlapField c n) : ℝ :=
  (1 / (n : ℝ)) * ∫ ω, sSup (range fun s => F.Y s ω) ∂F.P

end QPSpinParisi


