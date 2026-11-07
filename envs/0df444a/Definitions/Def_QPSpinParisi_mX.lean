-- Prove2me | Definitions.Def_QPSpinParisi_mX
-- name    : QPSpinParisi_mX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:06:22.665228+00:00
-- url     : https://prove2.me/theorems/1979fbef-6b33-4cbf-964f-e3afccd26332
-- title:
--   The ground-state energy $m^X_n$
-- statement:
--   The normalized expected maximum of $X_n$:
--   $$m^X_n=\frac1n\mathbb E\max_{s\in(S^2)^n}X_n(s).$$
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), p.13 (PDF p.13)

import Mathlib
import Definitions.Def_QPSpinParisi_Xn
import Definitions.Def_QPSpinParisi_gaussMeas

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The ground-state energy `m^X_n = (1/n) E max_{s ∈ (S²)ⁿ} X_n(s)` (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), p.13, PDF p.13).

**Formalization Note** `X_n(·)` is continuous on a compact set, so the real `sSup` is the maximum. -/
noncomputable def mX (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  (1 / (n : ℝ)) * ∫ α, sSup (range (Xn c n α)) ∂(gaussMeas n)

end QPSpinParisi


