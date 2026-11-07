-- Prove2me | Definitions.Def_QPSpinParisi_gaussE3
-- name    : QPSpinParisi_gaussE3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:02:04.400558+00:00
-- url     : https://prove2.me/theorems/7370c0bd-60c4-4096-a087-c7aba3af7f10
-- title:
--   The centered Gaussian law $N(0,vI_3)$ on $\mathbb R^3$
-- statement:
--   The law on $\mathbb R^3$ of a vector with independent centered Gaussian coordinates of variance $v\ge0$. These are the Gaussian increments of the cascade recursion.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), p.20 (PDF p.20)

import Mathlib
import Definitions.Def_QPSpinParisi_E3

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The centered Gaussian law `N(0, v I₃)` on `ℝ³` (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), p.20, PDF p.20), for `v ≥ 0`. -/
noncomputable def gaussE3 (v : ℝ) : Measure E3 :=
  (Measure.pi fun _ : Fin 3 => gaussianReal 0 v.toNNReal).map (WithLp.toLp 2)

end QPSpinParisi


