-- Prove2me | Definitions.Def_QPSpinParisi_gBeta
-- name    : QPSpinParisi_gBeta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:00:38.585672+00:00
-- url     : https://prove2.me/theorems/f47f867d-20fd-484a-9798-5ac86de86469
-- title:
--   The terminal function $g_\beta$
-- statement:
--   For $\beta>0$,
--   $$g_\beta(r)=\frac1\beta\log\frac{\sinh(\beta r)}{\beta r},\qquad g_\beta(0)=0.$$
--   It is the terminal function of the positive-temperature problem, and it approaches $r$ as $\beta\to\infty$.
--
--   **Formalization Note** Lean's conventions $x/0=0$ and $\log0=0$ give the printed value at $0$.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), p.17 (PDF p.17)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The terminal function `g_β(r) = (1/β) log(sinh(βr) / (βr))`, `g_β(0) = 0` (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), p.17, PDF p.17).

**Formalization Note** Lean's `x / 0 = 0` and `Real.log 0 = 0` give the printed `g_β(0) = 0`. -/
noncomputable def gBeta (β r : ℝ) : ℝ :=
  (1 / β) * Real.log (Real.sinh (β * r) / (β * r))

end QPSpinParisi


