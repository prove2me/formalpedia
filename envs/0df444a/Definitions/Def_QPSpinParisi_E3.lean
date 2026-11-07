-- Prove2me | Definitions.Def_QPSpinParisi_E3
-- name    : QPSpinParisi_E3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:00:44.195951+00:00
-- url     : https://prove2.me/theorems/040c5a98-ef45-4da6-be53-5a3045e0b70e
-- title:
--   $\mathbb R^3$ with the Euclidean norm
-- statement:
--   The space $\mathbb R^3$ with the Euclidean norm, in which controls, Brownian increments and Bloch vectors take values. The paper fixes this norm for all of its statements. The choice matters: the functional (2.3) is built from this norm, and a sup norm would define a different functional.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), §2.1, p.4 (PDF p.4)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- `ℝ³` with the Euclidean norm (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), §2.1, p.4, PDF p.4: "`∥.∥` denotes the Euclidean norm").

**Formalization Note** `Fin 3 → ℝ` would carry the sup norm, which is a different functional in (2.3). -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

end QPSpinParisi


