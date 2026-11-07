-- Prove2me | Definitions.Def_QPSpinParisi_gaussMeas
-- name    : QPSpinParisi_gaussMeas
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:02:30.263008+00:00
-- url     : https://prove2.me/theorems/4d4b6d01-1115-41cb-a86a-f246a0cb8d09
-- title:
--   The law of the coefficient vector $\alpha$
-- statement:
--   The coefficients $\alpha[\bar i,\bar a]$ are i.i.d. standard normal. This item is their joint law: the product of standard Gaussians over all indices, on a finite-dimensional space depending on $n$. Every expectation of $E^\star_{n,\mathrm{prod}}$ and $X_n$ is taken under it.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), §2.1, p.3 (PDF p.3)

import Mathlib
import Definitions.Def_QPSpinParisi_Idx

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The law of the coefficient vector `α` (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), §2.1, p.3, PDF p.3: "`α[ī, ā]` are i.i.d. standard normal
coefficients"): the product of standard Gaussians over `Idx n`.

**Formalization Note** The probability space is the finite-dimensional canonical one, and it changes with `n`. -/
noncomputable def gaussMeas (n : ℕ) : Measure (Idx n → ℝ) :=
  Measure.pi fun _ : Idx n => gaussianReal 0 1

instance gaussMeas.instIsProbabilityMeasure (n : ℕ) : IsProbabilityMeasure (gaussMeas n) := by
  unfold gaussMeas; infer_instance

end QPSpinParisi


