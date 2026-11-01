-- Prove2me | Definitions.Def_JRCurvedQFT_SharpTime_ofFunction
-- name    : JRCurvedQFT_SharpTime_ofFunction
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:35:45.024863+00:00
-- url     : https://prove2.me/theorems/4616caf5-28fb-4f7b-85c5-753081fb6d36
-- title:
--   A function as a test functional $u\mapsto\int fu\,\mathrm{dvol}$
-- statement:
--   A real function $f$ on $M$ defines the functional
--   $$u\longmapsto\int_M f\,u\ \mathrm{dvol}$$
--   on test functions. This is how functions in $L^2(M)$ and smooth test functions become elements of $H_{-1}(M)$, and how $\langle f,Cg\rangle_{L^2(M)}$ becomes the $H_{-1}$ inner product.
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral, arXiv:hep-th/0609003v1, §1.3, p. 4

import Mathlib

open scoped Manifold ContDiff ENNReal Topology
open Bundle MeasureTheory

namespace JRCurvedQFT.SharpTime

/-- A real function `f` on `M` as a functional on test functions: `u ↦ ∫_M f u dvol`.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral*, arXiv:hep-th/0609003v1, §1.3, p. 4: functions in `L²(M)` (and smooth functions) are test functions in `H₋₁(M)`
through this pairing; `⟨f, Cg⟩_{L²(M)}` is then the `H₋₁` inner product.

**Formalization Note** Reading 4. -/
noncomputable def ofFunction {M : Type} [MeasurableSpace M] (μ : Measure M) (f : M → ℝ) :
    (M → ℝ) → ℝ :=
  fun u => ∫ p, f p * u p ∂μ

end JRCurvedQFT.SharpTime


