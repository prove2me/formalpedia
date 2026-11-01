-- Prove2me | Definitions.Def_JRCurvedQFT_SharpTime_omegaSqForm
-- name    : JRCurvedQFT_SharpTime_omegaSqForm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:38:29.640794+00:00
-- url     : https://prove2.me/theorems/e939b7cf-3445-4484-94bd-c3138a018f18
-- title:
--   Quadratic form $\langle f,\omega^2 f\rangle_{\mathcal K_\Sigma}$
-- statement:
--   For a real test function $f$ on $\Sigma$,
--   $$\langle f,\omega^2f\rangle_{\mathcal K_\Sigma}=\int_\Sigma f\cdot F^{1/2}(-Q+m^2)(F^{1/2}f)\ \sqrt{\mathcal G}\,dx .$$
--   It describes the form domain of the Friedrichs extension of $\omega^2$.
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral, arXiv:hep-th/0609003v1, Theorem 4.3, p. 23; proof of Theorem 4.2, p. 22

import Mathlib
import Definitions.Def_JRCurvedQFT_SharpTime_omegaSqCore
import Definitions.Def_JRCurvedQFT_SharpTime_sliceMeasure

open scoped Manifold ContDiff ENNReal Topology
open Bundle MeasureTheory

namespace JRCurvedQFT.SharpTime

variable {d : ℕ} {M : Type} [EMetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]

/-- The quadratic form `⟨f, ω² f⟩_{𝒦_Σ} = ∫_Σ f · (F^{1/2}(−Q+m²)F^{1/2} f) √𝒢 dx` of `ω²` on
real test functions on `Σ`.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral*, arXiv:hep-th/0609003v1, Theorem 4.3, p. 23, and the proof of Theorem 4.2, p. 22 (the quadratic form of `−Q`).

**Formalization Note** Reading 8: used to describe the form domain of the Friedrichs extension. -/
noncomputable def omegaSqForm [MeasurableSpace M] (S : StaticStructure (d := d) M)
    (μ : Measure M) (m : ℝ) (f : M → ℝ) : ℝ :=
  ∫ x, f x * omegaSqCore S m f x ∂(sliceMeasure S μ)

end JRCurvedQFT.SharpTime


