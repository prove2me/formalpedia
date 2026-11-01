-- Prove2me | Definitions.Def_JRCurvedQFT_SharpTime_omegaSqCore
-- name    : JRCurvedQFT_SharpTime_omegaSqCore
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:37:27.689126+00:00
-- url     : https://prove2.me/theorems/3cf0eccd-429b-429d-8996-d06e0a2d8eae
-- title:
--   The operator $\omega^2=F^{1/2}(-Q+m^2)F^{1/2}$ on $C_c^\infty(\Sigma)$
-- statement:
--   On test functions $f$ on $\Sigma$ define
--   $$\omega^2 f=F^{1/2}\big(-Q+m^2\big)\big(F^{1/2}f\big),$$
--   the operator $\sqrt F\mu^2\sqrt F$ of Theorem 4.3 with $\mu^2=-Q+m^2$. Since $F>0$ is smooth, $F^{\pm1/2}$ preserves $C_c^\infty(\Sigma)$.
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral, arXiv:hep-th/0609003v1, Theorem 4.3, p. 23

import Mathlib
import Definitions.Def_JRCurvedQFT_SharpTime_laplaceBeltrami
import Definitions.Def_JRCurvedQFT_SharpTime_StaticStructure

open scoped Manifold ContDiff ENNReal Topology
open Bundle MeasureTheory

namespace JRCurvedQFT.SharpTime

variable {d : ℕ} {M : Type} [EMetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]

/-- The operator `ω² = √F μ² √F = F^{1/2}(−Q + m²)F^{1/2}` on (lifts of) test functions on `Σ`.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral*, arXiv:hep-th/0609003v1, Theorem 4.3, p. 23: "µ = (−Q + m²)^{1/2} and ω = (√F µ² √F)^{1/2}".

`omegaSqCore f = √F · (−Q(√F f) + m² √F f)`, with `Q` the Laplace–Beltrami operator of the
ξ-invariant lift ((4.3)).

**Formalization Note** Reading 8: this is the symmetric operator on `C_c^∞(Σ)` whose Friedrichs
extension is `ω²` (`IsOmegaSq`). `F > 0` is smooth, so `F^{±1/2}` preserves `C_c^∞(Σ)`. -/
noncomputable def omegaSqCore (S : StaticStructure (d := d) M) (m : ℝ) (f : M → ℝ) : M → ℝ :=
  fun p => Real.sqrt (S.lapse p) *
    (-laplaceBeltrami (d := d) (fun q => Real.sqrt (S.lapse q) * f q) p
      + m ^ 2 * (Real.sqrt (S.lapse p) * f p))

end JRCurvedQFT.SharpTime


