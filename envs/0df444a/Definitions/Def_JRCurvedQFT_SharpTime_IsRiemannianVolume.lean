-- Prove2me | Definitions.Def_JRCurvedQFT_SharpTime_IsRiemannianVolume
-- name    : JRCurvedQFT_SharpTime_IsRiemannianVolume
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:36:34.477932+00:00
-- url     : https://prove2.me/theorems/550fbff3-bdb9-4c58-93d9-4ebc5d08325c
-- title:
--   Riemannian volume measure $\mathrm{dvol}$
-- statement:
--   A Borel measure $\mu$ on $M$ is the **Riemannian volume** $\mathrm{dvol}$ if, for every chart of $M$ and every measurable set $A$ inside the chart domain,
--   $$\mu(A)=\int_{x(A)}\sqrt{\det g_{ab}(x)}\,dx ,$$
--   with $dx$ the Lebesgue measure on $\mathbb R^d$. Since countably many charts cover $M$, this determines $\mu$.
--
--   The paper's $L^2(M)$, the covariance $C$ and the Sobolev norms all refer to this measure.
--
--   **Formalization Note** The volume is characterized rather than constructed, and theorems quantify over every measure with this property (it exists and is unique).
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral, arXiv:hep-th/0609003v1, §1, p. 3 ("the Riemannian volume measure on M, which we sometimes denote by dvol"); Eq. (4.2), p. 21

import Mathlib
import Definitions.Def_JRCurvedQFT_SharpTime_chartGram

open scoped Manifold ContDiff ENNReal Topology
open Bundle MeasureTheory

namespace JRCurvedQFT.SharpTime

variable {d : ℕ} {M : Type} [EMetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]

/-- `μ` is the **Riemannian volume measure** `dvol` of `M`.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral*, arXiv:hep-th/0609003v1, p. 3: "The notation L²(M) is used when M is a C^∞ Riemannian manifold, and implicitly refers
to the Riemannian volume measure on M, which we sometimes denote by dvol"; in coordinates the
density is `√𝒢`, `𝒢 = det(g_ab)` ((4.2), p. 21).

The predicate says: for every chart (the chart of `M` at `p`) and every measurable `A` inside its
source, `μ(A) = ∫_{chart(A)} √det g_ab(x) dx` (Lebesgue measure on ℝ^d).

**Formalization Note** Reading 4: the measure is given by this characterization (it determines
`μ`, since countably many charts cover `M`) instead of a construction; theorems quantify over every
`μ` satisfying it. -/
def IsRiemannianVolume [MeasurableSpace M] (μ : Measure M) : Prop :=
  ∀ (p : M) (A : Set M), MeasurableSet A →
    A ⊆ (chartAt (EuclideanSpace ℝ (Fin d)) p).source →
    μ A = ∫⁻ x in extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) p '' A,
      ENNReal.ofReal (Real.sqrt (chartGram p x).det)

end JRCurvedQFT.SharpTime


