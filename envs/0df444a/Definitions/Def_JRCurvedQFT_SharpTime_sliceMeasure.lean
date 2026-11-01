-- Prove2me | Definitions.Def_JRCurvedQFT_SharpTime_sliceMeasure
-- name    : JRCurvedQFT_SharpTime_sliceMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:36:43.341996+00:00
-- url     : https://prove2.me/theorems/9dcaa07b-bcc8-4f61-a583-2ea8af3fe0cc
-- title:
--   The measure $\sqrt{\mathcal G}\,dx$ on the slice $\Sigma$
-- statement:
--   The measure $\nu=\sqrt{\mathcal G}\,dx$ on $\Sigma$ of (4.6), with $\mathcal G=F\det(G_{\mu\nu})$, is defined as the volume of unit time-slabs:
--   $$\nu(A)=\mathrm{vol}\big(\{p\in M:\ 0\le t(p)\le 1,\ \phi_{-t(p)}(p)\in A\}\big).$$
--   Because $\mathrm{dvol}=\sqrt{\mathcal G}\,dx\,dt$ in static coordinates and $\mathcal G$ does not depend on $t$, this is $\int_{A\cap\Sigma}\sqrt{\mathcal G}\,dx$. The Hilbert space $\mathcal K_\Sigma=L^2(\Sigma,\sqrt{\mathcal G}\,dx)$ is $L^2(\nu)$.
--
--   **Formalization Note** $\nu$ is a measure on $M$ concentrated on $\Sigma$ (the push-forward of the slab volume by the projection to $\Sigma$).
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral, arXiv:hep-th/0609003v1, Eq. (4.6), p. 21; Eq. (4.2), p. 21

import Mathlib
import Definitions.Def_JRCurvedQFT_SharpTime_StaticStructure

open scoped Manifold ContDiff ENNReal Topology
open Bundle MeasureTheory

namespace JRCurvedQFT.SharpTime

variable {d : ℕ} {M : Type} [EMetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]

/-- The measure `√𝒢 dx` on the time-zero slice `Σ`, as a measure on `M` concentrated on `Σ`.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral*, arXiv:hep-th/0609003v1, (4.6), p. 21: `𝒦_Σ := L²(Σ, √𝒢 dx)`, "Here √𝒢 dx denotes the Borel measure on Σ which has
the indicated form in each local coordinate system, and 𝒢 = FG as in eq. (4.2)".

Definition: `ν(A) = vol{p : 0 ≤ t(p) ≤ 1, φ_{−t(p)}(p) ∈ A}`, the volume of the unit time-slab over
`A ∩ Σ`. Since `dvol = √𝒢 dx dt` with `𝒢` independent of `t`, this is `∫_{A∩Σ} √𝒢 dx`.

**Formalization Note** The projection `p ↦ φ_{−t(p)}(p)` is continuous (the flow and `t` are
smooth), so the push-forward is not the junk zero measure. -/
noncomputable def sliceMeasure [MeasurableSpace M] (S : StaticStructure (d := d) M)
    (μ : Measure M) : Measure M :=
  (μ.restrict {p | 0 ≤ S.time p ∧ S.time p ≤ 1}).map S.sliceProj

end JRCurvedQFT.SharpTime


