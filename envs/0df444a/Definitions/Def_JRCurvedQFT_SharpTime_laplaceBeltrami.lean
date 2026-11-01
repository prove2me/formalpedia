-- Prove2me | Definitions.Def_JRCurvedQFT_SharpTime_laplaceBeltrami
-- name    : JRCurvedQFT_SharpTime_laplaceBeltrami
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:36:28.537795+00:00
-- url     : https://prove2.me/theorems/2fee20a2-feb5-427d-9252-a686ad65a633
-- title:
--   Laplace–Beltrami operator $\Delta u=\mathcal G^{-1/2}\partial_a(\mathcal G^{1/2}g^{ab}\partial_b u)$
-- statement:
--   For a function $u$ on $M$ and a point $p$, the **Laplace–Beltrami operator** is
--   $$\Delta u(p)=\mathcal G^{-1/2}\,\partial_a\big(\mathcal G^{1/2}g^{ab}\,\partial_b u\big)$$
--   evaluated at $p$ in the chart of $M$ at $p$, with $\mathcal G=\det(g_{ab})$ and $g^{ab}$ the inverse matrix. For functions constant along the Killing trajectories (4.3) gives $\Delta_M u=Qu$ with $Q=\mathcal G^{-1/2}\partial_\mu(\sqrt{\mathcal G}G^{\mu\nu}\partial_\nu)$ (4.4), so on lifts of functions on $\Sigma$ this is the paper's operator $Q$.
--
--   **Formalization Note** The value does not depend on the chart for smooth $u$. $Q$ is the differential operator, not a quadratic form.
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral, arXiv:hep-th/0609003v1, p. 21, Eqs. (4.3)–(4.4) and the formula above (4.3)

import Mathlib
import Definitions.Def_JRCurvedQFT_SharpTime_chartGram

open scoped Manifold ContDiff ENNReal Topology
open Bundle MeasureTheory

namespace JRCurvedQFT.SharpTime

variable {d : ℕ} {M : Type} [EMetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]

/-- The **Laplace–Beltrami operator** `Δu = 𝒢^{−1/2} ∂_a(𝒢^{1/2} g^{ab} ∂_b u)` at `p`,
computed in the chart of `M` at `p`.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral*, arXiv:hep-th/0609003v1, p. 21: "Using the formula, Δf = 𝒢^{−1/2}∂_a(𝒢^{1/2} g^{ab}∂_b f), the Laplacian on M may be
seen to be Δ_M = (1/F)∂_t² + Q" ((4.3)), with `Q = 𝒢^{−1/2} ∂_μ(√𝒢 G^{μν} ∂_ν)` ((4.4)).

**Formalization Note** Pitfall 7: the operator is the chart formula (a differential operator), not
defined through a quadratic form. The value is chart-independent for smooth `u`; the chart at `p`
is used. For a ξ-invariant `u` (`∂_t u = 0`), (4.3) gives `Δ_M u = Q u`, so on the slice this is
the paper's `Q`. -/
noncomputable def laplaceBeltrami (u : M → ℝ) (p : M) : ℝ :=
  let x₀ := extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) p p
  let uc : EuclideanSpace ℝ (Fin d) → ℝ :=
    u ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) p).symm
  let V : Fin d → EuclideanSpace ℝ (Fin d) → ℝ := fun a x =>
    Real.sqrt (chartGram p x).det *
      ∑ b, (chartGram p x)⁻¹ a b * fderiv ℝ uc x (EuclideanSpace.single b 1)
  (Real.sqrt (chartGram p x₀).det)⁻¹ * ∑ a, fderiv ℝ (V a) x₀ (EuclideanSpace.single a 1)

end JRCurvedQFT.SharpTime


