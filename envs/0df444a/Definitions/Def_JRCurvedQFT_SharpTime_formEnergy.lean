-- Prove2me | Definitions.Def_JRCurvedQFT_SharpTime_formEnergy
-- name    : JRCurvedQFT_SharpTime_formEnergy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:35:47.729879+00:00
-- url     : https://prove2.me/theorems/0078f07c-ef4f-4621-ac2d-093f3ff6ce81
-- title:
--   Form energy $q_m(u)=\int_M(|\nabla u|^2+m^2u^2)\,\mathrm{dvol}$
-- statement:
--   For a real function $u$ on $M$ and a mass $m$, the **form energy** is
--   $$q_m(u)=\int_M\big(|\nabla u|_g^2+m^2u^2\big)\,\mathrm{dvol},$$
--   where $|\nabla u|_g(p)$ is the norm of the differential $du_p$ with respect to the Riemannian norm on $T_pM$. For a test function $u$, $q_m(u)=\langle u,(-\Delta+m^2)u\rangle_{L^2(M)}=\|u\|_1^2$, the Sobolev norm (1.2) with $s=1$ ($C=(-\Delta+m^2)^{-1}$).
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral, arXiv:hep-th/0609003v1, §1.3, p. 4, Eq. (1.2)

import Mathlib

open scoped Manifold ContDiff ENNReal Topology
open Bundle MeasureTheory

namespace JRCurvedQFT.SharpTime

variable {d : ℕ} {M : Type} [EMetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]

/-- The **form energy** `q_m(u) = ∫_M (|∇u|²_g + m² u²) dvol = ⟨u, (−Δ + m²) u⟩_{L²(M)}`.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral*, arXiv:hep-th/0609003v1, §1.3, p. 4: `C = (−Δ + m²)⁻¹`, and `‖f‖²_s = ⟨f, C^{−s} f⟩` (1.2); for `s = 1` this is the
`H₁(M)` norm `‖u‖²₁ = ⟨u, (−Δ + m²) u⟩ = q_m(u)` on test functions.

`|∇u|_g(p)` is the norm of the differential `du_p : T_pM → ℝ` with respect to the Riemannian norm
on `T_pM` (the dual norm, equal to the length of the gradient).

**Formalization Note** Reading 4. The integral is a Bochner integral; it is finite for every test
function, which is the only use. -/
noncomputable def formEnergy [MeasurableSpace M] (μ : Measure M) (m : ℝ) (u : M → ℝ) : ℝ :=
  ∫ p, (‖mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, ℝ) u p‖ ^ 2 + m ^ 2 * u p ^ 2) ∂μ

end JRCurvedQFT.SharpTime


