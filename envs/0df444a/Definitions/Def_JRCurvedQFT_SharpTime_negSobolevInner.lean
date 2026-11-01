-- Prove2me | Definitions.Def_JRCurvedQFT_SharpTime_negSobolevInner
-- name    : JRCurvedQFT_SharpTime_negSobolevInner
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:38:00.06532+00:00
-- url     : https://prove2.me/theorems/677e87f8-3945-4265-b50e-78aaf88dc00a
-- title:
--   $H_{-1}$ inner product $\langle \ell_1, C\ell_2\rangle$
-- statement:
--   The **$H_{-1}$ inner product** of two functionals is defined by polarization:
--   $$\langle\ell_1,C\ell_2\rangle=\tfrac14\big(\|\ell_1+\ell_2\|_{-1}^2-\|\ell_1-\ell_2\|_{-1}^2\big).$$
--   For functions $f,g$ it is $\langle f,Cg\rangle_{L^2(M)}$; for sharp-time distributions it is the quantity $\langle f_t,Cg_s\rangle_M$ of Theorem 4.3.
--
--   **Formalization Note** Meaningful for elements of $H_{-1}(M)$; every statement using it asserts or assumes that membership.
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral, arXiv:hep-th/0609003v1, §1.3, p. 4, Eq. (1.2); Theorem 4.3, p. 23

import Mathlib
import Definitions.Def_JRCurvedQFT_SharpTime_negSobolevNorm

open scoped Manifold ContDiff ENNReal Topology
open Bundle MeasureTheory

namespace JRCurvedQFT.SharpTime

variable {d : ℕ} {M : Type} [EMetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]

/-- The **`H₋₁(M)` inner product** `⟨ℓ₁, C ℓ₂⟩`, by polarization of the norm `‖·‖₋₁`:
`(‖ℓ₁ + ℓ₂‖²₋₁ − ‖ℓ₁ − ℓ₂‖²₋₁) / 4`.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral*, arXiv:hep-th/0609003v1, §1.3, p. 4, (1.2): `‖f‖²₋₁ = ⟨f, Cf⟩`; so `⟨f, Cg⟩_{L²(M)}` is the polarized `H₋₁` inner
product, and `⟨f_t, C g_s⟩_M` in Theorem 4.3, p. 23, is this pairing of two sharp-time
distributions.

**Formalization Note** Reading 4. Meaningful for `ℓ₁, ℓ₂ ∈ H₋₁(M)` (finite norms); every statement
that uses it also asserts or assumes that membership. -/
noncomputable def negSobolevInner [MeasurableSpace M] (μ : Measure M) (m : ℝ)
    (ℓ₁ ℓ₂ : (M → ℝ) → ℝ) : ℝ :=
  ((negSobolevNorm (d := d) μ m (ℓ₁ + ℓ₂)).toReal ^ 2
    - (negSobolevNorm (d := d) μ m (ℓ₁ - ℓ₂)).toReal ^ 2) / 4

end JRCurvedQFT.SharpTime


