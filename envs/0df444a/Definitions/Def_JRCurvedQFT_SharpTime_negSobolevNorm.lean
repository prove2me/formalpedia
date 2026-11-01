-- Prove2me | Definitions.Def_JRCurvedQFT_SharpTime_negSobolevNorm
-- name    : JRCurvedQFT_SharpTime_negSobolevNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:36:49.331125+00:00
-- url     : https://prove2.me/theorems/02dfbc34-adeb-4e56-8443-a0dd48bbb8b2
-- title:
--   Sobolev norm $\|\ell\|_{-1}$ (dual norm of $H_1(M)$)
-- statement:
--   For a functional $\ell$ on test functions and a mass $m$,
--   $$\|\ell\|_{-1}=\sup\big\{|\ell(u)|:\ u\in C_c^\infty(M,\mathbb R),\ q_m(u)\le 1\big\}\in[0,\infty].$$
--   This is the norm of $\ell$ as an element of the dual of the form space $H_1(M)$. For a function $f$ paired with test functions through $u\mapsto\int fu\,\mathrm{dvol}$ it equals $\langle f,Cf\rangle^{1/2}$, the norm (1.2) with $s=-1$.
--
--   **Formalization Note** Test objects (functions, sharp-time distributions) are represented as functionals on test functions; the value $\infty$ means the functional is not in $H_{-1}(M)$. On a complete manifold the completion of $C_c^\infty(M)$ in $q_m$ is the form domain of the self-adjoint operator $-\Delta+m^2$, so this is the paper's $H_{-1}(M)$ (Reading 4).
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral, arXiv:hep-th/0609003v1, §1.3, p. 4, Eq. (1.2) with s = −1

import Mathlib
import Definitions.Def_JRCurvedQFT_SharpTime_IsTestFunction
import Definitions.Def_JRCurvedQFT_SharpTime_formEnergy

open scoped Manifold ContDiff ENNReal Topology
open Bundle MeasureTheory

namespace JRCurvedQFT.SharpTime

variable {d : ℕ} {M : Type} [EMetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]

/-- The **Sobolev norm** `‖ℓ‖₋₁` of a linear functional `ℓ` on test functions: the dual norm
`sup { |ℓ(u)| : u ∈ C_c^∞(M), ‖u‖²₁ = q_m(u) ≤ 1 }`, with value in `[0, ∞]`.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral*, arXiv:hep-th/0609003v1, §1.3, p. 4, (1.2) with `s = −1`: `‖f‖²₋₁ = ⟨f, C f⟩`, `C = (−Δ + m²)⁻¹`. For a function `f`
paired with test functions by `u ↦ ∫ f u dvol`, the dual norm of the form space `H₁(M)` is
`‖C^{1/2} f‖ = ⟨f, Cf⟩^{1/2}`.

**Formalization Note** Reading 4: `H₋₁(M)` is the dual of the form space `H₁(M)`, the completion
of `C_c^∞(M)` in `q_m` (on a complete `M` this is the form domain of the self-adjoint `−Δ + m²`).
Test objects (functions, sharp-time distributions) are functionals `(M → ℝ) → ℝ`, of which only
the values on test functions matter. The value `∞` means "not in `H₋₁`". -/
noncomputable def negSobolevNorm [MeasurableSpace M] (μ : Measure M) (m : ℝ)
    (ℓ : (M → ℝ) → ℝ) : ℝ≥0∞ :=
  ⨆ (u : M → ℝ) (_ : IsTestFunction (d := d) u ∧ formEnergy (d := d) μ m u ≤ 1),
    ENNReal.ofReal |ℓ u|

end JRCurvedQFT.SharpTime


