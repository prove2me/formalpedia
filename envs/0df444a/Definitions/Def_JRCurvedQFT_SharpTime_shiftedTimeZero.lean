-- Prove2me | Definitions.Def_JRCurvedQFT_SharpTime_shiftedTimeZero
-- name    : JRCurvedQFT_SharpTime_shiftedTimeZero
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:37:41.851161+00:00
-- url     : https://prove2.me/theorems/46957947-d48e-4e25-b02f-6bf888de203f
-- title:
--   Time-zero distribution $(f^\tau)_0$ of $f^\tau=F^{-1/2}e^{-\tau\omega}F^{1/2}f$
-- statement:
--   Let $P_\omega$ be the projection-valued measure of $\omega^2$. For a function $f$ on $\Sigma$ and $\tau\in\mathbb R$, set $f^\tau=F^{-1/2}e^{-\tau\omega}F^{1/2}f$ (4.18). Its time-zero distribution $(f^\tau)_0$ is the functional
--   $$u\longmapsto\big\langle F^{-1/2}u|_\Sigma,\ e^{-\tau\omega}F^{1/2}f\big\rangle_{\mathcal K_\Sigma}=\int_\Sigma f^\tau\,u\ \sqrt{\mathcal G}\,dx$$
--   on test functions $u$, where $e^{-\tau\omega}=g(\omega^2)$ with $g(\lambda)=e^{-\tau\sqrt\lambda}$ is computed by the spectral form $\int g\,d\mu_{\varphi,\psi}$ of $P_\omega$.
--
--   **Formalization Note** $f^\tau$ is generally not smooth with compact support, so $(f^\tau)_0$ is defined by its pairing with test functions rather than as a sharp-time distribution of a test function.
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral, arXiv:hep-th/0609003v1, Eq. (4.18), p. 26

import Mathlib
import Definitions.Def_JRCurvedQFT_SharpTime_toKSigma
import Definitions.Def_JRCurvedQFT_SharpTime_sliceMeasure
import Definitions.Def_TeschlQM_Spectral_spectralIntegral

open scoped Manifold ContDiff ENNReal Topology
open Bundle MeasureTheory

namespace JRCurvedQFT.SharpTime

variable {d : ℕ} {M : Type} [EMetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]

/-- The time-zero distribution `(f^τ)₀` of `f^τ = F^{−1/2} e^{−τω} F^{1/2} f`, as a functional on
test functions: `u ↦ ⟨F^{−1/2} u, e^{−τω} F^{1/2} f⟩_{𝒦_Σ} = ∫_Σ f^τ u √𝒢 dx`.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral*, arXiv:hep-th/0609003v1, (4.18), p. 26: "f^t := (F^{−1/2} e^{−tω} F^{1/2}) f, where f is a function on Σ, and hence
so is f^t. Thus f^t₀(p, t′) = δ(t′)(F^{−1/2} e^{−tω} F^{1/2} f)(p) for p ∈ Σ."

`Pω` is the projection-valued measure of `ω²`, and `e^{−τω} = g(ω²)` with `g(λ) = e^{−τ√λ}`; the
pairing is the spectral form `∫ g dμ_{φ,ψ}` (`TeschlQM.Spectral.spectralForm`, conjugate-linear in
`φ`).

**Formalization Note** `f^τ` is generally not `C_c^∞` on `Σ`, so `(f^τ)₀` is not `sharpTime` of a test
function; it is defined by its pairing with test functions. `F^{−1/2} u` is continuous with compact
support on `Σ`, so it lies in `𝒦_Σ`; `g` is bounded, so the spectral form is finite. -/
noncomputable def shiftedTimeZero [MeasurableSpace M] (S : StaticStructure (d := d) M)
    (μ : Measure M)
    (Pω : Set ℝ → (Lp ℂ 2 (sliceMeasure S μ) →L[ℂ] Lp ℂ 2 (sliceMeasure S μ)))
    (τ : ℝ) (f : M → ℝ) : (M → ℝ) → ℝ :=
  fun u => (TeschlQM.Spectral.spectralForm Pω
    (toKSigma (sliceMeasure S μ) (fun x => ((Real.sqrt (S.lapse x))⁻¹ * u x : ℝ)))
    (toKSigma (sliceMeasure S μ) (fun x => (Real.sqrt (S.lapse x) * f x : ℝ)))
    (fun l => (Real.exp (-(τ * Real.sqrt l)) : ℂ))).re

end JRCurvedQFT.SharpTime


