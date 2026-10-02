-- Prove2me | Definitions.Def_TeschlQM_Atomic_freeHamiltonian
-- name    : TeschlQM_Atomic_freeHamiltonian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T08:41:37.81053+00:00
-- url     : https://prove2.me/theorems/af574158-ebdd-4444-b3ef-905cbbde7055
-- title:
--   Free Schrödinger operator H₀ = −Δ on H²(ℝⁿ) (7.12), (7.23)
-- statement:
--   The **Sobolev space** $H^2(\mathbb R^n)$ is $\{ f \in L^2(\mathbb R^n) \mid |p|^2 \hat f(p) \in L^2(\mathbb R^n) \}$, where $\hat f$ is the Fourier transform. The **free Schrödinger operator** is
--   $$H_0 \psi = -\Delta\psi = \big(|p|^2 \hat\psi(p)\big)^\vee, \qquad \mathfrak D(H_0) = H^2(\mathbb R^n),$$
--   in units with $\hbar = 1$ and particle mass $m = 1/2$; it is unitarily equivalent, via the Fourier transform, to the maximally defined multiplication operator by $|p|^2$.
--
--   It is the kinetic energy part of every Hamiltonian in the chapter.
--
--   **Formalization Note.** $\mathbb R^n$ is `EuclideanSpace ℝ ι` for a finite type `ι` with Lebesgue measure `volume`. The Fourier transform is Mathlib's unitary $L^2$ transform `Lp.fourierTransformₗᵢ`, which extends $\mathcal F\psi(\xi) = \int e^{-2\pi i \langle x, \xi\rangle} \psi(x)\,dx$ (not Teschl's $(2\pi)^{-n/2}\int e^{-ipx}$). In this normalization $-\Delta$ is the multiplier $4\pi^2 \|\xi\|^2$, so `freeHamiltonian ι` $= \mathcal F^{-1} \circ (4\pi^2\|\xi\|^2 \cdot) \circ \mathcal F$ with domain $\{\psi \mid 4\pi^2\|\xi\|^2 \mathcal F\psi \in L^2\}$, which is exactly $H^2(\mathbb R^n)$; the operator is the same $-\Delta$ as in the book.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 164, Eq. (7.12), and p. 167, Eqs. (7.20)–(7.23)

import Mathlib
import Definitions.Def_TeschlQM_Atomic_mulOp

namespace TeschlQM.Atomic

open MeasureTheory

/-- Teschl (7.12), p. 164, and (7.20)–(7.23), p. 167: the **free Schrödinger operator** `H₀ = -Δ` in
`L²(ℝⁿ)` (units `ℏ = 1`, `m = 1/2`), with domain the Sobolev space
`H²(ℝⁿ) = {ψ ∈ L²(ℝⁿ) | |p|² ψ̂(p) ∈ L²(ℝⁿ)}`, defined as the Fourier multiplier `H₀ = F⁻¹ |p|² F`.
Here `ℝⁿ` is `EuclideanSpace ℝ ι` and `F` is Mathlib's unitary `L²` Fourier transform
`𝓕 ψ(ξ) = ∫ e^{-2πi⟨x, ξ⟩} ψ(x) dx`; with this normalization `-Δ` is the multiplier
`4π²‖ξ‖²` (Teschl's `F` gives `|p|²` with `p = 2πξ`). The domain is
`{ψ | 4π²‖ξ‖² 𝓕ψ ∈ L²}`, which is exactly `H²(ℝⁿ)`: the constant does not change the set. -/
noncomputable def freeHamiltonian (ι : Type*) [Fintype ι] :
    Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)) →ₗ.[ℂ]
      Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)) where
  domain := (mulOpDomain volume
      (fun ξ : EuclideanSpace ℝ ι => ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ))).comap
    (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ ι) ℂ).toLinearEquiv.toLinearMap
  toFun :=
    (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ ι) ℂ).symm.toLinearEquiv.toLinearMap ∘ₗ
      (mulOp volume
        (fun ξ : EuclideanSpace ℝ ι => ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ))).toFun ∘ₗ
      ((Lp.fourierTransformₗᵢ (EuclideanSpace ℝ ι) ℂ).toLinearEquiv.toLinearMap.restrict
        (fun _ hx => Submodule.mem_comap.1 hx))

end TeschlQM.Atomic


