-- Prove2me | Definitions.Def_TeschlQM_OneParticle_freeHamiltonian
-- name    : TeschlQM_OneParticle_freeHamiltonian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T07:30:15.322811+00:00
-- url     : https://prove2.me/theorems/6c533e1f-db9b-4886-a10f-6211d8eb4e07
-- title:
--   Sobolev space H²(ℝⁿ) and the free Schrödinger operator H₀ = −Δ (7.12), (7.22)–(7.23)
-- statement:
--   Let $\hat f$ denote the Fourier transform of $f \in L^2(\mathbb R^n)$. The **Sobolev space** of order two is
--   $$H^2(\mathbb R^n) = \{ f \in L^2(\mathbb R^n) \mid |p|^2 \hat f(p) \in L^2(\mathbb R^n) \},$$
--   and the **free Schrödinger operator** is
--   $$H_0 \psi = -\Delta \psi = \big(p^2 \hat\psi(p)\big)^\vee, \qquad \mathfrak D(H_0) = H^2(\mathbb R^n),$$
--   that is, $H_0$ is unitarily equivalent, via the Fourier transform, to the maximally defined operator of multiplication by $p^2$. Units are $\hbar = 1$ and mass $m = 1/2$.
--
--   This is the unperturbed Hamiltonian of a free nonrelativistic particle; the one-particle Schrödinger operators of the chapter are its perturbations $H_0 + V$.
--
--   **Formalization Note.** The Fourier transform is Mathlib's unitary $L^2$ extension `Lp.fourierTransformₗᵢ` of $\hat f(\xi) = \int e^{-2\pi i \langle x, \xi\rangle} f(x)\,d^n x$, not Teschl's $(2\pi)^{-n/2}\int e^{-ipx} f(x)\, d^nx$ of (7.3). In this normalization the symbol of $-\Delta$ is $(2\pi|\xi|)^2$ (Teschl's $p^2$ at $p = 2\pi\xi$), so `freeHamiltonian n` $= \mathcal F^{-1} (2\pi|\xi|)^2 \mathcal F$ is exactly $-\Delta$ and `sobolevH2 n` $= \{ f \mid (2\pi|\xi|)^2 \mathcal F f \in L^2\}$ is exactly $H^2(\mathbb R^n)$; neither depends on the normalization.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 167, Section 7.2, Eqs. (7.12), (7.22)–(7.24)

import Mathlib
import Definitions.Def_TeschlQM_OneParticle_multiplicationOperator

namespace TeschlQM.OneParticle

open MeasureTheory

/-- The Fourier transform on `L²(ℝⁿ)`, Mathlib's unitary extension `Lp.fourierTransformₗᵢ` of
`f̂(ξ) = ∫ e^{-2πi⟨x, ξ⟩} f(x) dⁿx`. It differs from Teschl's `F` of (7.3),
`f̂(p) = (2π)^{-n/2} ∫ e^{-ipx} f(x) dⁿx`, by the substitution `p = 2πξ` and a constant factor;
the definitions below are written so that they do not depend on that choice. -/
noncomputable def fourierL2 (n : ℕ) : L2 n ≃ₗᵢ[ℂ] L2 n :=
  Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin n)) ℂ

/-- The symbol of `-Δ` in Mathlib's normalization of the Fourier transform: `(2π|ξ|)²`, which is
Teschl's `p²` of (7.22) at `p = 2πξ`. -/
noncomputable def laplaceSymbol (n : ℕ) (ξ : EuclideanSpace ℝ (Fin n)) : ℂ :=
  (((2 * Real.pi * ‖ξ‖) ^ 2 : ℝ) : ℂ)

/-- Teschl (7.12), p. 164, with `r = 2`: the Sobolev space
`H²(ℝⁿ) = {f ∈ L²(ℝⁿ) | |p|² f̂(p) ∈ L²(ℝⁿ)}`. Membership does not depend on the normalization
of the Fourier transform, since `(2π|ξ|)²` is a constant multiple of `|ξ|²`. -/
noncomputable def sobolevH2 (n : ℕ) : Submodule ℂ (L2 n) :=
  (multDomain (laplaceSymbol n)).comap (fourierL2 n).toLinearEquiv.toLinearMap

/-- Teschl (7.22)–(7.23), p. 167: the **free Schrödinger operator** `H₀ψ = -Δψ` with
`𝔇(H₀) = H²(ℝⁿ)`, i.e. `H₀ = F⁻¹ p² F`: Fourier transform, multiplication by the symbol of `-Δ`
(maximally defined, (7.24)), inverse Fourier transform. Units `ℏ = 1`, `m = 1/2`. -/
noncomputable def freeHamiltonian (n : ℕ) : L2 n →ₗ.[ℂ] L2 n where
  domain := sobolevH2 n
  toFun := (fourierL2 n).symm.toLinearEquiv.toLinearMap ∘ₗ (multOp (laplaceSymbol n)).toFun ∘ₗ
    (fourierL2 n).toLinearEquiv.toLinearMap.restrict (q := (multOp (laplaceSymbol n)).domain)
      (fun _ hψ => hψ)

end TeschlQM.OneParticle


