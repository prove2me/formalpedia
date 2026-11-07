-- Prove2me | Definitions.Def_FourierEntropyApprox_fourierCoeff
-- name    : FourierEntropyApprox_fourierCoeff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:44:14.790029+00:00
-- url     : https://prove2.me/theorems/d3824fe8-8f9e-44c0-999c-4d824c5ebc28
-- title:
--   Fourier coefficients $\widehat f(S)$, inner product, spectral norm $\|\widehat f\|_1$ and $\|f\|_2^2$ on the cube
-- statement:
--   Let $f,g:\{-1,1\}^n\to\mathbb C$ (or $\mathbb R$). The **inner product** is $\langle f,g\rangle=\mathbb E_x[\overline{f(x)}\,g(x)]$, and the **Fourier coefficient** of $f$ at $S\subseteq[n]$ is
--
--   $$\widehat f(S)=\langle\chi_S,f\rangle=\mathbb E_x[f(x)\chi_S(x)] ,$$
--
--   so that $f=\sum_{S\subseteq[n]}\widehat f(S)\chi_S$. The **spectral norm** of $f$ and the squared **2-norm** of $f$ are
--
--   $$\|\widehat f\|_1=\sum_{S\subseteq[n]}|\widehat f(S)| ,\qquad \|f\|_2^2=\mathbb E_x\big[|f(x)|^2\big].$$
--
--   The spectral norm measures how expensive $f$ is to write as a combination of characters; it is the complexity measure that the approximate spectral norm relaxes. The 2-norm is the distance used by the approximation hypotheses of Theorem 3.1.
--
--   **Formalization Note** Since $\chi_S$ is real, no conjugation appears in $\widehat f(S)$. The inner product is `cubeInner`, conjugate-linear in its first argument. All four objects are defined for values in any `RCLike` field ($\mathbb R$ or $\mathbb C$); $|\cdot|$ is the absolute value or the complex modulus.
-- source:
--   Paraashar, Saurabh, Fourier Entropy Bounds via Approximations, arXiv:2611.06451 (held version, sha256 adc9c5fc…), §2, p.8 (PDF p.8): inner product, Fourier expansion, spectral norm

import Mathlib
import Definitions.Def_FourierEntropyApprox_Cube

namespace FourierEntropyApprox

/-!
# Fourier coefficients, inner product, spectral norm and squared 2-norm on the cube

M. Paraashar, N. Saurabh, *Fourier Entropy Bounds via Approximations*, arXiv:2611.06451 (held version,
sha256 adc9c5fc…), §2, p.8: "every complex-valued function f : {−1, 1}ⁿ → ℂ has a unique Fourier expansion
f(x) = ∑_{S⊆[n]} f̂(S)χ_S(x). […] The spectral norm ‖f̂‖₁ of f is defined to be ∑_S |f̂(S)|."

**Formalization Note.**
* The coefficient is `f̂(S) = ⟨χ_S, f⟩ = 𝔼ₓ[f(x)χ_S(x)]` (the inner product of p.8, with `χ_S` real so no
  conjugation is visible).
* `cubeInner f g = 𝔼ₓ[f(x)‾ g(x)]` is the inner product of p.8, conjugate-linear in the first slot.
* `l2NormSq f = 𝔼ₓ|f(x)|²` is `‖f‖₂²`, the squared norm of that inner product.
* Everything is stated for an arbitrary `RCLike` field `𝕜` (ℝ or ℂ); `‖·‖` is the absolute value or modulus.
-/

/-- The Fourier coefficient `f̂(S) = 𝔼ₓ[f(x) χ_S(x)]` (§2, p.8). -/
noncomputable def fourierCoeff {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (f : Cube n → 𝕜)
    (S : Finset (Fin n)) : 𝕜 :=
  avg (fun x => f x * (walsh S x : 𝕜))

/-- The inner product `⟨f, g⟩ = 𝔼ₓ[f(x)‾ g(x)]` (§2, p.8). -/
noncomputable def cubeInner {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (f g : Cube n → 𝕜) : 𝕜 :=
  avg (fun x => star (f x) * g x)

/-- The spectral norm `‖f̂‖₁ = ∑_S |f̂(S)|` (§2, p.8). -/
noncomputable def spectralNorm {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (f : Cube n → 𝕜) : ℝ :=
  ∑ S : Finset (Fin n), ‖fourierCoeff f S‖

/-- The squared 2-norm `‖f‖₂² = 𝔼ₓ|f(x)|²` (§2, p.8; used in Theorem 3.1, p.14). -/
noncomputable def l2NormSq {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (f : Cube n → 𝕜) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ * ∑ x, ‖f x‖ ^ 2

end FourierEntropyApprox


