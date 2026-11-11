-- Prove2me | Definitions.Def_QNoiseStab_fourierKet
-- name    : QNoiseStab_fourierKet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:20:44.03063+00:00
-- url     : https://prove2.me/theorems/fd0d3059-b51c-4e63-a837-991216786a10
-- title:
--   Single-coordinate Fourier state $|\hat w\rangle=m^{-1/2}\sum_x\omega_m^{wx}|x\rangle$
-- statement:
--   Let $m\ge1$ and $\omega_m=e^{2\pi i/m}$. For $w\in\mathbb Z_m$ the Fourier basis state of $\mathbb C^{\mathbb Z_m}$ is
--
--   $$
--   |\hat w\rangle=\frac1{\sqrt m}\sum_{x\in\mathbb Z_m}\omega_m^{\,w x}\,|x\rangle .
--   $$
--
--   The states $|\hat w\rangle$, $w\in\mathbb Z_m$, form an orthonormal basis; $|\hat 0\rangle$ is the uniform superposition.
--
--   **Formalization Note** The exponent $wx$ is computed in $\mathbb Z_m$ and read in $\{0,\dots,m-1\}$, which gives the same power of the primitive root $\omega_m$.
-- source:
--   Beame–Holman–Kornerup, A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), §2.3, pp.8–9 (|ŵ⟩)

import Mathlib

namespace QNoiseStab

/-- The single-coordinate Fourier basis state `|ŵ⟩ = m^{-1/2} Σ_{x ∈ [m]} ω_m^{w x} |x⟩` of `ℂ^{Z_m}`
(Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query Complexity and Time-Space
Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), §2.3, pp.8–9:
"|ŵ⟩ = 1/√m Σ_{x∈[m]} ω_m^{w x} |x⟩"), with the primitive root `ω_m = exp(2πi/m)`.

**Formalization Note** The value at `x` is `(√m)⁻¹ · exp(2πi · (w * x).val / m)`, the product
`w * x` taken in `ZMod m` and read in `{0, …, m − 1}`; since `exp(2πi/m)^m = 1` this is
`ω_m^{w x}`. -/
noncomputable def fourierKet {m : ℕ} [NeZero m] (w : ZMod m) : EuclideanSpace ℂ (ZMod m) :=
  WithLp.toLp 2 fun x =>
    ((Real.sqrt m)⁻¹ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((w * x).val : ℂ) / (m : ℂ))

end QNoiseStab


