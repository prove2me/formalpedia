-- Prove2me | Definitions.Def_FourierEntropyApprox_Cube
-- name    : FourierEntropyApprox_Cube
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:43:29.601626+00:00
-- url     : https://prove2.me/theorems/ceea6d5f-decb-479a-9f06-cb1af7395d2e
-- title:
--   The Boolean cube $\{-1,1\}^n$, its characters $\chi_S$ and the uniform average
-- statement:
--   The **Boolean cube** is $\{-1,1\}^n$ with the uniform probability measure. For a set of coordinates $S\subseteq[n]$, the **character** $\chi_S:\{-1,1\}^n\to\{-1,1\}$ is the product of the coordinates in $S$:
--
--   $$\chi_S(x)=\prod_{i\in S}x_i ,$$
--
--   with $\chi_\emptyset\equiv 1$. The **uniform average** of a function $F$ on the cube, with values in $\mathbb R$ or $\mathbb C$, is
--
--   $$\mathbb E_x[F(x)]=\frac{1}{2^n}\sum_{x\in\{-1,1\}^n}F(x).$$
--
--   These are the basic objects of Fourier analysis on the cube. Every other definition of the mission (Fourier coefficients, spectral norm, entropy, majority) is built from them.
--
--   **Formalization Note** A point of the cube is a function $\mathrm{Fin}\,n\to\mathrm{Bool}$, a coordinate $\mathrm{true}$ standing for $-1$ and $\mathrm{false}$ for $+1$ (`spin`). Coordinates are $0,\dots,n-1$ and a set $S$ is a `Finset (Fin n)`. The character is real valued (`walsh`). The average `avg` is defined for values in any `RCLike` field, i.e. $\mathbb R$ or $\mathbb C$.
-- source:
--   Paraashar, Saurabh, Fourier Entropy Bounds via Approximations, arXiv:2611.06451 (held version, sha256 adc9c5fc…), §2, p.8 (PDF p.8): the inner product and the character functions

import Mathlib

namespace FourierEntropyApprox

/-!
# The Boolean cube, its characters and the uniform average

M. Paraashar, N. Saurabh, *Fourier Entropy Bounds via Approximations*, arXiv:2611.06451 (held version,
sha256 adc9c5fc…), §2, p.8: "Consider the space of all functions from {−1, 1}ⁿ to ℂ equipped with the inner
product defined as ⟨f, g⟩ := 𝔼ₓ[f(x)‾ g(x)] = 1/2ⁿ ∑_{x∈{−1,1}ⁿ} f(x)‾ g(x). For S ⊆ [n], the character
function χ_S : {−1, 1}ⁿ → {−1, 1} is defined as χ_S(x) := ∏_{i∈S} xᵢ."

**Formalization Note.**
* The cube `{−1, 1}ⁿ` is `Fin n → Bool`, a point coordinate `true` standing for `−1` and `false` for `1`
  (`spin`). The coordinate set `[n]` is `Fin n` (0-based), and a set `S ⊆ [n]` is a `Finset (Fin n)`.
* The character `χ_S` is real valued (`walsh`); statements about `𝕜`-valued functions cast it into `𝕜`.
* The expectation `𝔼ₓ` under the uniform measure is `avg`, the sum over the `2ⁿ` points divided by `2ⁿ`,
  for values in any `RCLike` field `𝕜` (ℝ or ℂ).
-/

/-- The Boolean cube `{−1, 1}ⁿ`, as `Fin n → Bool` (`true ↦ −1`, `false ↦ 1`). -/
abbrev Cube (n : ℕ) : Type := Fin n → Bool

/-- The sign `±1` coded by a Boolean coordinate: `true ↦ −1`, `false ↦ 1`. -/
def spin (b : Bool) : ℝ := if b then -1 else 1

/-- The character `χ_S(x) = ∏_{i ∈ S} xᵢ` (§2, p.8). -/
def walsh {n : ℕ} (S : Finset (Fin n)) (x : Cube n) : ℝ := ∏ i ∈ S, spin (x i)

/-- The uniform average `𝔼ₓ[F(x)] = 2⁻ⁿ ∑ₓ F(x)` over the cube (§2, p.8). -/
noncomputable def avg {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (F : Cube n → 𝕜) : 𝕜 :=
  ((2 : 𝕜) ^ n)⁻¹ * ∑ x, F x

end FourierEntropyApprox


