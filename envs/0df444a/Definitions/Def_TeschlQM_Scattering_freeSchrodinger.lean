-- Prove2me | Definitions.Def_TeschlQM_Scattering_freeSchrodinger
-- name    : TeschlQM_Scattering_freeSchrodinger
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T10:22:19.362462+00:00
-- url     : https://prove2.me/theorems/d8b2d4f0-2b3b-4be1-9c0b-b6232456c8a3
-- title:
--   Free Schrödinger operator H₀ = −Δ on H²(ℝⁿ) and H = H₀ + V
-- statement:
--   On $L^2(\mathbb R^n)$ the **free Schrödinger operator** is $H_0 = -\Delta$ with domain the Sobolev space $H^2(\mathbb R^n)$ (units $\hbar = 1$, $m = \tfrac12$). Under the Fourier transform it is the maximally defined multiplication operator by $p^2$:
--   $$(\mathcal F H_0 \mathcal F^{-1})\varphi(p) = p^2\varphi(p), \qquad \mathfrak D(p^2) = \{\varphi \in L^2(\mathbb R^n) \mid p^2\varphi(p) \in L^2(\mathbb R^n)\}.$$
--   For a real function $V$ on $\mathbb R^n$, the **Schrödinger operator** $H = H_0 + V$ is the operator with $\mathfrak D(H) = \mathfrak D(H_0) = H^2(\mathbb R^n)$ and $(H\psi)(x) = (H_0\psi)(x) + V(x)\psi(x)$.
--
--   **Formalization Note.** $L^2(\mathbb R^n)$ is `Lp ℂ 2` on `EuclideanSpace ℝ (Fin n)` with Lebesgue measure. `IsFreeSchrodinger n H₀` characterizes $H_0$ through Mathlib's unitary $L^2$ Fourier transform $\mathcal F_M f(\xi) = \int \mathrm e^{-2\pi\mathrm i\langle x,\xi\rangle} f(x)\,dx$, not Teschl's $(2\pi)^{-n/2}\int \mathrm e^{-\mathrm ipx} f(x)\,dx$. The two differ by the dilation $p = 2\pi\xi$ and a constant, so $\mathfrak D(H_0) = \{\psi \mid |\xi|^2\mathcal F_M\psi \in L^2\}$ and $\mathcal F_M(H_0\psi)(\xi) = 4\pi^2|\xi|^2\mathcal F_M\psi(\xi)$ a.e. `IsSchrodingerOp n H₀ V H` says $\mathfrak D(H) = \mathfrak D(H_0)$ and $H\psi = H_0\psi + V\psi$ a.e. for each $\psi$ in it. Both predicates determine the operator uniquely.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 167, Section 7.2, Eqs. (7.20)–(7.24); p. 249, Theorem 12.4

import Mathlib

open MeasureTheory

namespace TeschlQM.Scattering

/-- The Hilbert space `L²(ℝⁿ)` of (classes of) square integrable complex functions on `ℝⁿ`
with Lebesgue measure; `ℝⁿ` is `EuclideanSpace ℝ (Fin n)`. -/
abbrev L2 (n : ℕ) : Type := Lp (α := EuclideanSpace ℝ (Fin n)) ℂ 2

/-- Teschl, p. 167, (7.20)–(7.24): `H₀` is the **free Schrödinger operator** `H₀ = −Δ` on
`L²(ℝⁿ)` with `𝔇(H₀) = H²(ℝⁿ)`, i.e. the operator unitarily equivalent under the Fourier
transform to the maximally defined multiplication operator by `p²`.
The Fourier transform used is Mathlib's unitary `L²` Fourier transform `𝓕`
(`𝓕f(ξ) = ∫ e^{−2πi⟨x,ξ⟩} f(x) dx`), not Teschl's `(2π)^{−n/2} ∫ e^{−ipx} f(x) dx`; the two
differ by the dilation `p = 2πξ` and a constant factor, so Teschl's `p² ψ̂(p)` becomes
`4π² |ξ|² 𝓕ψ(ξ)`:
`𝔇(H₀) = {ψ ∈ L² | |ξ|² 𝓕ψ ∈ L²}` (which is Teschl's `H²(ℝⁿ)`, (7.12)) and
`𝓕(H₀ψ)(ξ) = 4π² |ξ|² 𝓕ψ(ξ)` a.e. -/
def IsFreeSchrodinger (n : ℕ) (H₀ : L2 n →ₗ.[ℂ] L2 n) : Prop :=
  (∀ ψ : L2 n, ψ ∈ H₀.domain ↔
    MemLp (fun ξ : EuclideanSpace ℝ (Fin n) =>
      ((‖ξ‖ ^ 2 : ℝ) : ℂ) * (FourierTransform.fourier ψ : L2 n) ξ) 2) ∧
  ∀ ψ : H₀.domain,
    (FourierTransform.fourier (H₀ ψ) : L2 n) =ᵐ[volume]
      fun ξ : EuclideanSpace ℝ (Fin n) =>
        ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) * (FourierTransform.fourier (ψ : L2 n) : L2 n) ξ

/-- Teschl, p. 221, Sec. 10.1 and p. 249, Thm 12.4: `H` is the **Schrödinger operator**
`H = H₀ + V` with the real potential `V`, i.e. `𝔇(H) = 𝔇(H₀) = H²(ℝⁿ)` and
`(Hψ)(x) = (H₀ψ)(x) + V(x) ψ(x)` for almost every `x`, for every `ψ ∈ 𝔇(H)`.
(In particular `Vψ ∈ L²` for every `ψ ∈ 𝔇(H₀)`.) -/
def IsSchrodingerOp (n : ℕ) (H₀ : L2 n →ₗ.[ℂ] L2 n) (V : EuclideanSpace ℝ (Fin n) → ℝ)
    (H : L2 n →ₗ.[ℂ] L2 n) : Prop :=
  H.domain = H₀.domain ∧
  ∀ (ψ : H.domain) (ψ₀ : H₀.domain), (ψ : L2 n) = ψ₀ →
    (H ψ : L2 n) =ᵐ[volume] fun x : EuclideanSpace ℝ (Fin n) =>
      (H₀ ψ₀ : L2 n) x + (V x : ℂ) * (ψ : L2 n) x

end TeschlQM.Scattering


