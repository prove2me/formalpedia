-- Prove2me | Definitions.Def_FractionalSpectralGP_IsRealHilbertBasis
-- name    : FractionalSpectralGP_IsRealHilbertBasis
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:22:58.265454+00:00
-- url     : https://prove2.me/theorems/67a782d7-4cbf-4202-a1cd-fef0bb6764fd
-- title:
--   Real-valued orthonormal basis $(h_n)_{n\ge0}$ of $L^2(\mathbb R,dx)$
-- statement:
--   A Hilbert basis $(h_n)_{n\ge0}$ of the complex space $L^2(\mathbb R,dx)$ is **real** if every $h_n$ is real-valued almost everywhere.
--
--   The paper takes $h_n$ to be the Hermite functions. Every statement of the mission is made for an arbitrary real orthonormal basis, of which the Hermite functions are an instance. Real-valuedness is what makes $Z_n=\widetilde{h_n}$ real standard Gaussian variables and the chaos functions $H_\alpha$ real.
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, §4, p.10; §5, p.12

import Mathlib

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- A Hilbert basis `(h_n)_{n ≥ 0}` of `L²(ℝ, dx; ℂ)` consisting of real-valued functions
(Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, §4, p.10 and §5, p.12: the Hermite functions `h₀, h₁, …`).

**Formalization Note.** The paper uses the Hermite functions. Every statement of this mission is
made for an arbitrary real-valued orthonormal basis, of which the Hermite functions are one
instance; real-valuedness is what makes `Z_n = h̃_n` real Gaussian variables. -/
def IsRealHilbertBasis (h : HilbertBasis ℕ ℂ (Lp ℂ 2 (volume : Measure ℝ))) : Prop :=
  ∀ n, ∀ᵐ x ∂(volume : Measure ℝ), ((h n : ℝ → ℂ) x).im = 0

end FractionalSpectralGP


