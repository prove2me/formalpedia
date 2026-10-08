-- Prove2me | Definitions.Def_QuantumLinSys_Fourier_Setting
-- name    : QuantumLinSys_Fourier_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T10:18:19.960517+00:00
-- url     : https://prove2.me/theorems/e01f3265-b13d-4add-83e9-3cd1628701b0
-- title:
--   The Gaussian Fourier integral and sum of (18) and (21)
-- statement:
--   For a condition number $\kappa$, use the shared spectral domain
--   $$
--   D_\kappa=[-1,-1/\kappa]\cup[1/\kappa,1].
--   $$
--   Define $g_{y_J,z_K}(x)$ by the complex double integral (21), with $y$ integrated from $0$ to $y_J$ and $z$ from $-z_K$ to $z_K$. Define $h_{J,K,\Delta_y,\Delta_z}(x)$ by the complex double sum (18), with $j=0,\ldots,J-1$, $k=-K,\ldots,K$, $y_j=j\Delta_y$, and $z_k=k\Delta_z$. Both carry the factor $i/\sqrt{2\pi}$ and the phase $e^{-ixyz}$.
--
--   These definitions supply the exact scalar approximants used in Lemmas 11 and 12. The comparison target is the real reciprocal $1/x$, embedded into $\mathbb C$.
-- source:
--   Childs, Kothari and Somma, Quantum algorithm for systems of linear equations with exponentially improved dependence on precision, arXiv:1511.02306v2, pp. 10–11, D_κ and displays (18), (21)

import Mathlib
import Definitions.Def_QuantumLinSys_Chebyshev_Setting

namespace QuantumLinSys.Fourier

/-- The truncated Gaussian Fourier double integral `g` of (21), p. 11. -/
noncomputable def gTrunc (yJ zK x : ℝ) : ℂ :=
  (Complex.I / (Real.sqrt (2 * Real.pi) : ℂ)) *
    ∫ y in (0 : ℝ)..yJ, ∫ z in (-zK)..zK,
      (z : ℂ) * (Real.exp (-z ^ 2 / 2) : ℂ) *
        Complex.exp (-Complex.I * x * y * z)

/-- The double sum `h` of (18), p. 10: `y_j = j Δ_y`, `z_k = k Δ_z`,
`0 ≤ j < J`, and `-K ≤ k ≤ K`. -/
noncomputable def hDisc (J K : ℕ) (Δy Δz x : ℝ) : ℂ :=
  (Complex.I / (Real.sqrt (2 * Real.pi) : ℂ)) *
    ∑ j ∈ Finset.range J, (Δy : ℂ) *
      ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        (Δz : ℂ) * (((k : ℝ) * Δz : ℝ) : ℂ) *
          (Real.exp (-((k : ℝ) * Δz) ^ 2 / 2) : ℂ) *
          Complex.exp (-Complex.I * x * ((j : ℝ) * Δy) * ((k : ℝ) * Δz))

end QuantumLinSys.Fourier


