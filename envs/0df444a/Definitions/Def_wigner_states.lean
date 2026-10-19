-- Prove2me | Definitions.Def_wigner_states
-- name    : wigner_states
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-18T16:49:10.012769+00:00
-- url     : https://prove2.me/theorems/14fc97d6-c4a8-4050-9bf3-b61bb7c3b5ed
-- title:
--   Hermite polynomials, Laguerre polynomials, and Fock states
-- statement:
--   Physicists' Hermite polynomials, ordinary Laguerre polynomials, and the normalized Fock states of the harmonic oscillator. The Hermite polynomials $H_m$ are defined by the recurrence $H_0 = 1$, $H_1(x) = 2x$, $H_{n+1}(x) = 2x\,H_n(x) - 2n\,H_{n-1}(x)$; the Laguerre polynomials $L_m$ by $L_0 = 1$, $L_1(x) = 1-x$, $(m+1)L_{m+1}(x) = (2m+1-x)L_m(x) - mL_{m-1}(x)$. The $m$-th normalized Hermite (Fock) wavefunction is
--
--   $$u_m(x) = (2^m m!)^{-1/2}\,\pi^{-1/4}\,H_m(x)\,e^{-x^2/2},$$
--
--   the $m$-th number state $|m\rangle = (a^\dagger)^m/\sqrt{m!}\,|0\rangle$ of the quantum harmonic oscillator, in dimensionless units ($\hbar = m = \omega = 1$).
--
--   **Formalization Note** The factor $(2^m m!)^{-1/2}$ makes the states $u_m$ orthonormal in $L^2(\mathbb{R})$; it is required for Groenewold's closed formula for the Wigner function of a Fock state. The source's displayed eigenfunctions $u_m(x) = \pi^{-1/4}H_m(x)e^{-x^2/2}$ omit this normalization, but its Fock-state formula is stated for the normalized number states.
-- source:
--   Wikipedia, "Wigner quasiprobability distribution" (oldid 1376057304), sections "Examples" (Groenewold formula and Hermite functions) and "Positivity of the function". https://en.wikipedia.org/wiki/Wigner_quasiprobability_distribution

import Mathlib

namespace Wigner

/-- The m-th physicists' Hermite polynomial H_m, defined by the three-term
recurrence H_0 = 1, H_1 (x) = 2 * x,
H_{n+1} (x) = 2 * x * H_n (x) - 2 * n * H_{n-1} (x). -/
def hermiteP : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, x => 2 * x
  | n + 2, x => 2 * x * hermiteP (n + 1) x - 2 * (n + 1) * hermiteP n x

/-- The m-th ordinary Laguerre polynomial L_m, defined by the three-term
recurrence L_0 = 1, L_1 (x) = 1 - x,
(m + 1) * L_{m+1} (x) = (2 * m + 1 - x) * L_m (x) - m * L_{m-1} (x). -/
noncomputable def laguerreL : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, x => 1 - x
  | m + 2, x => ((2 * (m + 1) + 1 - x) * laguerreL (m + 1) x - (m + 1) * laguerreL m x) / (m + 2)

/-- The m-th normalized Hermite (Fock) wavefunction of the harmonic oscillator,
u_m (x) = (2^m * m!)^(-1/2) * pi^(-1/4) * H_m (x) * exp (-x^2 / 2). -/
noncomputable def fockState (m : ℕ) (x : ℝ) : ℂ :=
  (((Real.pi ^ (-(1 / 4 : ℝ)) * hermiteP m x * Real.exp (-(x ^ 2) / 2) /
      Real.sqrt ((2 : ℝ) ^ m * ((Nat.factorial m : ℕ) : ℝ))) : ℝ) : ℂ)

end Wigner


