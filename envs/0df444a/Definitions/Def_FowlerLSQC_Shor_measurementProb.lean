-- Prove2me | Definitions.Def_FowlerLSQC_Shor_measurementProb
-- name    : FowlerLSQC_Shor_measurementProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:35:29.776078+00:00
-- url     : https://prove2.me/theorems/93c4e358-847c-402d-8bed-a95cdd340b16
-- title:
--   Outcome probability $\Pr(j,r,L)$ of quantum period finding, (7.7)
-- statement:
--   Let $L\ge0$, $r\ge1$ and $j$ be natural numbers. The probability of measuring the value $j$ of the $2L$-qubit $k$-register at the end of quantum period finding is
--   $$
--   \Pr(j,r,L)=\left|\frac{\sqrt r}{2^{2L}}\sum_{p=0}^{2^{2L}/r-1}\exp\!\Big(\frac{2\pi i}{2^{2L}}\,j p r\Big)\right|^2 .
--   $$
--   It is obtained by measuring the $f$-register, which leaves the $k$-register in a uniform superposition of the $2^{2L}/r$ values $k_0+pr$, and then applying the quantum Fourier transform on $2^{2L}$ states; the offset $k_0$ only contributes a phase.
--
--   This is the distribution whose peaks at $j\approx c\,2^{2L}/r$ the classical postprocessing exploits.
--
--   **Formalization Note** The upper summation limit $2^{2L}/r-1$ is an integer when $r$ divides $2^{2L}$, the case in which the book evaluates (7.7); in general the sum runs over $p=0,\dots,\lfloor 2^{2L}/r\rfloor-1$ (natural-number division).
-- source:
--   Fowler, Towards Large-Scale Quantum Computation, arXiv:quant-ph/0506126v1, Ch. 7, Eq. (7.7), p.79 (PDF p.97)

import Mathlib

open Complex

namespace FowlerLSQC.Shor

/-- The probability (7.7) of measuring the value `j` of the `2L`-qubit `k`-register at the end of
quantum period finding, Fowler, *Towards Large-Scale Quantum Computation*,
arXiv:quant-ph/0506126v1, Ch. 7, (7.7), p.79 (PDF 97):
`Pr(j, r, L) = |(√r / 2^{2L}) Σ_{p=0}^{2^{2L}/r − 1} exp(2πi j p r / 2^{2L})|²`.

**Formalization Note** The upper limit `2^{2L}/r − 1` is an integer when `r ∣ 2^{2L}`, the case in
which the book evaluates (7.7) (p.79); the sum is over `p ∈ Finset.range (2^(2L) / r)` with `ℕ`
division, i.e. `p = 0, …, ⌊2^{2L}/r⌋ − 1` in general (this agrees with the book's state (7.3),
whose count is the same expression). The product `j p r` is formed in `ℕ` and cast to `ℂ`, and
`|·|` is the complex norm. -/
noncomputable def measurementProb (j r L : ℕ) : ℝ :=
  ‖((Real.sqrt r : ℂ) / (2 : ℂ) ^ (2 * L)) *
      ∑ p ∈ Finset.range (2 ^ (2 * L) / r),
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((j * p * r : ℕ) : ℂ) / (2 : ℂ) ^ (2 * L))‖ ^ 2

end FowlerLSQC.Shor


