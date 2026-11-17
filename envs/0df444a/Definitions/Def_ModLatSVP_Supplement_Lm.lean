-- Prove2me | Definitions.Def_ModLatSVP_Supplement_Lm
-- name    : ModLatSVP_Supplement_Lm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:18:03.760198+00:00
-- url     : https://prove2.me/theorems/831562ce-7a22-40ee-84c2-06f8c3486e7d
-- title:
--   The quantities $\mathcal L_m(\rho)$ and $\Psi_m(\rho)$ of (31)
-- statement:
--   For integers $m\ge1$ and reals $\rho\ge1$ let
--
--   $$\mathcal L_m(\rho)=\max\Big\{\log(2\rho),\ \frac{m\log(m\rho)}{2(m-1)}\Big\},$$
--
--   where the second term is omitted for $m=1$, and
--
--   $$\Psi_m(\rho)=m\,\mathcal L_m(\rho)\exp\Big(\frac{\log\rho}{2\mathcal L_m(\rho)}-1\Big).$$
--
--   Here $\log$ is the natural logarithm. Since $\mathcal L_m(\rho)\ge\log2>0$, $\Psi_m(\rho)$ is well defined. These quantities express the refined oracle-call bound of Theorem 6.2, $(N+6)^{n+2}2^{O(N)}\rho^{d/2}\exp(d\Psi_{n-1}(\rho))$.
--
--   **Formalization Note** The definition is the closed form (31), not the equivalent maximization stated after it. Values at $m=0$ are not used.
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), §6.2, (31), p.38 (PDF p.38)

import Mathlib

namespace ModLatSVP

namespace Supplement

/-- The quantity `𝓛_m(ρ)` of (31). Kim, Lee, Son, *Exact SVP and CVP in Structured Lattices:
Polynomial-Space Algorithms and Reductions*, STOC 2027 submission (manuscript sha256 e7151fad…), §6.2,
p.38 (PDF p.38): "For m ≥ 1 and ρ ≥ 1, define 𝓛_m(ρ) = max{log(2ρ), m log(mρ)/(2(m − 1))}, where the
second term is omitted for m = 1".

**Formalization Note.** `log` is the natural logarithm. The definition is used for `m ≥ 1` and `ρ ≥ 1`
only; the value at `m = 0` is irrelevant. -/
noncomputable def Lm (m : ℕ) (ρ : ℝ) : ℝ :=
  if m = 1 then Real.log (2 * ρ)
  else max (Real.log (2 * ρ)) ((m : ℝ) * Real.log (m * ρ) / (2 * ((m : ℝ) - 1)))

/-- The quantity `Ψ_m(ρ) = m 𝓛_m(ρ) exp(log ρ / (2𝓛_m(ρ)) − 1)` of (31), p.38. For `ρ ≥ 1`,
`𝓛_m(ρ) ≥ log 2 > 0`, so the quotient is well defined. -/
noncomputable def Psi (m : ℕ) (ρ : ℝ) : ℝ :=
  (m : ℝ) * Lm m ρ * Real.exp (Real.log ρ / (2 * Lm m ρ) - 1)

end Supplement

end ModLatSVP


