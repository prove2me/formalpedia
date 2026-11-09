-- Prove2me | Definitions.Def_RGGThreshold_kappaTri
-- name    : RGGThreshold_kappaTri
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:58:08.971204+00:00
-- url     : https://prove2.me/theorems/1ab316a9-946b-4ad9-883c-10d9a928d650
-- title:
--   The coefficients $\kappa_\triangle,\kappa_\square,\kappa_\diamond$ and the error term $R_{n,d,p}$
-- statement:
--   With $a=\phi(z_p)$, define
--
--   $$
--   \kappa_\triangle=\frac{a^3}{p^3(1-p)^3},\qquad
--   \kappa_\square=\frac{a^4}{p^4(1-p)^4}-\frac{2a^6}{p^5(1-p)^5},\qquad
--   \kappa_\diamond=\frac{a^5}{p^5(1-p)^5}\Big(z_p-\frac{a(1-2p)}{p(1-p)}\Big),
--   $$
--
--   and the error term
--
--   $$
--   R_{n,d,p}=\frac{n^{3/2}p^{1/2}}{d}+\frac{n^3p^2+n^{5/2}}{d^{3/2}}+\frac{n^4p^2}{d^2}.
--   $$
--
--   They are the coefficients of the signed counts and the error term in the main estimate, Proposition 2.1.
--
--   **Formalization Note** Fractional powers are real powers (`Real.rpow`).
-- source:
--   Hunter–Milojević–Sudakov, Distinguishability Threshold for Random Geometric Graphs, arXiv:2607.22480 (held version, sha256 1a398ef9…), Proposition 2.1, p.5 (PDF p.7)

import Mathlib
import Definitions.Def_RGGThreshold_gaussCDF

namespace RGGThreshold

/-- `κ_△ = a³ / (p³(1-p)³)` with `a = ϕ(z_p)` (Hunter–Milojević–Sudakov, arXiv:2607.22480, held
version, sha256 1a398ef9…, Proposition 2.1, p.5 (PDF p.7)). -/
noncomputable def kappaTri (p : ℝ) : ℝ :=
  aCoef p ^ 3 / (p ^ 3 * (1 - p) ^ 3)

/-- `κ_□ = a⁴ / (p⁴(1-p)⁴) - 2a⁶ / (p⁵(1-p)⁵)` (arXiv:2607.22480, held version, Proposition 2.1,
p.5 (PDF p.7)). -/
noncomputable def kappaC4 (p : ℝ) : ℝ :=
  aCoef p ^ 4 / (p ^ 4 * (1 - p) ^ 4) - 2 * aCoef p ^ 6 / (p ^ 5 * (1 - p) ^ 5)

/-- `κ_◇ = a⁵ / (p⁵(1-p)⁵) · (z_p - a(1-2p) / (p(1-p)))` (arXiv:2607.22480, held version,
Proposition 2.1, p.5 (PDF p.7)). -/
noncomputable def kappaDia (p : ℝ) : ℝ :=
  aCoef p ^ 5 / (p ^ 5 * (1 - p) ^ 5) * (zp p - aCoef p * (1 - 2 * p) / (p * (1 - p)))

/-- The error term `R_{n,d,p} = n^{3/2}p^{1/2}/d + (n³p² + n^{5/2})/d^{3/2} + n⁴p²/d²`
(arXiv:2607.22480, held version, Proposition 2.1, p.5 (PDF p.7)).

**Formalization Note** Fractional powers are `Real.rpow`. -/
noncomputable def Rerr (n d : ℕ) (p : ℝ) : ℝ :=
  (n : ℝ) ^ (3 / 2 : ℝ) * p ^ (1 / 2 : ℝ) / d +
    ((n : ℝ) ^ 3 * p ^ 2 + (n : ℝ) ^ (5 / 2 : ℝ)) / (d : ℝ) ^ (3 / 2 : ℝ) +
    (n : ℝ) ^ 4 * p ^ 2 / (d : ℝ) ^ 2

end RGGThreshold


