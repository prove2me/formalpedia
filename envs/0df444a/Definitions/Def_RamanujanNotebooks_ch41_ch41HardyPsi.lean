-- Prove2me | Definitions.Def_RamanujanNotebooks_ch41_ch41HardyPsi
-- name    : RamanujanNotebooks_ch41_ch41HardyPsi
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T15:53:36.603474+00:00
-- url     : https://prove2.me/theorems/e4c7f30b-e1dd-4964-92e7-3f5d9605e43b
-- title:
--   Ramanujan's Notebooks, Part I, Ch. 41: ch41HardyPsi
-- statement:
--   Hardy's function `Ψ(x) = (1/(2πi)) ∫_{c-i∞}^{c+i∞} (π / sin(πs)) ψ(-s) x^{-s} ds` of §1.3,
--   p. 299, for a real `x`, the line of integration `s = c + i t`, `t ∈ ℝ`, being parametrised by
--   `t` (so `ds = i dt` and the factor `1/(2πi)` becomes `1/(2π)`); `x^{-s}` is the principal power.
--   Domain: `x > 0`, `0 < c < δ < 1`, and `ψ` analytic on `Re s ≥ -δ` with
--   `|ψ(σ + i t)| ≤ C exp(Pσ + A|t|)`, `A < π`; then the integrand decays exponentially in `|t|`,
--   the integral converges absolutely and its value does not depend on `c`.
--   Outside: if the integrand is not integrable Lean returns `0`; for `x ≤ 0` the principal power
--   has no meaning here; if `c` is an integer the factor `π / sin(πs)` has a pole on the line.
--   Reference: for `ψ(s) = 1/Γ(s + 1)`, `Ψ(x) = e^{-x}` (`Ψ(0.3) = 0.74081822068171787429…`);
--   for `ψ(s) = 1`, `Ψ(x) = 1/(1 + x)`.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part I (Springer, 1985), Chapter 41.

import Mathlib

namespace RamanujanNotebooks

/-- Hardy's function `Ψ(x) = (1/(2πi)) ∫_{c-i∞}^{c+i∞} (π / sin(πs)) ψ(-s) x^{-s} ds` of §1.3,
p. 299, for a real `x`, the line of integration `s = c + i t`, `t ∈ ℝ`, being parametrised by
`t` (so `ds = i dt` and the factor `1/(2πi)` becomes `1/(2π)`); `x^{-s}` is the principal power.
Domain: `x > 0`, `0 < c < δ < 1`, and `ψ` analytic on `Re s ≥ -δ` with
`|ψ(σ + i t)| ≤ C exp(Pσ + A|t|)`, `A < π`; then the integrand decays exponentially in `|t|`,
the integral converges absolutely and its value does not depend on `c`.
Outside: if the integrand is not integrable Lean returns `0`; for `x ≤ 0` the principal power
has no meaning here; if `c` is an integer the factor `π / sin(πs)` has a pole on the line.
Reference: for `ψ(s) = 1/Γ(s + 1)`, `Ψ(x) = e^{-x}` (`Ψ(0.3) = 0.74081822068171787429…`);
for `ψ(s) = 1`, `Ψ(x) = 1/(1 + x)`. -/
noncomputable def ch41HardyPsi (ψ : ℂ → ℂ) (c x : ℝ) : ℂ :=
  ∫ t : ℝ, ((1 / (2 * (Real.pi : ℂ))) *
    ((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * ((c : ℂ) + (t : ℂ) * Complex.I))) *
    ψ (-((c : ℂ) + (t : ℂ) * Complex.I)) * (x : ℂ) ^ (-((c : ℂ) + (t : ℂ) * Complex.I)))

end RamanujanNotebooks


