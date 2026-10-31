-- Prove2me | Definitions.Def_DRBaseline_totalEmissions
-- name    : DRBaseline_totalEmissions
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:39:53.2633+00:00
-- url     : https://prove2.me/theorems/76577f4d-dd16-45ec-8ad1-b496b2077698
-- title:
--   Total expected emissions $E_u(b,r)$
-- statement:
--   With emission intensities $e^h_g$ (event peak) and $e^l_g$ (non-event peak and off-peak), the **total expected emissions** under baseline $b$ and rebate $r$ are
--
--   $$E_u=\rho\int_0^{2\Omega}\!\!\int_0^{2\Phi}\Bigl(e^h_g(\omega-s^*)+e^l_g(\varphi+s^*)\Bigr)h(\varphi)\,d\varphi\,f(\omega)\,d\omega+(1-\rho)\int_0^{2\Lambda}\!\!\int_0^{2\Phi}\bigl(e^l_g\lambda+e^l_g\varphi\bigr)h(\varphi)\,d\varphi\,g(\lambda)\,d\lambda .$$
--
--   This is the total; the paper's $E(b,r)=\rho\mathbb E[(e^h_g-e^l_g)s^*]$ is the *reduction* in emissions.
--
--   **Formalization Note** Iterated interval integrals with the uniform densities written out.
-- source:
--   Agrawal, Yücel, Design of Electricity Demand-Response Programs, manuscript of May 26, 2021, §3.5, pp.10–11; Online Appendix, p.OA3

import Mathlib

namespace DRBaseline

/-- **Total expected emissions `E_u = E_n + E_e`.**
Agrawal, Yücel, *Design of Electricity Demand-Response Programs*, manuscript of May 26, 2021, §3.5, pp.10–11, written out in the Online Appendix, Proof of Lemma 3 and 4, and
Propositions 2, 3, and 4, p.OA3:
`E_u .= ρ ∫_0^{2Ω} ∫_0^{2Φ} (E^h_g(ω − s∗(b,r|ω)) + E^l_g(φ + s∗(b,r|ω))) h(φ)dφ f(ω)dω
 + (1 − ρ) ∫_0^{2Λ} ∫_0^{2Φ} (E^l_g(λ) + E^l_g(φ)) h(φ)dφ g(λ)dλ`,
with `E^h_g(q) = e^h_g q`, `E^l_g(q) = e^l_g q` and the uniform densities of p.7.

**Formalization Note** Iterated interval integrals with the densities written out. This is the
total, not the reduction `E(b, r) = ρE[Δe s∗]` of p.11. -/
noncomputable def totalEmissions (ρ Ω Λ Φ ehg elg : ℝ) (s : ℝ → ℝ → ℝ → ℝ) (b r : ℝ) : ℝ :=
  ρ * (∫ ω in (0 : ℝ)..2 * Ω,
        (∫ φ in (0 : ℝ)..2 * Φ, (ehg * (ω - s b r ω) + elg * (φ + s b r ω)) / (2 * Φ)) /
          (2 * Ω)) +
    (1 - ρ) * (∫ l in (0 : ℝ)..2 * Λ,
        (∫ φ in (0 : ℝ)..2 * Φ, (elg * l + elg * φ) / (2 * Φ)) / (2 * Λ))

end DRBaseline


