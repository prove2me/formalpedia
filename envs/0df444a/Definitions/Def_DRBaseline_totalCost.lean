-- Prove2me | Definitions.Def_DRBaseline_totalCost
-- name    : DRBaseline_totalCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:40:28.211824+00:00
-- url     : https://prove2.me/theorems/4a45c4d8-c57a-450a-a005-a87a13c5d6bb
-- title:
--   Firm's total expected cost $C_u(b,r)$
-- statement:
--   Peak demand is uniform on $[0,2\Omega]$ in an event (probability $\rho$) and on $[0,2\Lambda]$ otherwise; off-peak demand $\varphi$ is uniform on $[0,2\Phi]$, independent of peak demand. The firm's **total expected cost** is
--
--   $$C_u(b,r)=\rho\int_0^{2\Omega}\!\!\int_0^{2\Phi}\Bigl(c^h_p(\omega-s^*)+rS(s^*)+c^l_p(\varphi+s^*)\Bigr)h(\varphi)\,d\varphi\,f(\omega)\,d\omega+(1-\rho)\int_0^{2\Lambda}\!\!\int_0^{2\Phi}\bigl(c^l_p\lambda+c^l_p\varphi\bigr)h(\varphi)\,d\varphi\,g(\lambda)\,d\lambda,$$
--
--   with $s^*=s^*(b,r\mid\omega)$ and uniform densities $f,g,h$.
--
--   **Formalization Note** Iterated interval integrals with the densities written out.
-- source:
--   Agrawal, Yücel, Design of Electricity Demand-Response Programs, manuscript of May 26, 2021, §3.4, pp.9–10; Online Appendix, pp.OA1–OA2

import Mathlib
import Definitions.Def_DRBaseline_estReduction

namespace DRBaseline

/-- **Firm's total expected cost `C_u(b, r) = C_n + C_e(b, r)`.**
Agrawal, Yücel, *Design of Electricity Demand-Response Programs*, manuscript of May 26, 2021, §3.4, pp.9–10, written out in the Online Appendix, Proof of Lemma 3 and 4, and
Propositions 2, 3, and 4, pp.OA1–OA2:
`C_u(b,r) = ρ ∫_0^{2Ω} ∫_0^{2Φ} (C^h_p(ω − s∗) + rS(s∗) + C^l_p(φ + s∗)) h(φ)dφ f(ω)dω
 + (1 − ρ) ∫_0^{2Λ} ∫_0^{2Φ} (C^l_p(λ) + C^l_p(φ)) h(φ)dφ g(λ)dλ`,
with `C^h_p(q) = c^h_p q`, `C^l_p(q) = c^l_p q` and uniform densities `f = 1/(2Ω)` on `[0,2Ω]`,
`g = 1/(2Λ)` on `[0,2Λ]`, `h = 1/(2Φ)` on `[0,2Φ]` (p.7).

**Formalization Note** Iterated interval integrals with the densities written out; the event
peak demand `ω` and the off-peak demand `φ` are independent, as the page's iterated integral
says. -/
noncomputable def totalCost (ρ Ω Λ Φ chp clp : ℝ) (s : ℝ → ℝ → ℝ → ℝ) (b r : ℝ) : ℝ :=
  ρ * (∫ ω in (0 : ℝ)..2 * Ω,
        (∫ φ in (0 : ℝ)..2 * Φ,
          (chp * (ω - s b r ω) + r * estReduction b ω (s b r ω) + clp * (φ + s b r ω)) /
            (2 * Φ)) / (2 * Ω)) +
    (1 - ρ) * (∫ l in (0 : ℝ)..2 * Λ,
        (∫ φ in (0 : ℝ)..2 * Φ, (clp * l + clp * φ) / (2 * Φ)) / (2 * Λ))

end DRBaseline


