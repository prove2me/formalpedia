-- Prove2me | Definitions.Def_TongString_dedekind_eta
-- name    : TongString_dedekind_eta
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-25T20:17:22.070833+00:00
-- url     : https://prove2.me/theorems/1c4a65e9-168d-4c0e-8b02-e06488774b8f
-- title:
--   The Dedekind eta function $\eta(\tau)=q^{1/24}\prod_{n\ge1}(1-q^n)$, $q=e^{2\pi i\tau}$
-- statement:
--   For $\tau$ in the upper half-plane put $q=e^{2\pi i\tau}$. The **Dedekind eta function** is
--
--   $$
--   \eta(\tau)=q^{1/24}\prod_{n=1}^{\infty}(1-q^{n})=e^{2\pi i\tau/24}\prod_{n=1}^{\infty}\bigl(1-e^{2\pi i n\tau}\bigr),
--   $$
--
--   where $q^{1/24}$ means $e^{2\pi i\tau/24}$. Its inverse is the oscillator contribution to the partition function of a free scalar field on a torus of modular parameter $\tau$ (eq. (6.20)).
--
--   **Formalization Note** The infinite product is Mathlib's unconditional product `tprod`; for $\operatorname{Im}\tau>0$ it converges, while for other $\tau$ the definition returns an unspecified junk value, so all theorems about $\eta$ assume $\operatorname{Im}\tau>0$.
-- source:
--   D. Tong, *String Theory*, University of Cambridge Part III Mathematical Tripos lecture notes (January 2009), http://www.damtp.cam.ac.uk/user/tong/string.html, Section 6.4.2, p. 151 (definition of the Dedekind eta function, with q = e^{2πiτ} from p. 149)

import Mathlib

namespace TongString

open Complex

/-- Tong's Dedekind eta function `η(τ) = q^(1/24) ∏_{n ≥ 1} (1 - q^n)` with `q = exp(2πiτ)`
and `q^(1/24) = exp(2πiτ/24)`. The product index `n : ℕ` stands for `n + 1 ≥ 1`. -/
noncomputable def dedekindEta (τ : ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * I * τ / 24) *
    ∏' n : ℕ, (1 - Complex.exp (2 * Real.pi * I * ((n : ℂ) + 1) * τ))

end TongString


