-- Prove2me | Definitions.Def_KallMayerSLP_ICC_H
-- name    : KallMayerSLP_ICC_H
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:10:55.389986+00:00
-- url     : https://prove2.me/theorems/f313aaff-3dc0-4ea0-a707-40e5c6f2bb57
-- title:
--   Separate integrated probability function $H(x)$
-- statement:
--   With $z^-=\max\{0,-z\}$, the **separate integrated probability function** for negative parts is
--   $$
--   H(x)=\mathbb E_\xi\big[\zeta^-(x,\xi)\big]=\mathbb E_\xi\big[[t(\xi)^{\mathrm T}x-h(\xi)]^-\big].
--   $$
--   It is the expected loss when losses are modelled by negative values of $\zeta$, as in the constraint (4.4).
--
--   **Formalization Note** $\mathbb E_\xi$ is the Bochner integral against the law `P`, which is $0$ when the integrand is not integrable; every theorem using `H` assumes integrability of $t,h$ (p.149).
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §4.1.1, p.150 (PDF 160)

import Mathlib
import Definitions.Def_KallMayerSLP_ICC_zeta

open MeasureTheory

namespace KallMayerSLP.ICC

/-- **The separate integrated probability function `H(x) = 𝔼_ξ[ζ⁻(x, ξ)]`.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §4.1.1, p.150 (PDF 160):
`H(x) := ρ⁻_sic(ζ(x, ξ)) = 𝔼_ξ[ζ⁻(x, ξ)]`, with `z⁻ = max{0, −z}` (p.149).

**Formalization Note.** `P` is the law of `ξ` on `Ξ`, and `𝔼_ξ` is the Bochner integral against
`P`. The integral is `0` when the integrand is not integrable; every theorem about `H` assumes that
`t` and `h` are integrable (p.149). -/
noncomputable def H {Ξ : Type*} [MeasurableSpace Ξ] {n : ℕ} (P : Measure Ξ)
    (t : Ξ → Fin n → ℝ) (h : Ξ → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∫ ξ, max 0 (-(zeta t h x ξ)) ∂P

end KallMayerSLP.ICC


