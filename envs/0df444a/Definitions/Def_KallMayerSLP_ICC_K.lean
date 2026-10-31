-- Prove2me | Definitions.Def_KallMayerSLP_ICC_K
-- name    : KallMayerSLP_ICC_K
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:10:52.323993+00:00
-- url     : https://prove2.me/theorems/b0e59cd4-d131-4b91-9771-adba9b4bef72
-- title:
--   Separate integrated probability function $K(x)$
-- statement:
--   With $z^+=\max\{0,z\}$, the **separate integrated probability function** for positive parts is
--   $$
--   K(x)=\mathbb E_\xi\big[\zeta^+(x,\xi)\big]=\mathbb E_\xi\big[[t(\xi)^{\mathrm T}x-h(\xi)]^+\big].
--   $$
--   The constraint $K(x)\le\gamma$ bounds the expected loss, and replaces the probability of a loss by its expected size.
--
--   **Formalization Note** `P` is the law of $\xi$ on `Ξ`, and $\mathbb E_\xi$ is the Bochner integral, which is $0$ when the integrand is not integrable. Every theorem using `K` assumes integrability of $t,h$ (the standing assumption of §4.1, p.149), or works with a finite discrete law, where it is automatic.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §4.1.1, p.150 (PDF 160)

import Mathlib
import Definitions.Def_KallMayerSLP_ICC_zeta

open MeasureTheory

namespace KallMayerSLP.ICC

/-- **The separate integrated probability function `K(x) = 𝔼_ξ[ζ⁺(x, ξ)]`.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §4.1.1, p.150 (PDF 160):
`K(x) := ρ⁺_sic(ζ(x, ξ)) = 𝔼_ξ[ζ⁺(x, ξ)]`, with `z⁺ = max{0, z}` (p.149).

**Formalization Note.** `P` is the law of `ξ` on `Ξ`, and `𝔼_ξ` is the Bochner integral against
`P`. The integral is `0` when the integrand is not integrable; every theorem about `K` either
assumes that `t` and `h` are integrable (the book's "the expected values of `T(ξ)` and `h(ξ)`
exist", p.149) or uses a finite discrete law, where everything is integrable. -/
noncomputable def K {Ξ : Type*} [MeasurableSpace Ξ] {n : ℕ} (P : Measure Ξ)
    (t : Ξ → Fin n → ℝ) (h : Ξ → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∫ ξ, max 0 (zeta t h x ξ) ∂P

end KallMayerSLP.ICC


