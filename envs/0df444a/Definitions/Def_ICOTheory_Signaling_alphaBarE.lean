-- Prove2me | Definitions.Def_ICOTheory_Signaling_alphaBarE
-- name    : ICOTheory_Signaling_alphaBarE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:04:06.256553+00:00
-- url     : https://prove2.me/theorems/8350bc9e-a7c3-4b1e-ab77-696fa807380c
-- title:
--   Minimal equity share $\bar\alpha^E_j=I/(\mathbb E R_j-C)$, display (21)
-- statement:
--   Let $I$ be the initial investment, $C$ the fixed production cost ($C(q)=C$), and $j\in\{H,L\}$ investors' belief about the venture's quality. Equity is a claim to profit $R-C$, so selling a fraction $\alpha$ of equity raises $\alpha(\mathbb E R_j-C)$, and the smallest fraction that finances the investment is
--
--   $$
--   \bar\alpha^E_j=\frac{I}{\mathbb E R_j-C}=\frac{I}{\mu_j/4-C}.
--   $$
--
--   This is display (21); the equity financing constraint reads $\bar\alpha^E_j\le\alpha\le1$.
--
--   **Formalization Note** $\mathbb E R_j=\mu_j/4$ (p. 18). When $\mu_j/4=C$ Lean's division returns $0$; the statements that use the share assume $C<\mu_j/4$.
-- source:
--   Chod, Lyandres, A Theory of ICOs: Diversification, Agency, and Information Asymmetry, SSRN 3159528 (December 14, 2019), §4, display (21), p. 19; C(q) = C, p. 18

import Mathlib

namespace ICOTheory.Signaling

/-- **The minimal share of equity `ᾱ^E_j` that finances the investment, display (21).**
Chod, Lyandres, *A Theory of ICOs: Diversification, Agency, and Information Asymmetry*,
SSRN 3159528 (December 14, 2019), §4, display (21), p. 19: `ᾱ^E_j = I / (𝔼R_j − C)`, where `I`
is the initial investment, `C` the fixed production cost (`C(q) = C`, p. 18) and `j ∈ {H, L}`
investors' belief about the venture's quality.

`alphaBarE I C μ` is `ᾱ^E_j` for a venture of believed type `j` with `μ = μ_j`.

**Formalization Note.** `𝔼R_j = μ_j / 4` (p. 18: `R_i = ξ_i²/4`, `ξ_i² ~ N(μ_i, σ)`). The value
does not depend on `μ_L` (for `j = H`) or on `σ` (proof of Proposition 6, p. 32). For
`μ / 4 = C` Lean's division gives `0`; the statements using it assume `C < μ / 4` (directly or
through `C + I < μ_H/4` with `0 < I`). -/
noncomputable def alphaBarE (I C μ : ℝ) : ℝ :=
  I / (μ / 4 - C)

end ICOTheory.Signaling


