-- Prove2me | Definitions.Def_ICOTheory_Signaling_alphaBarT
-- name    : ICOTheory_Signaling_alphaBarT
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:03:52.13606+00:00
-- url     : https://prove2.me/theorems/9f938f08-9e9f-437a-a609-9197595e0131
-- title:
--   Minimal token share $\bar\alpha^T_j=I/\mathbb E R_j$, display (21)
-- statement:
--   Let $I$ be the initial investment the venture requires and let $j\in\{H,L\}$ be investors' belief about the venture's quality. Under token financing the entrepreneur raises $\alpha\,\mathbb E R_j$ by selling a fraction $\alpha$ of the tokens, so the smallest fraction that finances the investment is
--
--   $$
--   \bar\alpha^T_j=\frac{I}{\mathbb E R_j}=\frac{I}{\mu_j/4}.
--   $$
--
--   This is display (21); the token financing constraint reads $\bar\alpha^T_j\le\alpha\le1$.
--
--   **Formalization Note** The expected revenue is written $\mathbb E R_j=\mu_j/4$, since $R_j=\xi_j^2/4$ and $\mathbb E\xi_j^2=\mu_j$ (p. 18). The share depends on neither $\mu_L$ (for $j=H$) nor $\sigma$, which is the paper's $d\bar\alpha^i_H/d\mu_L=d\bar\alpha^i_H/d\sigma=0$.
-- source:
--   Chod, Lyandres, A Theory of ICOs: Diversification, Agency, and Information Asymmetry, SSRN 3159528 (December 14, 2019), §4, display (21), p. 19; R_i = ξ_i²/4 and ξ_i² ≈ N(µ_i, σ), p. 18

import Mathlib

namespace ICOTheory.Signaling

/-- **The minimal share of tokens `ᾱ^T_j` that finances the investment, display (21).**
Chod, Lyandres, *A Theory of ICOs: Diversification, Agency, and Information Asymmetry*,
SSRN 3159528 (December 14, 2019), §4, display (21), p. 19: `ᾱ^T_j = I / 𝔼R_j`, where `I` is the
initial investment and `j ∈ {H, L}` is investors' belief about the venture's quality.

`alphaBarT I μ` is `ᾱ^T_j` for a venture of believed type `j` with `μ = μ_j`.

**Formalization Note.** The expected revenue is written `𝔼R_j = μ_j / 4`: by p. 18,
`R_i = ξ_i²/4` and `ξ_i² ~ N(μ_i, σ)`, so `𝔼R_j = μ_j/4`. The result does not depend on `μ_L`
(for `j = H`) or on `σ`, which is the proof of Proposition 6's `dᾱ^i_H/dμ_L = dᾱ^i_H/dσ = 0`
(p. 32). For `μ = 0` Lean's division gives `0`; the statements using it keep `μ` positive. -/
noncomputable def alphaBarT (I μ : ℝ) : ℝ :=
  I / (μ / 4)

end ICOTheory.Signaling


