-- Prove2me | Definitions.Def_FractionalSpectralGP_wick
-- name    : FractionalSpectralGP_wick
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:23:21.830443+00:00
-- url     : https://prove2.me/theorems/8d5b3fc7-726d-43c3-b9d1-7ad0aea2eab9
-- title:
--   The Wick product $F\diamond G=\sum_\gamma(\sum_{\alpha+\beta=\gamma}f_\alpha g_\beta)H_\gamma$ (4.4)
-- statement:
--   For formal series $F=\sum_\alpha f_\alpha H_\alpha$ and $G=\sum_\beta g_\beta H_\beta$,
--
--   $$
--   F\diamond G=\sum_{\gamma\in\ell}\Big(\sum_{\alpha+\beta=\gamma}f_\alpha g_\beta\Big)H_\gamma ,
--   $$
--
--   the bilinear extension of $H_\alpha\diamond H_\beta=H_{\alpha+\beta}$. For each $\gamma$ the inner sum is finite, so the product is defined for all formal series; Våge's inequality controls it on the spaces $\mathcal H'_k$.
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, (4.4), p.11

import Mathlib

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- The Wick product `F ♦ G = Σ_γ (Σ_{α+β=γ} f_α g_β) H_γ` (Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, (4.4), p.11), on
coefficient families: `H_α ♦ H_β = H_{α+β}` extended bilinearly.

**Formalization Note.** For each `γ` the inner sum is the finite sum over the antidiagonal
`{(α, β) : α + β = γ}` of `ℓ = ℕ →₀ ℕ`, so the product is defined for all formal series. -/
noncomputable def wick (f g : (ℕ →₀ ℕ) → ℂ) (γ : ℕ →₀ ℕ) : ℂ :=
  ∑ p ∈ Finset.HasAntidiagonal.antidiagonal γ, f p.1 * g p.2

end FractionalSpectralGP


