-- Prove2me | Definitions.Def_FractionalSpectralGP_dualPair
-- name    : FractionalSpectralGP_dualPair
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:23:53.635177+00:00
-- url     : https://prove2.me/theorems/d85ae3f4-b0f4-457a-ac92-dbe1a4060fb8
-- title:
--   Duality $\langle f,g\rangle=\sum_\alpha\alpha!\,f_\alpha g_\alpha$ between $S_{-1}$ and $S_1$
-- statement:
--   For $f\in S_{-1}$ and $g\in S_1$,
--
--   $$
--   \langle f,g\rangle=\sum_{\alpha\in\ell}\alpha!\,f_\alpha\,g_\alpha .
--   $$
--
--   This extends the inner product $E[FG]=\sum_\alpha\alpha!f_\alpha g_\alpha$ of the white noise space and realizes $S_{-1}$ as the dual of $S_1$.
--
--   **Formalization Note** For $f\in\mathcal H'_q$ and $g\in S_1$ the series converges absolutely, by Cauchy–Schwarz against $|||g|||_q$.
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, §4, p.11

import Mathlib
import Definitions.Def_FractionalSpectralGP_multiFactorial

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- The duality `⟨f, g⟩ = Σ_α α! f_α g_α` between `S_{−1}` and `S₁` (Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, §4, p.11:
`S_{−1}` is the third element of the Gelfand triple `S₁ ⊂ 𝒲 ⊂ S_{−1}`, and this pairing extends
the inner product `E[FG] = Σ α! f_α g_α` of `𝒲` given by (4.3)).

**Formalization Note.** For `f ∈ 𝓗'_q` and `g ∈ S₁` the series converges absolutely (Cauchy–Schwarz
against `|||g|||_q`), so the `tsum` is never a junk value where it is used. -/
noncomputable def dualPair (f g : (ℕ →₀ ℕ) → ℂ) : ℂ :=
  ∑' α, (multiFactorial α : ℂ) * f α * g α

end FractionalSpectralGP


