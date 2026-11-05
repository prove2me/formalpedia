-- Prove2me | Definitions.Def_BauerleRiederMDP_Indifference_Market_v
-- name    : BauerleRiederMDP_Indifference_Market_v
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:27:51.105603+00:00
-- url     : https://prove2.me/theorems/ab75e7b3-0c2f-4f4e-8810-e00d12c0ed6a
-- title:
--   The constant $v$ of (4.39)
-- statement:
--   The constant
--   $$
--   v:=\inf_{a\in\mathbb R}\mathbb E\bigl[e^{-\gamma a(\tilde R_1-1)}\bigr]
--   $$
--   is the value of the one-period problem without a claim. It governs the claim-free value function, $V^0_n(x,s,\hat s)=-e^{-\gamma x}v^{N-n}$.
--
--   **Formalization Note** The expectation is over the four-point space, so the integrand is integrable; the family is nonempty and bounded below by $0$, so the real infimum is the book's infimum.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), eq. (4.39), p.138

import Mathlib
import Definitions.Def_BauerleRiederMDP_Indifference_Market

open MeasureTheory

namespace BauerleRiederMDP.Indifference

namespace Market

/-- The constant `v := inf_{a ∈ ℝ} 𝔼[e^{-γ a (R̃₁ - 1)}]` (Bäuerle & Rieder, Markov Decision
Processes with Applications to Finance (2011), eq. (4.39), p.138, PDF 152).

**Formalization Note.** The expectation is over the four-point space `Ω`, so the integrand is
integrable, and the family is nonempty and bounded below by `0`, so the real infimum is the
book's. -/
noncomputable def v (M : Market) : ℝ :=
  ⨅ a : ℝ, ∫ ω, Real.exp (-M.γ * a * (M.Rt ω - 1)) ∂M.P

end Market

end BauerleRiederMDP.Indifference


