-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_CIRandom_v0
-- name    : BauerleRiederMDP_LQ_Supplement_CIRandom_v0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:07:01.258806+00:00
-- url     : https://prove2.me/theorems/dc67cd8f-a162-55ab-abf5-93d41bd27413
-- title:
--   The constant $v_0$ of §9.1
-- statement:
--   **The constant $v_0$ of §9.1** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §9.1, p.269, PDF 279): `Ã := {α ∈ ℝ^d | 1 + α · R_1 ≥ 0 ℙ-a.s.}` and $v_0 := \sup _{\alpha  \in  \tilde A } \mathbb E (1 + \alpha  \cdot  R_1)$; the contraction constant of the bounding function $b(x) = 1 + x$ is $\alpha _b = \max {1, v_0}$.
--
--   **Formalization Note.** For $\alpha  \in  \tilde A $ the integrand is a.s. nonnegative, so the expectation is a Lebesgue integral in $[0, \infty ]$ and the supremum is taken in $[0, \infty ]$ ($0 \in  \tilde A $).
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §9.1, p.269, PDF 279

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_CIRandom

open MeasureTheory
open scoped ENNReal

namespace BauerleRiederMDP.LQ.Supplement

/-- **The constant `v_0` of §9.1** (Bäuerle & Rieder, *Markov Decision Processes with Applications
to Finance* (2011), §9.1, p.269, PDF 279): `Ã := {α ∈ ℝ^d | 1 + α · R_1 ≥ 0 ℙ-a.s.}` and
`v_0 := sup_{α ∈ Ã} 𝔼(1 + α · R_1)`; the contraction constant of the bounding function
`b(x) = 1 + x` is `α_b = max{1, v_0}`.

**Formalization Note.** For `α ∈ Ã` the integrand is a.s. nonnegative, so the expectation is a
Lebesgue integral in `[0, ∞]` and the supremum is taken in `[0, ∞]` (`0 ∈ Ã`). -/
noncomputable def CIRandom.v0 {d : ℕ} (C : CIRandom d) : ℝ≥0∞ :=
  ⨆ α ∈ {α : Fin d → ℝ | ∀ᵐ z ∂C.μR, 0 ≤ 1 + ∑ k, α k * z k},
    ∫⁻ z, ENNReal.ofReal (1 + ∑ k, α k * z k) ∂C.μR

end BauerleRiederMDP.LQ.Supplement


