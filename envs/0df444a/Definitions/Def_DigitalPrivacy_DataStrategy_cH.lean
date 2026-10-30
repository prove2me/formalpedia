-- Prove2me | Definitions.Def_DigitalPrivacy_DataStrategy_cH
-- name    : DigitalPrivacy_DataStrategy_cH
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:04:53.961001+00:00
-- url     : https://prove2.me/theorems/14147672-e292-4298-a95a-e06113776e35
-- title:
--   $C_h(\xi)$ of Lemma 1
-- statement:
--   For $\psi>0$ define
--
--   $$C_h(\xi)=\frac1{1-\beta}\Big(-\xi^2+\xi\sqrt{\tfrac1\psi(1+\rho\xi)(1-P+P\xi)}\Big).$$
--
--   It is the root of the first-order condition $\partial\Pi/\partial C=0$ at fixed $\xi$; Lemma 1 shows that the optimal protection is $\max\{C_h(\xi),0\}$.
--
--   **Formalization Note** Literal; meant for $\psi>0$. $C_h$ can be negative (footnote 29).
-- source:
--   Fainmesser, Galeotti, Momot, Digital Privacy, author manuscript (April 2022 draft; SSRN 3459274), Lemma 1, p. 29 (PDF 30)

import Mathlib

namespace DigitalPrivacy.DataStrategy

/-- **`C_h(ξ) = (1/(1 − β))(−ξ² + ξ√((1/ψ)(1 + ρξ)(1 − P + Pξ)))`, Lemma 1.**
Fainmesser, Galeotti, Momot, *Digital Privacy*, author manuscript (April 2022 draft; SSRN 3459274), Lemma 1, p. 29 (PDF 30): "Ch(ξ) = 1/(1−β) (−ξ² + ξ √((1/ψ)(1 + ρξ)(1 − P + Pξ)))".
It is the root of the first-order condition in `C` of the profit at fixed `ξ` (OA B.1).

**Formalization Note.** The formula is literal; it is meant for `ψ > 0` (at `ψ = 0` Lean reads
`1/0 = 0`, a value no theorem uses). `C_h` can be negative (footnote 29, p. 29); Lemma 1 takes
`max{C_h(ξ), 0}`. -/
noncomputable def cH (β ρ P ψ ξ : ℝ) : ℝ :=
  (1 / (1 - β)) * (-ξ ^ 2 + ξ * Real.sqrt ((1 / ψ) * (1 + ρ * ξ) * (1 - P + P * ξ)))

end DigitalPrivacy.DataStrategy


