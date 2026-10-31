-- Prove2me | Definitions.Def_KallMayerSLP_ValueOfInfo_EVPI
-- name    : KallMayerSLP_ValueOfInfo_EVPI
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:15:34.072828+00:00
-- url     : https://prove2.me/theorems/aac30994-89f8-4d93-915d-b1a5d3ea2559
-- title:
--   Expected value of perfect information $EVPI=RS-WS$ (2.72)
-- statement:
--   The expected value of perfect information (Avriel–Williams),
--
--   $$
--   EVPI=RS-WS,
--   $$
--
--   the most a decision maker would pay for exact information on the future outcome of $\xi$.
--
--   **Formalization Note** The difference is taken in the extended reals. When $RS$ and $WS$ are finite it is the ordinary difference; the book leaves $\infty-\infty$ undefined, where Lean's convention returns $-\infty$, and the theorems that need a defined difference assume it.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, eq. (2.72), p.246 (PDF 255)

import Mathlib
import Definitions.Def_KallMayerSLP_ValueOfInfo_RS
import Definitions.Def_KallMayerSLP_ValueOfInfo_WS

open MeasureTheory

namespace KallMayerSLP.ValueOfInfo

/-- **The expected value of perfect information, (2.72).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, eq. (2.72), p.246 (PDF 255):
`EVPI := RS − WS`.

**Formalization Note.** Subtraction in `EReal`. When `RS` and `WS` are finite, the case in which the
book uses the difference, it is ordinary subtraction; the book leaves `∞ − ∞` undefined (Mathlib's
`EReal` returns `⊤ − ⊤ = ⊥`, `⊥ − ⊥ = ⊥`), and the theorems that need a defined difference state it. -/
noncomputable def EVPI {r n₁ m₁ n₂ m₂ : ℕ} (P : TwoStageSLP r n₁ m₁ n₂ m₂)
    (μ : Measure (Fin r → ℝ)) : EReal :=
  RS P μ - WS P μ

end KallMayerSLP.ValueOfInfo


