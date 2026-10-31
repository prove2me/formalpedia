-- Prove2me | Definitions.Def_KallMayerSLP_ValueOfInfo_VSS
-- name    : KallMayerSLP_ValueOfInfo_VSS
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:15:55.829995+00:00
-- url     : https://prove2.me/theorems/f470ae16-f5eb-4d79-8d6b-e648dad4bed3
-- title:
--   Value of the stochastic solution $VSS=EEV-RS$ (2.73)
-- statement:
--   The value of the stochastic solution (Birge),
--
--   $$
--   VSS=EEV-RS,
--   $$
--
--   the extra expected cost of using the first-stage solution $\hat x$ of the expected value problem instead of an optimal first-stage solution of the recourse problem.
--
--   **Formalization Note** $VSS$ is taken at the same $\hat x$ as $EEV$. The difference is taken in the extended reals; ordinary subtraction when both values are finite, and the book leaves $\infty-\infty$ undefined.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, eq. (2.73), p.246 (PDF 255)

import Mathlib
import Definitions.Def_KallMayerSLP_ValueOfInfo_RS
import Definitions.Def_KallMayerSLP_ValueOfInfo_EEV

open MeasureTheory

namespace KallMayerSLP.ValueOfInfo

/-- **The value of the stochastic solution, (2.73).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, eq. (2.73), p.246 (PDF 255):
`VSS := EEV − RS`.

**Formalization Note.** `VSS` inherits from `EEV` the dependence on the chosen EV-optimal `x̂`.
Subtraction in `EReal`: ordinary subtraction when `EEV` and `RS` are finite; the book leaves `∞ − ∞`
undefined (Mathlib's `EReal` returns `⊥`), and the theorems that need a defined difference state it. -/
noncomputable def VSS {r n₁ m₁ n₂ m₂ : ℕ} (P : TwoStageSLP r n₁ m₁ n₂ m₂)
    (μ : Measure (Fin r → ℝ)) (xhat : Fin n₁ → ℝ) : EReal :=
  EEV P μ xhat - RS P μ

end KallMayerSLP.ValueOfInfo


