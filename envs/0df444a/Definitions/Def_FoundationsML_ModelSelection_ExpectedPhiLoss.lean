-- Prove2me | Definitions.Def_FoundationsML_ModelSelection_ExpectedPhiLoss
-- name    : FoundationsML_ModelSelection_ExpectedPhiLoss
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:20:28.421305+00:00
-- url     : https://prove2.me/theorems/c8a2ea7b-1378-419f-a566-d8870d6d8243
-- title:
--   Expected Φ-loss L_Φ(h) (Eq. 4.10)
-- statement:
--   **Eq. (4.10), p. 75, PDF p. 92.** The expected $\Phi$-loss of a real-valued scoring function
--   $h:X\to\mathbb R$ is $L_\Phi(h) = \mathbb E_{x\sim D_X}[\eta(x)\Phi(-h(x)) +
--   (1-\eta(x))\Phi(h(x))]$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, Eq. (4.10), p. 75 (PDF p. 92)

import Mathlib
import Definitions.Def_FoundationsML_ModelSelection_PhiLossPointwise

open MeasureTheory

namespace FoundationsML.ModelSelection

/-- The expected Φ-loss of a real-valued scoring function `h : X → ℝ`,
`L_Φ(h) = E_{x∼D_X}[η(x) Φ(−h(x)) + (1 − η(x)) Φ(h(x))]` (Mohri, Rostamizadeh & Talwalkar,
*Foundations of Machine Learning*, 2nd ed., MIT Press 2018, Eq. (4.10), p. 75, PDF p. 92). -/
noncomputable def ExpectedPhiLoss {X : Type*} [MeasurableSpace X]
    (DX : Measure X) (η : X → ℝ) (Φ : ℝ → ℝ) (h : X → ℝ) : ℝ :=
  ∫ x, PhiLossPointwise η Φ x (h x) ∂DX

end FoundationsML.ModelSelection


