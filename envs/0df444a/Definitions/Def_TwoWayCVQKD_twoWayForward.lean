-- Prove2me | Definitions.Def_TwoWayCVQKD_twoWayForward
-- name    : TwoWayCVQKD_twoWayForward
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:44:47.050206+00:00
-- url     : https://prove2.me/theorems/1413ee9b-82ea-4cee-a071-c5ccf5b55b3a
-- title:
--   First entangling cloner $(T,W):C_1\to A_1$
-- statement:
--   On the forward path, the mode $C_1$ of Bob's EPR pair undergoes an entangling cloner $(T,W):C_1\to A_1$. For each quadrature, this definition gives the perturbed mode $A_1$ that reaches Alice and the mode $E_1'$ that Eve keeps.
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, p.8 and Fig. 5 (p.4)

import Mathlib
import Definitions.Def_TwoWayCVQKD_cloner
import Definitions.Def_TwoWayCVQKD_TwoWaySrc

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, p.8 and Fig. 5 (p.4): quadrature
`k` of the first entangling cloner `(T, W) : C₁ → A₁`. Its inputs are `C₁` and `E₁`, and its outputs
are the perturbed mode `A₁` and Eve's mode `E₁'`. -/
noncomputable def twoWayForward (T : ℝ) (k : Fin 2) : (TwoWaySrc → ℝ) × (TwoWaySrc → ℝ) :=
  cloner T (Pi.single (Sum.inr (Sum.inl (1, k))) 1)
    (Pi.single (Sum.inr (Sum.inr (Sum.inl (0, k)))) 1)

end TwoWayCVQKD


