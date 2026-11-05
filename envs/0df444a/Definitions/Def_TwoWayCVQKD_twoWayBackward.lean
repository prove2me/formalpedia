-- Prove2me | Definitions.Def_TwoWayCVQKD_twoWayBackward
-- name    : TwoWayCVQKD_twoWayBackward
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:45:51.466826+00:00
-- url     : https://prove2.me/theorems/42474f9c-71d2-46b0-9375-efad5585f204
-- title:
--   Alice's modulation and the second cloner $(T,W):A_2\to B_2$
-- statement:
--   On the perturbed mode $A_1$ Alice performs a Gaussian modulation by adding the stochastic amplitude $\alpha=(Q_A+iP_A)/2$, which shifts the quadratures of the mode by $Q_A$ and $P_A$. The modulated mode $A_2$ goes back through a second, independent entangling cloner $(T,W):A_2\to B_2$. For each quadrature, this definition gives the output mode $B_2$ received by Bob and the mode $E_2'$ that Eve keeps.
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, p.8 and Fig. 5 (p.4)

import Mathlib
import Definitions.Def_TwoWayCVQKD_twoWayForward
import Definitions.Def_TwoWayCVQKD_aliceVar

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, p.8 and Fig. 5 (p.4): quadrature
`k` of the second entangling cloner `(T, W) : A₂ → B₂`. Alice adds `α = (Q_A + iP_A)/2`, so the
quadratures of `A₂` are those of `A₁` plus `Q_A`, `P_A`. The other input is `E₂`, and the outputs
are `B₂` and Eve's mode `E₂'`. -/
noncomputable def twoWayBackward (T : ℝ) (k : Fin 2) : (TwoWaySrc → ℝ) × (TwoWaySrc → ℝ) :=
  cloner T ((twoWayForward T k).1 + aliceVar k)
    (Pi.single (Sum.inr (Sum.inr (Sum.inr (Sum.inl (0, k))))) 1)

end TwoWayCVQKD


