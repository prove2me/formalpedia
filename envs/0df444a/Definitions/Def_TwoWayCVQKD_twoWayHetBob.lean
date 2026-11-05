-- Prove2me | Definitions.Def_TwoWayCVQKD_twoWayHetBob
-- name    : TwoWayCVQKD_twoWayHetBob
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:47:21.494034+00:00
-- url     : https://prove2.me/theorems/34be7493-a67c-48ff-b468-06cc5341e38d
-- title:
--   Bob's variables $X_B=\{Q_B,P_B\}$ in $Het^2$
-- statement:
--   In the protocol $Het^2$ Bob heterodynes both modes. From $B_1$, with a vacuum mode $0$, he gets
--   $$
--   \hat q_-=2^{-1/2}(\hat Q_{B_1}-\hat Q_0),\qquad \hat p_+=2^{-1/2}(\hat P_{B_1}+\hat P_0),
--   $$
--   and from $B_2$, with a vacuum mode $0'$, he gets
--   $$
--   \hat Q_-=2^{-1/2}(\hat Q_{B_2}-\hat Q_{0'}),\qquad \hat P_+=2^{-1/2}(\hat P_{B_2}+\hat P_{0'}).
--   $$
--   He then decodes $\{Q_A,P_A\}$ through $Q_B:=Q_--Tq_-$ and $P_B:=P_++Tp_+$.
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, Eqs. (67)–(69), p.9

import Mathlib
import Definitions.Def_TwoWayCVQKD_twoWayBob

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, Eqs. (67)–(69), p.9: in `Het²`,
Bob measures `q̂₋ = 2^{-1/2}(Q̂_B₁ - Q̂₀)`, `p̂₊ = 2^{-1/2}(P̂_B₁ + P̂₀)` and
`Q̂₋ = 2^{-1/2}(Q̂_B₂ - Q̂₀')`, `P̂₊ = 2^{-1/2}(P̂_B₂ + P̂₀')`, and decodes `Q_B := Q₋ - T q₋`,
`P_B := P₊ + T p₊`. -/
noncomputable def twoWayHetBob (T : ℝ) : Fin 2 → TwoWaySrc → ℝ :=
  ![(Real.sqrt 2)⁻¹ • (twoWayBob T (1, 0) -
        Pi.single (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (0, 0)))))) 1) -
      T • ((Real.sqrt 2)⁻¹ • (twoWayBob T (0, 0) -
        Pi.single (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (0, 0)))))) 1)),
    (Real.sqrt 2)⁻¹ • (twoWayBob T (1, 1) +
        Pi.single (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (0, 1)))))) 1) +
      T • ((Real.sqrt 2)⁻¹ • (twoWayBob T (0, 1) +
        Pi.single (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (0, 1)))))) 1))]

end TwoWayCVQKD


