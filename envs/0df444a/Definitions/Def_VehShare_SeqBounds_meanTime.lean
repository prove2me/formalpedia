-- Prove2me | Definitions.Def_VehShare_SeqBounds_meanTime
-- name    : VehShare_SeqBounds_meanTime
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:32:25.697166+00:00
-- url     : https://prove2.me/theorems/36246b6f-3bcb-472e-8d43-bab3f8ab7b71
-- title:
--   Mean travel time $1/\mu_{ij}$
-- statement:
--   The **mean travel time** of the pair $(i,j)$ is
--
--   $$
--   \frac1{\mu_{ij}}=\beta_{ij}\,(-T)^{-1}\mathbf 1,
--   $$
--
--   the mean absorption time of the phase-type law (a zero-length trip contributes $0$). It is the quantity $1/\mu_{ij}$ of the paper (p. 4).
--
--   **Formalization Note** Lean's matrix inverse is $0$ on a singular matrix. Here $-T$ is invertible because from every stage a stage with positive exit rate is reachable (a field of the instance), so the value is the true mean.
-- source:
--   Benjaafar, Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN 3998297 (version of 2023-01-10), https://ssrn.com/abstract=3998297, p. 4 ("with mean 1/µij")

import Mathlib
import Definitions.Def_VehShare_SeqBounds_subGen

namespace VehShare.SeqBounds

/-- **Mean travel time `1/μ_ij`.**
Benjaafar, Shen, *Pricing in On-Demand (and One-Way) Vehicle Sharing Networks*, SSRN 3998297
(version of 2023-01-10), p. 4 ("with mean `1/μ_ij`").

`meanTime P i j = β ⬝ (−T)⁻¹ 𝟙`, the mean absorption time of the phase-type law of `i → j`
(a trip of length zero, probability `1 − ∑ β`, contributes 0).

**Formalization Note.** `Matrix.inv` returns 0 on a singular matrix; here `−T` is invertible
because every stage reaches a stage with positive exit rate (field `absorbing` of `Instance`), so
the value is the true mean. -/
noncomputable def meanTime (P : Instance) (i j : P.L) : ℝ :=
  dotProduct (P.β i j) (Matrix.mulVec (-subGen P i j)⁻¹ (fun _ => (1 : ℝ)))

end VehShare.SeqBounds


