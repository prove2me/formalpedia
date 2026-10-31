-- Prove2me | Definitions.Def_KallMayerSLP_ValueOfInfo_EV
-- name    : KallMayerSLP_ValueOfInfo_EV
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:14:00.375723+00:00
-- url     : https://prove2.me/theorems/c276466c-dab7-44ff-b0ae-402b5c559c2a
-- title:
--   Optimal value $EV$ of the expected value problem (2.67)
-- statement:
--   The optimal value of the problem obtained by replacing $\xi$ by its mean $\bar\xi$:
--
--   $$
--   EV=\min_{x,y}\{c^{\mathsf T}x+q(\bar\xi)^{\mathsf T}y : Ax=b,\ T(\bar\xi)x+W(\bar\xi)y=h(\bar\xi),\ x\ge0,\ y\ge0\}=\gamma(\bar\xi).
--   $$
--
--   **Formalization Note** Defined as the wait-and-see value at the mean, $\gamma(\bar\xi)$, as the book writes on p.246; an infimum in $[-\infty,+\infty]$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, eq. (2.67), p.244 (PDF 253)

import Mathlib
import Definitions.Def_KallMayerSLP_ValueOfInfo_gamma
import Definitions.Def_KallMayerSLP_ValueOfInfo_xiBar

open MeasureTheory

namespace KallMayerSLP.ValueOfInfo

/-- **The optimal value `EV` of the expected value problem, (2.67).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, eq. (2.67), p.244 (PDF 253):
`EV := min_{x,y} {cᵀx + qᵀ(ξ̄)y}` s.t. `Ax = b`, `T(ξ̄)x + W(ξ̄)y = h(ξ̄)`, `x, y ≥ 0`, with
`ξ̄ = 𝔼_ξ[ξ]`.

This is the wait-and-see LP evaluated at the mean, `EV = γ(ξ̄)`, as the book itself writes on p.246.

**Formalization Note.** Infimum in `EReal` (`+∞` infeasible, `−∞` unbounded). -/
noncomputable def EV {r n₁ m₁ n₂ m₂ : ℕ} (P : TwoStageSLP r n₁ m₁ n₂ m₂)
    (μ : Measure (Fin r → ℝ)) : EReal :=
  gamma P (xiBar μ)

end KallMayerSLP.ValueOfInfo


