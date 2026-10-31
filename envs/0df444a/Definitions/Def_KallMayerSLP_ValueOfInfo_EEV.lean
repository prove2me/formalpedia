-- Prove2me | Definitions.Def_KallMayerSLP_ValueOfInfo_EEV
-- name    : KallMayerSLP_ValueOfInfo_EEV
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:13:57.530165+00:00
-- url     : https://prove2.me/theorems/e749edc0-a5d1-47e9-bab2-4d71df1dbac2
-- title:
--   Expected result of the EV solution, $EEV$ (2.69)
-- statement:
--   For a first-stage decision $\hat x$ (in the book, an optimal first-stage solution of the EV problem),
--
--   $$
--   EEV=c^{\mathsf T}\hat x+\mathbb E_\xi\big[\min_y\{q(\xi)^{\mathsf T}y : W(\xi)y=h(\xi)-T(\xi)\hat x,\ y\ge0\}\big],
--   $$
--
--   the expected cost of implementing $\hat x$ in the recourse problem.
--
--   **Formalization Note** $EEV$ depends on the chosen $\hat x$ (the book notes $EEV(\hat x)\ne EEV(\tilde x)$ is possible), so $\hat x$ is an argument; the theorems assume its EV-optimality. The inner minimum is the recourse function and the expectation is `eExp`.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, eq. (2.69), p.244 (PDF 253)

import Mathlib
import Definitions.Def_KallMayerSLP_ValueOfInfo_eExp
import Definitions.Def_KallMayerSLP_ValueOfInfo_recourse

open MeasureTheory Matrix

namespace KallMayerSLP.ValueOfInfo

/-- **The expected result of the EV solution, `EEV`, (2.69).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, eq. (2.69), p.244 (PDF 253):
`EEV := cᵀx̂ + 𝔼_ξ[min_y {qᵀ(ξ)y | W(ξ)y = h(ξ) − T(ξ)x̂, y ≥ 0}]`, for "any optimal first stage
solution `x̂` of the EV problem (2.67)".

**Formalization Note.** `EEV` depends on the chosen `x̂` (the book, p.244: "`EEV(x̂) ≠ EEV(x̃)`" is
possible), so `x̂` is an argument; the theorems state its EV-optimality (`IsEVOptimal`) as a
hypothesis. The inner `min_y` is the recourse function `Q(x̂; ξ)` (an `EReal` infimum) and the
expectation is `eExp`. -/
noncomputable def EEV {r n₁ m₁ n₂ m₂ : ℕ} (P : TwoStageSLP r n₁ m₁ n₂ m₂)
    (μ : Measure (Fin r → ℝ)) (xhat : Fin n₁ → ℝ) : EReal :=
  ((P.c ⬝ᵥ xhat : ℝ) : EReal) + eExp μ (fun ξ => recourse P xhat ξ)

end KallMayerSLP.ValueOfInfo


