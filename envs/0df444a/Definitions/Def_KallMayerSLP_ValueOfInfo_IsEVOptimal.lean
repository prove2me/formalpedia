-- Prove2me | Definitions.Def_KallMayerSLP_ValueOfInfo_IsEVOptimal
-- name    : KallMayerSLP_ValueOfInfo_IsEVOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:14:58.883401+00:00
-- url     : https://prove2.me/theorems/d2b3bee5-6c89-4f1a-b009-bc392d6d2c70
-- title:
--   $\hat x$ is an optimal first-stage solution of the EV problem
-- statement:
--   A first-stage decision $\hat x$ is an optimal first stage solution of the expected value problem (2.67) if there is a second-stage $\hat y$ such that
--
--   1. $(\hat x,\hat y)$ is feasible: $A\hat x=b$, $T(\bar\xi)\hat x+W(\bar\xi)\hat y=h(\bar\xi)$, $\hat x\ge0$, $\hat y\ge0$;
--   2. it attains the optimal value: $c^{\mathsf T}\hat x+q(\bar\xi)^{\mathsf T}\hat y=EV$.
--
--   $EEV$ and $VSS$ are evaluated at such an $\hat x$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, §2.3, p.244 (PDF 253): 'any optimal first stage solution x̂ of the EV problem (2.67)'

import Mathlib
import Definitions.Def_KallMayerSLP_ValueOfInfo_EV

open MeasureTheory Matrix

namespace KallMayerSLP.ValueOfInfo

/-- **`x̂` is an optimal first stage solution of the EV problem (2.67).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, p.244 (PDF 253): "with the first
stage solution fixed as any optimal first stage solution `x̂` of the EV problem (2.67)".

There is a second-stage `ŷ` such that `(x̂, ŷ)` is feasible for (2.67) (`Ax̂ = b`,
`T(ξ̄)x̂ + W(ξ̄)ŷ = h(ξ̄)`, `x̂, ŷ ≥ 0`) and attains its optimal value: `cᵀx̂ + qᵀ(ξ̄)ŷ = EV`. -/
def IsEVOptimal {r n₁ m₁ n₂ m₂ : ℕ} (P : TwoStageSLP r n₁ m₁ n₂ m₂)
    (μ : Measure (Fin r → ℝ)) (xhat : Fin n₁ → ℝ) : Prop :=
  ∃ yhat : Fin n₂ → ℝ, P.A *ᵥ xhat = P.b ∧
    P.T (xiBar μ) *ᵥ xhat + P.W (xiBar μ) *ᵥ yhat = P.h (xiBar μ) ∧ 0 ≤ xhat ∧ 0 ≤ yhat ∧
    ((P.c ⬝ᵥ xhat + P.q (xiBar μ) ⬝ᵥ yhat : ℝ) : EReal) = EV P μ

end KallMayerSLP.ValueOfInfo


