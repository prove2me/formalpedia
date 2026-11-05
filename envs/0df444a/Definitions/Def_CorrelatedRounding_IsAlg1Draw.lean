-- Prove2me | Definitions.Def_CorrelatedRounding_IsAlg1Draw
-- name    : CorrelatedRounding_IsAlg1Draw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:35:18.361689+00:00
-- url     : https://prove2.me/theorems/eb656032-019e-479c-82bd-6469c62a6767
-- title:
--   The draws of Algorithm 1
-- statement:
--   A family $(E_k)_k$ of real random variables on a measure space is a draw of Algorithm 1 when it is independent and each $E_k$ with $y_k>0$ is exponentially distributed with rate $y_k$, that is, with mean $1/y_k$.
--
--   **Formalization Note.** Definition 1 assumes $y_k>0$ without loss. Here $y_k=0$ is allowed and such an entry is unconstrained, because its clock is $\infty$ at every item. The law $\mathrm{Exp}(0)$ would not be a probability measure.
-- source:
--   Ma, Order-optimal Correlated Rounding for Fulfilling Multi-item E-commerce Orders, arXiv:2207.04774v4, Algorithm 1, p.10

import Mathlib
import Definitions.Def_CorrelatedRounding_y

open MeasureTheory ProbabilityTheory

namespace CorrelatedRounding

/-- **The draws of Algorithm 1.** W. Ma, *Order-optimal Correlated Rounding for Fulfilling Multi-item E-commerce Orders*, arXiv:2207.04774v4,
Algorithm 1, p.10: "for k = 1,…,K do E_k ← independent draw from Exponential distribution with mean
1/y_k".

`E` is an independent family, and `E k` has law `Exp(rate y_k)` whenever `y_k > 0`.

**Formalization Note.** Definition 1 assumes `y_k > 0` "without loss". Here `y_k = 0` is allowed, and such
an entry is unconstrained: its clock is `⊤` at every item. Writing `expMeasure (y k)` without the guard
would make the draw unsatisfiable on such an instance, since `expMeasure 0` is not a probability measure.
`HasLaw` includes the almost-everywhere measurability of `E k`. -/
def IsAlg1Draw {q K : ℕ} {Ω : Type*} [MeasurableSpace Ω] (u : Fin K → Fin q → ℝ) (μ : Measure Ω)
    (E : Fin K → Ω → ℝ) : Prop :=
  iIndepFun E μ ∧ ∀ k, 0 < y u k → HasLaw (E k) (expMeasure (y u k)) μ

end CorrelatedRounding


