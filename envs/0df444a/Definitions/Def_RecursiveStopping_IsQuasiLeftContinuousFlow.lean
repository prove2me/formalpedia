-- Prove2me | Definitions.Def_RecursiveStopping_IsQuasiLeftContinuousFlow
-- name    : RecursiveStopping_IsQuasiLeftContinuousFlow
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:39:58.002518+00:00
-- url     : https://prove2.me/theorems/dfc6fe03-8b96-46ce-b3ec-086cf48ac4d8
-- title:
--   Quasi left-continuity of a stochastic flow
-- statement:
--   A stochastic flow $X=(X^x_t)$ on $(\Omega,\mathcal F,\mathsf P)$ with values in a topological space $S$ is **quasi left-continuous** (left continuous over stopping times) when, for every starting point $x$ and every sequence $(\tau_n)$ of $\mathbb F$-stopping times increasing to a stopping time $\tau$,
--
--   $$
--   X^x_{\tau_n}\longrightarrow X^x_\tau\qquad\mathsf P\text{-a.s. on }\{\tau<\infty\}.
--   $$
--
--   Together with right-continuity of paths and the strong Markov property this is the standard regularity of a Hunt-type process.
-- source:
--   Colaneri & De Angelis, A Class of Recursive Optimal Stopping Problems with Applications to Stock Trading, arXiv:1905.02650v4, §2, p.5

import Mathlib

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace RecursiveStopping

/-- **Quasi left-continuity** (Colaneri & De Angelis, arXiv:1905.02650v4, §2, p.5: "We also
assume that X is quasi left-continuous, i.e., left continuous over stopping times").

For every starting point `x`, every sequence of `𝔽`-stopping times `τ_n` increasing to a
stopping time `τ`, `X^x_{τ_n} → X^x_τ` `P`-a.s. on `{τ < ∞}`. -/
def IsQuasiLeftContinuousFlow {S Ω : Type*} [TopologicalSpace S] [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (𝔽 : Filtration ℝ≥0 mΩ) (X : S → ℝ≥0 → Ω → S) : Prop :=
  ∀ (x : S) (τn : ℕ → Ω → ℝ≥0∞) (τ : Ω → ℝ≥0∞),
    (∀ n, IsStoppingTime 𝔽 (τn n)) → IsStoppingTime 𝔽 τ →
    (∀ ω, Monotone (fun n => τn n ω)) →
    (∀ ω, Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω))) →
    ∀ᵐ ω ∂P, τ ω ≠ ⊤ →
      Tendsto (fun n => X x (τn n ω).toNNReal ω) atTop (𝓝 (X x (τ ω).toNNReal ω))

end RecursiveStopping


