-- Prove2me | Definitions.Def_RecursiveStopping_MarkovFlow
-- name    : RecursiveStopping_MarkovFlow
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:41:01.447061+00:00
-- url     : https://prove2.me/theorems/dd79eeaa-9ff6-42d0-a172-6eeb22837133
-- title:
--   Right-continuous, strong Markov, quasi left-continuous flow
-- statement:
--   A map $X:S\times[0,\infty)\times\Omega\to S$, $(x,t,\omega)\mapsto X^x_t(\omega)$, is a **right-continuous strong Markov flow** on $(\Omega,\mathcal F,\mathbb F,\mathsf P)$ when
--
--   1. $X^x_0=x$ $\mathsf P$-a.s. for every $x\in S$;
--   2. every path $t\mapsto X^x_t(\omega)$ is right-continuous;
--   3. every process $X^x$ is $\mathbb F$-adapted;
--   4. $X$ has the strong Markov property (`IsStrongMarkovFlow`);
--   5. $X$ is quasi left-continuous (`IsQuasiLeftContinuousFlow`).
--
--   These are the process axioms of the paper's §2: $X$ is a right-continuous, strong Markov, quasi left-continuous process realised as a stochastic flow, and $\mathsf P_x$ is the law of $X^x$ under the single measure $\mathsf P$.
-- source:
--   Colaneri & De Angelis, A Class of Recursive Optimal Stopping Problems with Applications to Stock Trading, arXiv:1905.02650v4, §2, p.5

import Mathlib
import Definitions.Def_RecursiveStopping_IsStrongMarkovFlow
import Definitions.Def_RecursiveStopping_IsQuasiLeftContinuousFlow

open MeasureTheory
open scoped NNReal ENNReal

namespace RecursiveStopping

/-- The process axioms of Colaneri & De Angelis, arXiv:1905.02650v4, §2, p.5: "Let
`X = (X_t)_{t≥0}` be a right-continuous, strong Markov process, taking values in `ℝ^d`, that
can be realised as a stochastic flow `(t, x) ↦ X^x_t`, so that `X^x_0 = x`, `P`-a.s. We also
assume that `X` is quasi left-continuous".

`MarkovFlow P 𝔽 X` for a flow `X : S → ℝ≥0 → Ω → S` (`X x t ω = X^x_t(ω)`):
1. `X^x_0 = x` `P`-a.s. for every `x`;
2. every path `t ↦ X^x_t(ω)` is right-continuous;
3. every `X^x` is adapted to `𝔽`;
4. the strong Markov property (`IsStrongMarkovFlow`);
5. quasi left-continuity (`IsQuasiLeftContinuousFlow`).

**Formalization Note** `P_x` is the law of the flow started at `x` under the single
measure `P`, so `E_x[f(X_·)] = E[f(X^x_·)]` as on p.5. -/
structure MarkovFlow {S Ω : Type*} [TopologicalSpace S] [MeasurableSpace S]
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) (𝔽 : Filtration ℝ≥0 mΩ)
    (X : S → ℝ≥0 → Ω → S) : Prop where
  init : ∀ x, ∀ᵐ ω ∂P, X x 0 ω = x
  right_cont : ∀ x ω (t : ℝ≥0), ContinuousWithinAt (fun s => X x s ω) (Set.Ici t) t
  adapted : ∀ x, Adapted 𝔽 (X x)
  strong_markov : IsStrongMarkovFlow P 𝔽 X
  quasi_left_cont : IsQuasiLeftContinuousFlow P 𝔽 X

end RecursiveStopping


