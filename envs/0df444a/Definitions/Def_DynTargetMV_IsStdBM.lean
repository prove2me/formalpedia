-- Prove2me | Definitions.Def_DynTargetMV_IsStdBM
-- name    : DynTargetMV_IsStdBM
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:38:39.092269+00:00
-- url     : https://prove2.me/theorems/9562ecb3-4a13-4ade-a984-fbbe5c3e2d6d
-- title:
--   A standard $d$-dimensional Brownian motion on $[0,T]$ for a filtration
-- statement:
--   The process $W=(W_1,\dots,W_d)^\top$ is a standard $d$-dimensional Brownian motion on $[0,T]$ for the filtration $(\mathcal F_t)$ of the probability space $(\Omega,P)$: each coordinate is a Brownian motion for the filtration, and for $0\le r\le s\le T$ the coordinate increments $W_j(s)-W_j(r)$ are independent and the vector increment $W(s)-W(r)$ is independent of $\mathcal F_r$.
--
--   **Formalization Note** Each coordinate is the published `EntropyMFG.Enhanced.BrownianOn`, which includes the usual conditions on the filtration. The source leaves the filtration implicit.
-- source:
--   He & Jiang, Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth, Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, §2.1, p.6

import Definitions.Def_EntropyMFG_Enhanced_Stochastic

open MeasureTheory ProbabilityTheory Set

namespace DynTargetMV

/-- `W = (W₁,…,W_d)` is a standard `d`-dimensional Brownian motion on `[0,T]` for the filtration `F`
of the probability space `(Ω, P)`. He & Jiang, *Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth*,
Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, §2.1, p.6.

**Formalization Note** The source only says "standard, d-dimensional Brownian motion". Each coordinate
is the published `EntropyMFG.Enhanced.BrownianOn`, which also asks that `F` satisfy the usual
conditions (null sets in `F 0`, right-continuity). For `0 ≤ r ≤ s ≤ T` the coordinate increments are
independent, and the vector increment is independent of `F r`. The Brownian motion is only needed on
`[0,T]`. -/
def IsStdBM {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (F : Filtration ℝ mΩ) (W : Fin d → ℝ → Ω → ℝ) (T : ℝ) : Prop :=
  IsProbabilityMeasure P ∧
  (∀ j, EntropyMFG.Enhanced.BrownianOn P F (W j) T) ∧
  ∀ r ∈ Icc 0 T, ∀ s ∈ Icc r T,
    iIndepFun (fun j ω => W j s ω - W j r ω) P ∧
    Indep (MeasurableSpace.comap (fun ω j => W j s ω - W j r ω) inferInstance) (F r) P

end DynTargetMV


