-- Prove2me | Definitions.Def_TransitoryQueue_IsBrownianBridge
-- name    : TransitoryQueue_IsBrownianBridge
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:00:25.893814+00:00
-- url     : https://prove2.me/theorems/c598f91a-9821-45eb-b99a-07847def1c68
-- title:
--   Brownian bridge on $[0,1]$
-- statement:
--   A process $(Y_t)$ on a probability space $(\Omega,\mathcal F,P)$ is a **standard Brownian bridge** if, restricted to $t\in[0,1]$,
--
--   1. it is a Gaussian process (all finite-dimensional laws are Gaussian);
--   2. it is centred: $E[Y_t]=0$;
--   3. its covariance is $\mathrm{Cov}(Y_s,Y_t)=s(1-t)$ for $0\le s\le t\le1$;
--   4. almost every path is continuous on $[0,1]$.
--
--   These are exactly the laws of $B_t-tB_1$, $t\in[0,1]$, for a standard Brownian motion $B$, the paper's definition of $B^{\mathrm{br}}$.
--
--   **Formalization Note** Time is real and only $[0,1]$ is constrained. $Y_0=Y_1=0$ almost surely follows from clauses 2 and 3.
-- source:
--   Chakraborty and Honnappa, Strong Embeddings for Transitory Queueing Models, arXiv:1906.06740v1, §3.2, p.9

import Mathlib
open MeasureTheory ProbabilityTheory

namespace TransitoryQueue

/-- `Y` is a (standard) Brownian bridge on `[0, 1]` under `P`: it has the law of
`B_t - t B_1`, `t ∈ [0, 1]`, for a standard Brownian motion `B`. That is, `(Y_t)_{t ∈ [0,1]}` is
a centred Gaussian process with covariance `Cov(Y_s, Y_t) = s (1 - t)` for `0 ≤ s ≤ t ≤ 1`, and
almost every path is continuous on `[0, 1]`.
Chakraborty and Honnappa, *Strong Embeddings for Transitory Queueing Models*, arXiv:1906.06740v1, §3.2, p.9 ("the standard Brownian bridge B^br is a stochastic process that may be
defined as: B^br_t = B_t − tB_1, t ∈ [0, 1], for a Brownian motion B").

**Formalization Note** Time is real; only `t ∈ [0, 1]` is constrained, and the values of `Y`
outside `[0, 1]` play no role (the mission only evaluates `Y` at values of distribution
functions). `Y_0 = Y_1 = 0` a.s. follows from the covariance (variance `0`) and centring. The
finite-dimensional laws of `B_t - t B_1` are exactly those of a centred Gaussian process with
this covariance, so the clauses pin down the law of a continuous process on `[0, 1]`. -/
structure IsBrownianBridge {Ω : Type*} [MeasurableSpace Ω] (Y : ℝ → Ω → ℝ) (P : Measure Ω) :
    Prop where
  gaussian : IsGaussianProcess (fun t : Set.Icc (0 : ℝ) 1 => Y t) P
  centred : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∫ ω, Y t ω ∂P = 0
  covariance : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 → cov[Y s, Y t; P] = s * (1 - t)
  cont : ∀ᵐ ω ∂P, ContinuousOn (fun t => Y t ω) (Set.Icc 0 1)

end TransitoryQueue


