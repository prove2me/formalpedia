-- Prove2me | Definitions.Def_GeomDRSub_Supplement_OracleStrategy
-- name    : GeomDRSub_Supplement_OracleStrategy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:38:10.506042+00:00
-- url     : https://prove2.me/theorems/59fdfa60-19cd-4a4d-af1b-700f8e25a633
-- title:
--   Randomized oracle algorithm (adaptive strategy, uniform in the dimension)
-- statement:
--   A **randomized oracle algorithm** with $m$ real inputs is one rule for every dimension $d$. It draws an internal seed $\omega$ from a space $\Omega$ and receives $d$ and inputs $x\in\mathbb R^m$ (for instance $(\varepsilon,M,B,v,D)$ offline, or $(T,D,M,B)$ online). Its $k$-th call ($k=0,1,\dots$) is
--
--   $$c_k=\mathrm{step}(d,x,k,\omega,r_0,\dots,r_{k-1}),$$
--
--   a function of the inputs, the seed, and the responses $r_0,\dots,r_{k-1}$ to its previous calls. The algorithm therefore learns about the objective and the feasible set only through the oracles. For fixed $d,x,k$, the map $(\omega,r_0,\dots,r_{k-1})\mapsto c_k$ is required to be measurable.
--
--   This is the algorithm model behind the offline coefficient of Definition 6.1 and the uniform online algorithms of Section 7.2.
--
--   **Formalization Note** Only oracle calls are counted and all other computation is free, as in (129) and (213), which count calls only. The probability measure on $\Omega$ is supplied together with the algorithm in `OfflineAchievable` and `OnlineAchievable`.
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Definition 6.1, p.33 ("one randomized algorithm"), and Section 7.2, p.52 ("a uniform online algorithm")

import Mathlib
import Definitions.Def_GeomDRSub_Supplement_OCall
import Definitions.Def_GeomDRSub_Supplement_OResp

namespace GeomDRSub.Supplement

/-- **Randomized oracle algorithm (adaptive strategy).** Aggarwal–Lu, *Geometry-Dependent Online and Offline Approximation for Non-Monotone
DR-Submodular Maximization*, arXiv:2610.00545, Definition 6.1 (p.33,
"one randomized algorithm") and Section 7.2 (p.52, "a uniform online algorithm is a single
algorithm that receives `d, T, D, M, B` and is run on every such instance").

An `OracleStrategy Ω m` is one algorithm for every dimension. It has internal randomness `ω ∈ Ω`
(a probability measure on `Ω` is supplied with it, see `OfflineAchievable`, `OnlineAchievable`)
and receives the dimension `d` and `m` real inputs `x : Fin m → ℝ`. Its `k`-th call (0-based) is
`step d x k ω r`, where `r : Fin k → OResp d` are the responses to its first `k` calls. Thus each
call is a function of the inputs, the seed and the previous responses only: the algorithm sees the
objective and the feasible set only through the oracles. For each `d`, `x`, `k`, the map
`(ω, r) ↦ step d x k ω r` is measurable.

**Formalization Note.** Only oracle calls are counted; all other computation is free (the paper
counts calls only, (129) and (213)). Measurability of the step maps is the standard meaning of a
randomized algorithm and guarantees that the outputs are random variables. -/
structure OracleStrategy (Ω : Type) [MeasurableSpace Ω] (m : ℕ) where
  /-- the `k`-th call, as a function of dimension, inputs, seed and the first `k` responses -/
  step : (d : ℕ) → (Fin m → ℝ) → (k : ℕ) → Ω → (Fin k → OResp d) → OCall d
  /-- each step map is jointly measurable in the seed and the previous responses -/
  measurable_step : ∀ (d : ℕ) (x : Fin m → ℝ) (k : ℕ),
    Measurable (fun q : Ω × (Fin k → OResp d) => step d x k q.1 q.2)

end GeomDRSub.Supplement


