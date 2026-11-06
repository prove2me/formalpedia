-- Prove2me | Definitions.Def_SKAnnealing_Sampling_IsStdBrownian
-- name    : SKAnnealing_Sampling_IsStdBrownian
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:14:17.88053+00:00
-- url     : https://prove2.me/theorems/97b02fed-9799-4e37-a8bb-6bbc91e2d419
-- title:
--   Standard Brownian motion in $\mathbb R^N$
-- statement:
--   A process $(B_t)_{t\ge0}$ with values in $\mathbb R^N$ on a probability space $(\Omega,P)$ is a **standard Brownian motion** if each coordinate $t\mapsto B_t^{(i)}$ is a real Brownian motion (Gaussian finite-dimensional distributions with covariance $\min(s,t)$, almost surely continuous paths) and the $N$ coordinate processes are mutually independent.
--
--   It drives stochastic localization (display (3) and its posterior form (4)) in Lemma 2.4 and display (7).
--
--   **Formalization Note** Each coordinate is Mathlib's `IsBrownianReal`, with time in $[0,\infty)$; independence is `iIndepFun` of the coordinate paths. The statements that use it quantify over every probability space carrying such a process.
-- source:
--   Du, Huang, Mohanty, Rajaraman, Sampling from the Sherrington–Kirkpatrick Model up to Criticality, arXiv:2610.17717 (PDF of October 29, 2026), p. 3; Lemma 2.4, p. 11; display (7), p. 13

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SKAnnealing.Sampling

/-- `B` is a **standard Brownian motion in `ℝ^N`** under `P`: each coordinate `t ↦ B_t^{(i)}` is a real
Brownian motion (Mathlib's `IsBrownianReal`: Brownian finite-dimensional laws and a.s. continuous paths) and
the `N` coordinate processes are mutually independent.

Du, Huang, Mohanty, Rajaraman, *Sampling from the Sherrington–Kirkpatrick Model up to Criticality*, arXiv:2610.17717 (PDF of October 29, 2026), p. 3 ("a Brownian motion `(B_t)_{t ≥ 0}`"), display (7), p. 13, Lemma 2.4, p. 11.

**Formalization Note** Time is `ℝ≥0`, as in Mathlib. Wiener measure is not constructed: theorems quantify
over every probability space carrying such a `B`. -/
def IsStdBrownian {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (B : ℝ≥0 → Ω → (Fin N → ℝ))
    (P : Measure Ω) : Prop :=
  (∀ i : Fin N, IsBrownianReal (fun t ω => B t ω i) P) ∧
    iIndepFun (fun (i : Fin N) (ω : Ω) => fun t : ℝ≥0 => B t ω i) P

end SKAnnealing.Sampling


