-- Prove2me | Definitions.Def_FTPLLinBandit_FTPLRun_thetaHat
-- name    : FTPLLinBandit_FTPLRun_thetaHat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:08:10.577035+00:00
-- url     : https://prove2.me/theorems/6b8fcfb4-ffd7-4283-a0a9-0ed084f1518e
-- title:
--   The estimates $\hat\theta_t$ of a run (recursion over rounds)
-- statement:
--   The **estimates** of a run are defined by recursion over rounds: the estimate $\hat\theta_t$ of round $t$ is the geometric-resampling estimator of round $t$ computed from the estimates $\hat\theta_0,\dots,\hat\theta_{t-1}$ of the earlier rounds, and the cumulative estimate is $\hat\Theta_{t}=\sum_{\tau<t}\hat\theta_\tau$ (Algorithm 1: "$\hat\Theta_1\leftarrow0$ … $\hat\Theta_{t+1}\leftarrow\hat\Theta_t+\hat\theta_t$").
--
--   **Formalization Note** Rounds are indexed from $0$; the value is computed outcome by outcome.
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, Algorithm 1, lines 2–9, p.8

import Mathlib
import Definitions.Def_FTPLLinBandit_FTPLRun_estimate

open MeasureTheory

namespace FTPLLinBandit

variable {d : ℕ} {A : Set (EuclideanSpace ℝ (Fin d))} {ν : Measure (EuclideanSpace ℝ (Fin d))}
  {x : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} {s : Scheme} {γ β : ℝ} {N : ℕ}
  {lam : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **The reward estimates `θ̂_t` of a run of Algorithm 1.** Wei, arXiv:2610.17818, Algorithm 1,
lines 2–9, p.8: "Initialization: Θ̂_1 ← 0. for t = 1, 2, … do Construct ρ_t from {θ̂_τ}_{τ<t} …
θ̂_t ← H_t(a_t − ā_t)y_t. Θ̂_{t+1} ← Θ̂_t + θ̂_t."

`run.thetaHat t ω` is the estimate of round `t` on the outcome `ω`, defined by recursion on `t`:
round `t`'s estimate (`FTPLRun.estimate`) is computed from the estimates of rounds `τ < t`. The
cumulative estimate is `Θ̂_t = ∑_{τ<t} θ̂_τ`.

**Formalization Note.** Rounds are indexed from `0`. The value of `past τ` for `τ ≥ t` is never
read by `FTPLRun.estimate`; it is set to `0`. -/
noncomputable def FTPLRun.thetaHat (run : FTPLRun A ν x s γ β N lam Ω P) (t : ℕ) (ω : Ω) :
    EuclideanSpace ℝ (Fin d) :=
  run.estimate (fun τ => if τ < t then run.thetaHat τ ω else 0) t ω
termination_by t

end FTPLLinBandit


