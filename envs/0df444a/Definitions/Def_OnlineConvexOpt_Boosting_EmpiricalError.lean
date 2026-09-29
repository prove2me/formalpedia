-- Prove2me | Definitions.Def_OnlineConvexOpt_Boosting_EmpiricalError
-- name    : OnlineConvexOpt_Boosting_EmpiricalError
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T17:33:40.319638+00:00
-- url     : https://prove2.me/theorems/25facde0-bab0-43c5-9939-5bab5de5e995
-- title:
--   Weighted and uniform empirical error
-- statement:
--   Two declarations. `EmpiricalErrorWeighted S p h` is $\mathrm{error}_{S,p}(h) =
--   \sum_i p(i)\cdot\mathbf 1[h(x_i)\ne y_i]$ (p. 189), the empirical error of `h` on sample
--   `S`, weighted by a distribution `p` over the sample indices. `EmpiricalError S h` is the
--   uniformly-weighted special case, `error_S(h)` (p. 188, Theorem 11.2's own quantity).
--   Labels and predictions are real-valued (`±1`), the standard convention this chapter needs
--   for the majority-vote output `h̄ = sign(∑h_t)` to be meaningful.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 188-189 (PDF p. 210-211)

import Mathlib

namespace OnlineConvexOpt.Boosting

variable {X : Type*} {m : ℕ}

/-- The empirical error of a hypothesis `h` on sample `S`, weighted by a distribution `p`
(Hazan, *Introduction to Online Convex Optimization*, 2nd ed., arXiv:1909.05207v3, p. 189, PDF
p. 211): `error_{S,p}(h) = ∑_i p(i)·1[h(x_i)≠y_i]`. Labels and predictions are real-valued
(`±1`, the standard boosting/majority-vote convention this chapter uses for `h̄ = sign(∑h_t)`
to be meaningful). -/
noncomputable def EmpiricalErrorWeighted (S : Fin m → X × ℝ) (p : Fin m → ℝ) (h : X → ℝ) : ℝ :=
  ∑ i : Fin m, p i * (if h (S i).1 ≠ (S i).2 then (1 : ℝ) else 0)

/-- The (uniformly-weighted) empirical error `error_S(h)` (p. 188, PDF p. 210, Theorem 11.2's
own `error_S(h̄)`): `EmpiricalErrorWeighted` at the uniform distribution over `S`'s `m`
examples. -/
noncomputable def EmpiricalError (S : Fin m → X × ℝ) (h : X → ℝ) : ℝ :=
  EmpiricalErrorWeighted S (fun _ => 1 / (m : ℝ)) h

end OnlineConvexOpt.Boosting


