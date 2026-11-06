-- Prove2me | Definitions.Def_GeomDRSub_Alg1Run
-- name    : GeomDRSub_Alg1Run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:10:13.195758+00:00
-- url     : https://prove2.me/theorems/80caef04-3f24-4f7d-8d8a-9792ac7b925c
-- title:
--   Processes of a run of Algorithm 1
-- statement:
--   A run of Algorithm 1 on a sample space $\Omega$ consists of, for each round $t$, random variables $I_t\in[d]$ (coordinate draw), $S_t\in\mathbb R$ (uniform draw), $U_t\in\mathbb R$ (branch coin), $V_t\in\mathbb R^d$ (the gradient response at the query point) and $x_t\in\mathbb R^d$ (the state).
--
--   **Formalization Note** Rounds are indexed from $0$. The relations between these processes are imposed separately (the run predicate and the oracle conditions).
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Algorithm 1, p.20

import Mathlib

namespace GeomDRSub

/-- **The random processes of a run of Algorithm 1.** Aggarwal–Lu, arXiv:2610.00545, Algorithm 1,
p.20: on round `t` the learner draws `I_t, S_t` (and the branch of `Y_t`) as in (49), receives the
gradient response `V_t(Y_t)`, and keeps the state `x_t`.

A run on a sample space `Ω` consists of the coordinate draws `I t`, the uniform draws `S t`, the
branch coins `U t`, the oracle responses `V t` and the states `x t`, one random variable each per
round `t`.

**Formalization Note.** Rounds are indexed from `0` (round `t + 1` of the paper is index `t`).
The constraints tying these processes together (fresh uniform draws, the projection update,
`x₁ = 0`) are `IsAlg1Run`; the oracle conditions (6)/(7) are separate predicates. -/
structure Alg1Run (d : ℕ) (Ω : Type*) where
  /-- coordinate draw `I_t` -/
  I : ℕ → Ω → Fin d
  /-- uniform draw `S_t ∈ [0,1]` -/
  S : ℕ → Ω → ℝ
  /-- branch coin `U_t ∈ [0,1]` -/
  U : ℕ → Ω → ℝ
  /-- gradient response `V_t(Y_t)` -/
  V : ℕ → Ω → EuclideanSpace ℝ (Fin d)
  /-- state `x_t` -/
  x : ℕ → Ω → EuclideanSpace ℝ (Fin d)

end GeomDRSub


