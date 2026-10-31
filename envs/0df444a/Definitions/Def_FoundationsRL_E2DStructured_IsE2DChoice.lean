-- Prove2me | Definitions.Def_FoundationsRL_E2DStructured_IsE2DChoice
-- name    : FoundationsRL_E2DStructured_IsE2DChoice
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:25:23.693633+00:00
-- url     : https://prove2.me/theorems/0bf3da65-7021-45e6-b4f9-14599a24e35e
-- title:
--   The E2D decision rule
-- statement:
--   A distribution $p\in\Delta(\Pi)$ is an **E2D choice** for the class $\mathcal F$, the parameter $\gamma$ and the estimate $\hat f$ when it solves the minimax problem of the Estimation-to-Decisions algorithm,
--   $$p\in\arg\min_{p'\in\Delta(\Pi)}\ \sup_{f\in\mathcal F}\mathbb E_{\pi\sim p'}\big[f(\pi_f)-f(\pi)-\gamma\,(f(\pi)-\hat f(\pi))^2\big],$$
--   that is, when the inner value of the game at $p$ is at most $\mathrm{dec}_\gamma(\mathcal F,\hat f)$.
--
--   **Formalization Note** The E2D algorithm is represented by this one-round condition on its distribution.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §4.2, E2D algorithm, p. 64; (4.19), p. 66

import Mathlib
import Definitions.Def_FoundationsRL_E2DStructured_dec

open MeasureTheory
open scoped ENNReal

namespace FoundationsRL.E2DStructured

/-- `p` is a choice of the E2D algorithm against the estimate `f̂`: it solves the minimax problem
`arg min_{p∈Δ(Π)} max_{f∈F} E_{π∼p}[f(π_f) − f(π) − γ·(f(π) − f̂(π))²]`, that is, it certifies the
value `dec_γ(F, f̂)` (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §4.2, p. 64, the E2D algorithm; (4.19), p. 66).

**Formalization Note.** Stated as `decGame ≤ dec`. Since `dec` is the infimum of `decGame`, this says
that `p` attains the infimum. -/
def IsE2DChoice {D : Type*} [MeasurableSpace D] (γ : ℝ) (F : Set (D → ℝ)) (fhat : D → ℝ)
    (p : ProbabilityMeasure D) : Prop :=
  decGame γ F fhat p ≤ dec γ F fhat

end FoundationsRL.E2DStructured


