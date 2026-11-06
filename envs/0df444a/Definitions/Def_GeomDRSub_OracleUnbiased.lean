-- Prove2me | Definitions.Def_GeomDRSub_OracleUnbiased
-- name    : GeomDRSub_OracleUnbiased
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:17:14.920242+00:00
-- url     : https://prove2.me/theorems/e56da65f-f9ea-4a07-a71f-affe6b6a6ff4
-- title:
--   Unbiased gradient responses: first condition of (6)
-- statement:
--   The responses of a run are **unbiased** for objectives $f_1,f_2,\dots$ if, for every round $t<T$, $V_t$ is integrable and
--   $$
--   \mathbb E[V_t\mid F_t]=\nabla f_t(Y_t)\quad\text{almost surely},
--   $$
--   where $F_t$ is the information of the round (history plus this round's draws).
--
--   **Formalization Note** The integrability clause is what the conditional expectation presupposes; in Lean an unintegrable function has conditional expectation $0$.
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Section 3.2, pp.8–9, Eq. (6)

import Mathlib
import Definitions.Def_GeomDRSub_gradQ
import Definitions.Def_GeomDRSub_Alg1Run
import Definitions.Def_GeomDRSub_Alg1Run_Y
import Definitions.Def_GeomDRSub_Alg1Run_info

namespace GeomDRSub

open MeasureTheory

/-- **Unbiased gradient responses, first condition of (6).** Aggarwal–Lu, arXiv:2610.00545,
Section 3.2, p.8–9: "A stochastic gradient response `V_t(y)` satisfies `E[V_t(y) | F] = ∇f_t(y)`
… where the information `F` includes the objective sequence, the current query point, and all
choices and responses preceding this answer."

`OracleUnbiased P f ζ T R` says that for every round `t < T` the response `V_t` is integrable and
its conditional expectation given `R.info t` is `∇f_t(Y_t)` almost surely.

**Formalization Note.** `F` is `R.info t` (history plus this round's draws), the smallest
σ-algebra the page allows, which gives the strongest reading. The integrability clause is what the
page's conditional expectation presupposes; without it Lean's conditional expectation is `0` and
the condition would say nothing. -/
def OracleUnbiased {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (ζ : ℝ) (T : ℕ) (R : Alg1Run d Ω) : Prop :=
  ∀ t < T, Integrable (R.V t) P ∧
    P[R.V t | R.info t] =ᵐ[P] fun ω => gradQ (f t) (R.Y ζ t ω)

end GeomDRSub


