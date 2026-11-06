-- Prove2me | Definitions.Def_GeomDRSub_IsAlg1Run
-- name    : GeomDRSub_IsAlg1Run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:13:37.439793+00:00
-- url     : https://prove2.me/theorems/9d65b7ac-290f-4132-ad79-b42906033032
-- title:
--   A run of Algorithm 1 (OMBQ with one gradient query)
-- statement:
--   Algorithm 1 has input $K$, $\zeta\mathbf 1\in K$, a horizon $T$, a diameter bound $D$ and a moment bound $V_{\mathrm{gen}}$; it initializes $x_1=\mathbf 0$ and $\eta=D/\sqrt{TV_{\mathrm{gen}}}$, and on each round $t=1,\dots,T$:
--   1. commits $p_t=h_\zeta(x_t)$;
--   2. draws $I_t,S_t$ and the query point $Y_t$ as in (49);
--   3. queries the gradient response $V_t(Y_t)$ and sets $\hat g_t=d\,[V_t(Y_t)]_{I_t}e_{I_t}$;
--   4. sets $x_{t+1}=\Pi_K(x_t+\eta\hat g_t)$.
--
--   A family of processes is a **run of Algorithm 1 with step $\eta$ for $T$ rounds** under a probability measure $P$ if, for every round $t<T$, the draws $(I_t,S_t,U_t)$ and the response $V_t$ are random variables, the draws are independent of the history of earlier rounds and have the uniform law (uniform coordinate, uniform $S_t$, uniform coin $U_t$); the initial state is $\mathbf 0$; and, for every outcome, $x_{t+1}$ is the Euclidean projection of $x_t+\eta\hat g_t$ onto $K$.
--
--   **Formalization Note** Rounds are 0-based. The Euclidean projection is the published argmin predicate `OrabonaOL.OGD.IsEuclideanProj`. How the responses relate to the gradients (exact, or the stochastic conditions (6)–(7)) is stated separately.
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Algorithm 1, p.20; Eq. (49), p.17

import Mathlib
import Definitions.Def_OrabonaOL_OGD_IsEuclideanProj
import Definitions.Def_GeomDRSub_gHat
import Definitions.Def_GeomDRSub_drawLaw
import Definitions.Def_GeomDRSub_Alg1Run
import Definitions.Def_GeomDRSub_Alg1Run_draws
import Definitions.Def_GeomDRSub_Alg1Run_hist

namespace GeomDRSub

open MeasureTheory ProbabilityTheory

/-- **A run of Algorithm 1 for `T` rounds.** Aggarwal–Lu, arXiv:2610.00545, Algorithm 1, p.20:
"Initialize: `x₁ = 0` and `η = D/√(TV_gen)`. For `t = 1, …, T`: 1. Commit `p_t = h_ζ(x_t)` for
reward. 2. Form the coordinate order and draw `I_t, S_t, Y_t` as in (49). 3. Query `V_t(Y_t)` and
set `ĝ_t = d[V_t(Y_t)]_{I_t} e_{I_t}`. 4. Set `x_{t+1} = Π_K(x_t + ηĝ_t)`."

`IsAlg1Run P K η T R` says, for the probability measure `P` and the step `η`:
1. for every round `t < T`, the draws `(I_t, S_t, U_t)` and the response `V_t` are random
   variables, the draws are independent of the history of earlier rounds (`R.hist t`), and their
   law is `drawLaw d` (uniform coordinate, uniform `S`, uniform coin);
2. the initial state is `x₁ = 0`;
3. for every round `t < T` and every outcome, `x_{t+1}` is the Euclidean projection of
   `x_t + η ĝ_t` onto `K`, with `ĝ_t = gHat I_t V_t`.

The action of round `t` is `p_t = h_ζ(x_t)` (step 1); it is not a separate process.

**Formalization Note.** Rounds are 0-based. Only rounds `t < T` are constrained. The projection
`Π_K` is the published argmin predicate `OrabonaOL.OGD.IsEuclideanProj` (for nonempty closed
convex `K` it determines `x_{t+1}` uniquely). How the responses `V_t` relate to the gradients is
not part of this predicate: it is the oracle condition (exact gradients, `OracleUnbiased`,
`OracleMoment`, `OracleNoise`). -/
def IsAlg1Run {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (K : Set (EuclideanSpace ℝ (Fin d))) (η : ℝ) (T : ℕ) (R : Alg1Run d Ω) : Prop :=
  (∀ t < T, Measurable (R.draws t) ∧ Measurable (R.V t) ∧
      Indep (MeasurableSpace.comap (R.draws t) inferInstance) (R.hist t) P ∧
      P.map (R.draws t) = drawLaw d) ∧
    (∀ ω, R.x 0 ω = 0) ∧
    (∀ t < T, ∀ ω, OrabonaOL.OGD.IsEuclideanProj K
      (R.x t ω + η • gHat (R.I t ω) (R.V t ω)) (R.x (t + 1) ω))

end GeomDRSub


