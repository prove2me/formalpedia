-- Prove2me | Definitions.Def_GeomDRSub_OracleNoise
-- name    : GeomDRSub_OracleNoise
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:17:27.973032+00:00
-- url     : https://prove2.me/theorems/ecbcd7d1-a4e9-425e-9c12-e35cd0c35019
-- title:
--   Noise bound (7)
-- statement:
--   The responses of a run satisfy the **noise bound** $\sigma_g$ for objectives $f_1,f_2,\dots$ if, for every round $t<T$, $\|V_t-\nabla f_t(Y_t)\|_2^2$ is integrable and
--   $$
--   \mathbb E\big[\|V_t-\nabla f_t(Y_t)\|_2^2\mid F_t\big]\le\sigma_g^2\quad\text{almost surely},
--   $$
--   where $F_t$ is the information of the round (history plus this round's draws). Exact gradients correspond to $\sigma_g=0$.
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Section 3.2, p.9, Eq. (7)

import Mathlib
import Definitions.Def_GeomDRSub_gradQ
import Definitions.Def_GeomDRSub_Alg1Run
import Definitions.Def_GeomDRSub_Alg1Run_Y
import Definitions.Def_GeomDRSub_Alg1Run_info

namespace GeomDRSub

open MeasureTheory

/-- **Noise bound on gradient responses, Eq. (7).** Aggarwal–Lu, arXiv:2610.00545, Section 3.2,
p.9: "When a noise bound is needed separately, we assume `E[‖V_t(y) − ∇f_t(y)‖₂² | F] ≤ σ_g²`".

`OracleNoise P f ζ T σg R` says that for every round `t < T`, `‖V_t − ∇f_t(Y_t)‖²` is integrable
and its conditional expectation given `R.info t` is at most `σ_g²` almost surely.

**Formalization Note.** `F` is `R.info t` (strongest reading, see `Alg1Run.info`). The
integrability clause rules out the junk value `0` of Lean's conditional expectation. -/
def OracleNoise {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (ζ : ℝ) (T : ℕ) (σg : ℝ) (R : Alg1Run d Ω) : Prop :=
  ∀ t < T, Integrable (fun ω => ‖R.V t ω - gradQ (f t) (R.Y ζ t ω)‖ ^ 2) P ∧
    P[fun ω => ‖R.V t ω - gradQ (f t) (R.Y ζ t ω)‖ ^ 2 | R.info t] ≤ᵐ[P] fun _ => σg ^ 2

end GeomDRSub


