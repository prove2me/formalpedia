-- Prove2me | Definitions.Def_GeomDRSub_OracleMoment
-- name    : GeomDRSub_OracleMoment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:14:33.320447+00:00
-- url     : https://prove2.me/theorems/7cfc2951-baeb-4bc8-9c73-31b9b90c6d17
-- title:
--   Second-moment bound: second condition of (6)
-- statement:
--   The responses of a run satisfy the **second-moment bound** $B_1$ if, for every round $t<T$, $\|V_t\|_2^2$ is integrable and
--   $$
--   \mathbb E[\|V_t\|_2^2\mid F_t]\le B_1^2\quad\text{almost surely},
--   $$
--   where $F_t$ is the information of the round (history plus this round's draws).
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Section 3.2, p.8, Eq. (6)

import Mathlib
import Definitions.Def_GeomDRSub_Alg1Run
import Definitions.Def_GeomDRSub_Alg1Run_info

namespace GeomDRSub

open MeasureTheory

/-- **Second-moment bound on gradient responses, second condition of (6).** Aggarwal–Lu,
arXiv:2610.00545, Section 3.2, p.8: `E[‖V_t(y)‖₂² | F] ≤ B₁²`.

`OracleMoment P T B₁ R` says that for every round `t < T`, `‖V_t‖²` is integrable and its
conditional expectation given `R.info t` is at most `B₁²` almost surely.

**Formalization Note.** `F` is `R.info t` (strongest reading, see `Alg1Run.info`). The
integrability clause rules out the junk value `0` of Lean's conditional expectation. -/
def OracleMoment {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (T : ℕ) (B₁ : ℝ)
    (R : Alg1Run d Ω) : Prop :=
  ∀ t < T, Integrable (fun ω => ‖R.V t ω‖ ^ 2) P ∧
    P[fun ω => ‖R.V t ω‖ ^ 2 | R.info t] ≤ᵐ[P] fun _ => B₁ ^ 2

end GeomDRSub


