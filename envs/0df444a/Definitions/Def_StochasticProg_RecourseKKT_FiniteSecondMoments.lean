-- Prove2me | Definitions.Def_StochasticProg_RecourseKKT_FiniteSecondMoments
-- name    : StochasticProg_RecourseKKT_FiniteSecondMoments
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:47:34.700053+00:00
-- url     : https://prove2.me/theorems/d3b3d485-8a86-437c-87ee-555eb7e593c5
-- title:
--   The random data $\xi$ has finite second moments
-- statement:
--   The random vector $\xi = (q, h, T)$ **has finite second moments** when every coordinate is square integrable:
--
--   $$
--   \mathrm E\, q_j^2 < \infty,\quad \mathrm E\, h_i^2 < \infty,\quad \mathrm E\, T_{ij}^2 < \infty \qquad \text{for all } i, j .
--   $$
--
--   This is equivalent to $\mathrm E\,\|\xi\|^2 < \infty$ for any norm on the $N = n_2 + m_2 + m_2 n_1$ coordinates. It is the hypothesis of Theorem 6 and of Theorem 9 (via p. 115).
--
--   **Formalization Note** Each coordinate is required to be in $L^2(P)$ (`MemLp _ 2 P`).
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, doi:10.1007/978-1-4614-0237-4, Chapter 3, Theorem 6, printed p. 112 (PDF p. 137), and printed p. 115 (PDF p. 140)

import Mathlib
import Definitions.Def_StochasticProg_RecourseKKT_RecourseData
open MeasureTheory

namespace StochasticProg.RecourseKKT

/-- **"ξ has finite second moments."**
Birge & Louveaux, *Introduction to Stochastic Programming*, 2nd ed., Springer 2011,
doi:10.1007/978-1-4614-0237-4, Chapter 3, Theorem 6, printed p. 112 (PDF p. 137), and printed p. 115 (PDF p. 140):
"For a stochastic program with fixed recourse where ξ has finite second moments"; "supposing that
ξ has finite second moments, we know that 𝒬 is Lipschitzian."

Every coordinate of the random vector `ξ = (q, h, T)` is square integrable.

**Formalization Note.** `MemLp f 2 P` is `E f² < ∞` (with `f` a.e. strongly measurable). Asking it
of every coordinate is equivalent to `E ‖ξ‖² < ∞` for any norm on the `N = n2 + m2 + m2·n1`
coordinates. -/
def FiniteSecondMoments {Ω : Type*} [MeasurableSpace Ω] {n1 m1 n2 m2 : ℕ}
    (P : Measure Ω) (pb : RecourseData Ω n1 m1 n2 m2) : Prop :=
  (∀ j, MemLp (fun ω => pb.q ω j) 2 P) ∧ (∀ i, MemLp (fun ω => pb.h ω i) 2 P) ∧
    (∀ i j, MemLp (fun ω => pb.T ω i j) 2 P)

end StochasticProg.RecourseKKT


