-- Prove2me | Definitions.Def_MemQueryFeas_unifBall
-- name    : MemQueryFeas_unifBall
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:36:30.734125+00:00
-- url     : https://prove2.me/theorems/559f2c32-60b5-4b2e-9e93-e2494422223d
-- title:
--   Uniform law $\mathrm{Unif}(B(F,\rho))$ on a Grassmannian ball
-- statement:
--   $\mathrm{Unif}(B(F,\rho))$ is the Haar law $\nu$ of $\mathrm{Gr}(k,d)$ conditioned on the ball $B(F,\rho)$:
--   $$
--   \mathrm{Unif}(B(F,\rho))(A)=\frac{\nu(A\cap B(F,\rho))}{\nu(B(F,\rho))}.
--   $$
--   For $\rho>0$ and $F\in\mathrm{Gr}(k,d)$ the ball has positive Haar measure.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Algorithm 1, p.8 (PDF p.9); Lemma 14, p.26

import Mathlib
import Definitions.Def_MemQueryFeas_grBall

open MeasureTheory

namespace MemQueryFeas

/-- **Uniform law on a Grassmannian ball `Unif(B(F, ρ))`.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Algorithm 1, p.8 (PDF p.9):
"Sample `F^(i) ∼ Unif(B(F^(i+1), δ^(i)))`"; Lemma 14, p.26.

`unifBall ν k F ρ` is the Haar law `ν` of `Gr(k,d)` conditioned on the ball `B(F, ρ)`
(`ProbabilityTheory.cond`).

**Formalization Note.** For `ρ > 0` and `F ∈ Gr(k,d)` the ball has positive Haar measure and this is a
probability measure; the Haar law is passed as the argument `ν` (see `IsHaarGr`). -/
noncomputable def unifBall {d : ℕ} (ν : Measure (Op d)) (k : ℕ) (F : Op d) (ρ : ℝ) :
    Measure (Op d) :=
  ProbabilityTheory.cond ν (grBall k F ρ)

end MemQueryFeas


