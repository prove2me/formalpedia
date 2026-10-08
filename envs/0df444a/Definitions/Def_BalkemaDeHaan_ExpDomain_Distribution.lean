-- Prove2me | Definitions.Def_BalkemaDeHaan_ExpDomain_Distribution
-- name    : BalkemaDeHaan_ExpDomain_Distribution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:05:43.899256+00:00
-- url     : https://prove2.me/theorems/ff09fc57-15a5-4f90-b295-89e01cc4ccb8
-- title:
--   (1) — survival and residual-life distributions; weak convergence
-- statement:
--   Let $X$ have a probability law $\mu$ on the real line. Its **survival function** is $R(x)=\Pr(X>x)$. For a threshold $t$ with $R(t)>0$, the **residual-life distribution function** is
--
--   $$F_t(x)=\Pr(X-t\le x\mid X>t)=\frac{\Pr(t<X\le t+x)}{R(t)}.$$
--
--   Weak convergence of a family of distribution functions means convergence at every continuity point of the limit distribution function. This module supplies the real-indexed and sequence-indexed versions used by the attraction domains.
--
--   **Formalization Note** The residual distribution is represented by a total real quotient. Every theorem using it assumes $R(t)>0$ through $D_r$, so the quotient is never used at a zero denominator.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), p. 792 (PDF 1), (1); p. 794 (PDF 3), weak convergence

import Mathlib
import Definitions.Def_BalkemaDeHaan_LimitTypes_ResidualLife

namespace BalkemaDeHaan.ExpDomain

open Filter MeasureTheory ProbabilityTheory

/-- Weak convergence of real distribution functions, evaluated at each continuity point. -/
def WeakConvergenceReal (H : ℝ → ℝ → ℝ) (G : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, ContinuousAt G x → Tendsto (fun t : ℝ => H t x) atTop (nhds (G x))

/-- Weak convergence of sequential distribution functions. -/
def WeakConvergenceNat (H : ℕ → ℝ → ℝ) (G : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, ContinuousAt G x → Tendsto (fun n : ℕ => H n x) atTop (nhds (G x))

end BalkemaDeHaan.ExpDomain


