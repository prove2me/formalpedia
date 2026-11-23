-- Prove2me | Definitions.Def_VolunteerEngage_Thresholds_Supplement_Admissible
-- name    : VolunteerEngage_Thresholds_Supplement_Admissible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T04:09:56.28308+00:00
-- url     : https://prove2.me/theorems/93f4f3d7-1002-4e0f-ae34-aee119875d79
-- title:
--   Stationary Markov and admissible policies (pp. 20, 22–23)
-- statement:
--   A stationary Markov policy is a Borel function $\theta:[0,\infty)\to A$, evaluated at the current workload. It is admissible when, for some threshold $\bar z$, its tail lies below the largest negative breakpoint:
--
--   $$\theta(z)\le\bar\theta=\max\{\theta_l:0\le l\le L,\ \theta_l<0\},\qquad z\ge0,\quad z\ge\bar z.$$
--
--   The set of negative breakpoints is nonempty because $\theta_0<0$. This is the full comparison class in Theorem 2; no monotonicity, continuity or threshold form is imposed on competitors.
--
--   **Formalization Note** Measurability is required only on the nonnegative half-line. The finite maximum condition is encoded equivalently as existence of one negative breakpoint that bounds the entire tail. Choosing the largest one recovers exactly the source condition. No behavior at negative arguments is constrained.
-- source:
--   Ata, Tongarlak, Lee, Field, A Dynamic Model for Managing Volunteer Engagement, arXiv:2312.02920v2, p. 20, restriction to stationary Markov policies; pp. 22–23, Definition (Admissible Policies)

import Mathlib
import Definitions.Def_VolunteerEngage_Thresholds_Setting

namespace VolunteerEngage.Thresholds.Supplement

/-- Stationary Markov policies of §4: Borel functions from the nonnegative
workload to A. Values at negative arguments are unconstrained and unused. -/
def IsPolicy (M : Model) (θ : ℝ → ℝ) : Prop :=
  Measurable (fun z : Set.Ici (0 : ℝ) => θ z) ∧
  ∀ z : ℝ, 0 ≤ z → θ z ∈ Set.Icc M.θ0 (M.θ M.L)

/-- Definition (Admissible Policies), p. 23. The tail is bounded by one
negative breakpoint, equivalently by the largest negative breakpoint θ̄. -/
def IsAdmissible (M : Model) (θ : ℝ → ℝ) : Prop :=
  IsPolicy M θ ∧ ∃ zbar : ℝ, ∃ l : ℕ, l ≤ M.L ∧ M.θ l < 0 ∧
    ∀ z : ℝ, 0 ≤ z → zbar ≤ z → θ z ≤ M.θ l

end VolunteerEngage.Thresholds.Supplement


