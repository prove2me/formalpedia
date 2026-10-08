-- Prove2me | Definitions.Def_FastRatesSVM_GeomNoise_Envelope
-- name    : FastRatesSVM_GeomNoise_Envelope
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:52:30.388027+00:00
-- url     : https://prove2.me/theorems/30ae0e5e-26b3-4d4f-bd6d-926d53518844
-- title:
--   Definition 2.5 — envelope of order $\gamma$: $|2\eta(x)-1| \le c_\gamma \tau_x^\gamma$ for $P_X$-a.a. $x$
-- statement:
--   Let $X \subset \mathbb R^d$, let $P$ be a distribution on $X \times \{-1, 1\}$ with marginal $P_X$, regression function $\eta$ and distance to the decision boundary $\tau_x$ (equation (7)), and let $\gamma > 0$. The distribution $P$ has an **envelope of order $\gamma$** if there is a constant $c_\gamma > 0$ such that for $P_X$-almost all $x \in X$
--
--   $$|2\eta(x) - 1| \le c_\gamma\, \tau_x^{\gamma}.$$
--
--   Geometrically, the graph of $2\eta - 1$ lies between $-c_\gamma\tau_x^\gamma$ and $c_\gamma\tau_x^\gamma$: $\eta$ may be irregular away from the decision boundary but tends to $\tfrac12$ at rate $\tau_x^\gamma$ as $x$ approaches it.
--
--   **Formalization Note** "For $P_X$-almost all $x \in X$" is `∀ᵐ x ∂μ, x ∈ X → …`. The power $\tau_x^\gamma$ is the real power of the nonnegative number $\tau_x$. The requirement $\gamma > 0$ is part of the definition, as on the page.
-- source:
--   Steinwart, Scovel, Fast Rates for Support Vector Machines Using Gaussian Kernels, arXiv:0708.1838v1, p. 8, Definition 2.5, equation (10)

import Mathlib
import Definitions.Def_FastRatesSVM_GeomNoise_Tau

open MeasureTheory

namespace FastRatesSVM.GeomNoise

/-- **Envelope of order `γ`**, Definition 2.5, p. 8 (Steinwart–Scovel, arXiv:0708.1838v1):
`γ > 0` and there is `c_γ > 0` such that `|2η(x) − 1| ≤ c_γ τ_x^γ` for `P_X`-almost all
`x ∈ X` (equation (10)). -/
def HasEnvelope {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d)))
    (μ : Measure (EuclideanSpace ℝ (Fin d))) (η : EuclideanSpace ℝ (Fin d) → ℝ) (γ : ℝ) :
    Prop :=
  0 < γ ∧ ∃ cγ : ℝ, 0 < cγ ∧ ∀ᵐ x ∂μ, x ∈ X → |2 * η x - 1| ≤ cγ * tau X η x ^ γ

end FastRatesSVM.GeomNoise


